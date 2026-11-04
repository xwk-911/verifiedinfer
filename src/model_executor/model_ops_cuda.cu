#include "model_internal.h"

#include <cuda_runtime.h>
#include <cublas_v2.h>
#include <math.h>
#include <new>

struct cuda_context { cudaStream_t stream = nullptr; cublasHandle_t blas = nullptr; };
static vi_status launch_status() { return cudaGetLastError() == cudaSuccess ? VI_OK : VI_MODEL_ERROR; }
static vi_status create(void **out)
{
    cuda_context *c = new (std::nothrow) cuda_context;
    if (!c) return VI_MODEL_ERROR;
    if (cudaStreamCreateWithFlags(&c->stream, cudaStreamNonBlocking) != cudaSuccess ||
        cublasCreate(&c->blas) != CUBLAS_STATUS_SUCCESS ||
        cublasSetStream(c->blas, c->stream) != CUBLAS_STATUS_SUCCESS ||
        cublasSetMathMode(c->blas, CUBLAS_PEDANTIC_MATH) != CUBLAS_STATUS_SUCCESS ||
        cublasSetAtomicsMode(c->blas, CUBLAS_ATOMICS_NOT_ALLOWED) != CUBLAS_STATUS_SUCCESS) {
        if (c->blas) cublasDestroy(c->blas);
        if (c->stream) cudaStreamDestroy(c->stream);
        delete c;
        return VI_MODEL_ERROR;
    }
    *out = c;
    return VI_OK;
}
static void destroy(void *context)
{
    auto *c = static_cast<cuda_context *>(context);
    if (!c) return;
    cudaStreamSynchronize(c->stream);
    cublasDestroy(c->blas);
    cudaStreamDestroy(c->stream);
    delete c;
}
static float *allocate(void *, size_t count)
{
    float *p = nullptr;
    if (count > SIZE_MAX / sizeof(float) || cudaMalloc(&p, count * sizeof(float)) != cudaSuccess) return nullptr;
    return p;
}
static void release(float *data) { if (data) cudaFree(data); }
static vi_status transfer(void *context, float *dst, const float *src, size_t n,
                           cudaMemcpyKind kind, bool wait)
{
    auto *c = static_cast<cuda_context *>(context);
    if (cudaMemcpyAsync(dst, src, n * sizeof(float), kind, c->stream) != cudaSuccess) return VI_MODEL_ERROR;
    if (wait && cudaStreamSynchronize(c->stream) != cudaSuccess) return VI_MODEL_ERROR;
    return VI_OK;
}
static vi_status write(void *c, float *d, const float *s, size_t n) { return transfer(c,d,s,n,cudaMemcpyHostToDevice,true); }
static vi_status read(void *c, float *d, const float *s, size_t n) { return transfer(c,d,s,n,cudaMemcpyDeviceToHost,true); }
static vi_status copy(void *c, float *d, const float *s, size_t n) { return transfer(c,d,s,n,cudaMemcpyDeviceToDevice,false); }

__global__ static void add_kernel(float *x, const float *y, size_t n)
{
    size_t i = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (i < n) x[i] += y[i];
}
static vi_status add(void *context, float *x, const float *y, size_t n)
{
    auto *c = static_cast<cuda_context *>(context);
    add_kernel<<<(unsigned)((n + 255) / 256),256,0,c->stream>>>(x,y,n);
    return launch_status();
}
static vi_status linear(void *context, const float *w, const float *bias,
                         const float *x, float *out, size_t rows, size_t cols)
{
    auto *c = static_cast<cuda_context *>(context);
    const float alpha = 1, beta = 0;
    /* Row-major [rows,cols] is column-major [cols,rows], hence transpose.
     * One fixed GEMV shape per projection for both prefill and decode. */
    if (cublasSgemv(c->blas, CUBLAS_OP_T, (int)cols, (int)rows, &alpha,
                    w, (int)cols, x, 1, &beta, out, 1) != CUBLAS_STATUS_SUCCESS) return VI_MODEL_ERROR;
    return bias ? add(context, out, bias, rows) : VI_OK;
}
__global__ static void norm_kernel(const float *x, const float *w, float *out, size_t n, float epsilon)
{
    if (threadIdx.x != 0) return;
    float sum = 0;
    for (size_t i = 0; i < n; ++i) sum += x[i] * x[i];
    if (!isfinite(sum)) {
        for (size_t i = 0; i < n; ++i) out[i] = NAN;
        return; /* Propagate failure to the synchronous finite-logits check. */
    }
    float scale = 1.0f / sqrtf(sum / (float)n + epsilon);
    for (size_t i = 0; i < n; ++i) out[i] = (x[i] * scale) * w[i];
}
static vi_status norm(void *context, const float *x, const float *w, float *out, size_t n, float epsilon)
{
    auto *c = static_cast<cuda_context *>(context);
    norm_kernel<<<1,1,0,c->stream>>>(x,w,out,n,epsilon);
    return launch_status();
}
__global__ static void rope_kernel(float *x, size_t heads, size_t dim, size_t pos, float theta)
{
    size_t pair = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (pair >= heads * (dim / 2)) return;
    size_t h = pair / (dim / 2), i = pair % (dim / 2);
    float angle = (float)pos * (1.0f / powf(theta, (float)(2 * i) / (float)dim));
    float c = cosf(angle), s = sinf(angle);
    size_t a = h * dim + i, b = a + dim / 2;
    float left = x[a], right = x[b];
    x[a] = left * c - right * s;
    x[b] = right * c + left * s;
}
static vi_status rope(void *context, float *x, size_t heads, size_t dim, size_t pos, float theta)
{
    auto *c = static_cast<cuda_context *>(context);
    rope_kernel<<<(unsigned)((heads * (dim / 2) + 255) / 256),256,0,c->stream>>>(x,heads,dim,pos,theta);
    return launch_status();
}
__global__ static void attention_kernel(const float *q, const float *keys, const float *values,
                                        float *out, float *scores, size_t heads, size_t kv_heads,
                                        size_t dim, size_t length, size_t capacity)
{
    size_t h = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (h >= heads) return;
    size_t kh = h / (heads / kv_heads), kv_width = kv_heads * dim;
    float *row = scores + h * capacity;
    float maximum = -INFINITY, total = 0, scale = 1.0f / sqrtf((float)dim);
    for (size_t t = 0; t < length; ++t) {
        float dot = 0;
        for (size_t j = 0; j < dim; ++j) dot += q[h * dim + j] * keys[t * kv_width + kh * dim + j];
        row[t] = dot * scale;
        if (row[t] > maximum) maximum = row[t];
    }
    for (size_t t = 0; t < length; ++t) { row[t] = expf(row[t] - maximum); total += row[t]; }
    for (size_t j = 0; j < dim; ++j) {
        float sum = 0;
        for (size_t t = 0; t < length; ++t) sum += (row[t] / total) * values[t * kv_width + kh * dim + j];
        out[h * dim + j] = sum;
    }
}
static vi_status attention(void *context, const float *q, const float *k, const float *v,
                            float *out, float *scores, size_t heads, size_t kv_heads,
                            size_t dim, size_t length, size_t capacity)
{
    auto *c = static_cast<cuda_context *>(context);
    attention_kernel<<<(unsigned)((heads + 31) / 32),32,0,c->stream>>>(q,k,v,out,scores,heads,kv_heads,dim,length,capacity);
    return launch_status();
}
__global__ static void swiglu_kernel(float *gate, const float *up, size_t n)
{
    size_t i = (size_t)blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= n) return;
    float e = expf(gate[i] >= 0 ? -gate[i] : gate[i]);
    float sigmoid = gate[i] >= 0 ? 1.0f / (1.0f + e) : e / (1.0f + e);
    gate[i] = (gate[i] * sigmoid) * up[i];
}
static vi_status swiglu(void *context, float *gate, const float *up, size_t n)
{
    auto *c = static_cast<cuda_context *>(context);
    swiglu_kernel<<<(unsigned)((n + 255) / 256),256,0,c->stream>>>(gate,up,n);
    return launch_status();
}
extern "C" const vi_model_ops *vi_cuda_model_ops(void)
{
    static const vi_model_ops ops = {create,destroy,allocate,release,write,read,copy,linear,norm,rope,attention,add,swiglu};
    return &ops;
}
