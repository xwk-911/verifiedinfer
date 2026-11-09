#define _POSIX_C_SOURCE 200809L
#include "../model_internal.h"

#include <cuda.h>
#include <cuda_runtime_api.h>
#include <cublas_v2.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

_Static_assert(sizeof(size_t) == 8 && sizeof(void *) == 8,
               "The PTX parameter ABI requires a 64-bit host");

enum kernel_id { K_ADD, K_NORM, K_ROPE, K_ATTENTION, K_SWIGLU, K_COUNT };
struct cuda_context {
    cudaStream_t stream;
    cublasHandle_t blas;
    CUmodule module;
    CUfunction kernels[K_COUNT];
    unsigned max_grid_x;
};

static void destroy(void *context)
{
    struct cuda_context *c = context;
    if (!c) return;
    if (c->stream) cudaStreamSynchronize(c->stream);
    if (c->blas) cublasDestroy(c->blas);
    if (c->module) cuModuleUnload(c->module);
    if (c->stream) cudaStreamDestroy(c->stream);
    free(c);
}

static bool load_module(CUmodule *module)
{
    const char *path = getenv("VI_PTX_PATH");
    char executable[PATH_MAX];
    if (!path) {
        /* Resolve beside the executable, independently of the working directory. */
        ssize_t length = readlink("/proc/self/exe", executable, sizeof(executable) - 1);
        if (length < 0) {
            perror("verifiedinfer: cannot locate executable for PTX loading");
            return false;
        }
        if ((size_t)length >= sizeof(executable) - 1) {
            fprintf(stderr, "verifiedinfer: executable path too long for PTX loading\n");
            return false;
        }
        executable[length] = '\0';
        char *name = strrchr(executable, '/');
        if (!name) return false;
        size_t offset = (size_t)(name + 1 - executable);
        int written = snprintf(executable + offset, sizeof(executable) - offset,
                               "ptx/model_ops_cuda.ptx");
        if (written < 0 || (size_t)written >= sizeof(executable) - offset) {
            fprintf(stderr, "verifiedinfer: PTX module path too long\n");
            return false;
        }
        path = executable;
    }
    CUresult status = cuModuleLoad(module, path);
    if (status != CUDA_SUCCESS) {
        const char *description = NULL;
        cuGetErrorString(status, &description);
        fprintf(stderr, "verifiedinfer: cannot load PTX module '%s': %s\n", path,
                description ? description : "unknown CUDA error");
        return false;
    }
    return true;
}

static vi_status create(void **out)
{
    static const char *const names[K_COUNT] = {
        "vi_add", "vi_norm", "vi_rope", "vi_attention", "vi_swiglu"
    };
    struct cuda_context *c = calloc(1, sizeof(*c));
    CUdevice device;
    int max_grid_x;
    if (!c) return VI_MODEL_ERROR;
    /* Runtime and Driver API calls share the current CUDA context and stream. */
    if (cuInit(0) != CUDA_SUCCESS ||
        cudaStreamCreateWithFlags(&c->stream, cudaStreamNonBlocking) != cudaSuccess ||
        cuCtxGetDevice(&device) != CUDA_SUCCESS ||
        cuDeviceGetAttribute(&max_grid_x, CU_DEVICE_ATTRIBUTE_MAX_GRID_DIM_X, device) != CUDA_SUCCESS ||
        max_grid_x < 1 ||
        cublasCreate(&c->blas) != CUBLAS_STATUS_SUCCESS ||
        cublasSetStream(c->blas, c->stream) != CUBLAS_STATUS_SUCCESS ||
        cublasSetMathMode(c->blas, CUBLAS_PEDANTIC_MATH) != CUBLAS_STATUS_SUCCESS ||
        cublasSetAtomicsMode(c->blas, CUBLAS_ATOMICS_NOT_ALLOWED) != CUBLAS_STATUS_SUCCESS) {
        destroy(c);
        return VI_MODEL_ERROR;
    }
    c->max_grid_x = (unsigned)max_grid_x;
    if (!load_module(&c->module)) {
        destroy(c);
        return VI_MODEL_ERROR;
    }
    for (unsigned i = 0; i < K_COUNT; ++i) {
        if (cuModuleGetFunction(&c->kernels[i], c->module, names[i]) != CUDA_SUCCESS) {
            fprintf(stderr, "verifiedinfer: PTX module is missing kernel '%s'\n", names[i]);
            destroy(c);
            return VI_MODEL_ERROR;
        }
    }
    *out = c;
    return VI_OK;
}

static float *allocate(void *context, size_t count)
{
    (void)context;
    float *p = NULL;
    if (count > SIZE_MAX / sizeof(float) ||
        cudaMalloc((void **)&p, count * sizeof(float)) != cudaSuccess) return NULL;
    return p;
}

static void release(float *data)
{
    if (data) cudaFree(data);
}

static vi_status transfer(void *context, float *dst, const float *src, size_t n,
                          enum cudaMemcpyKind kind, bool wait)
{
    struct cuda_context *c = context;
    if (n > SIZE_MAX / sizeof(float)) return VI_INVALID;
    if (n == 0) return VI_OK;
    if (cudaMemcpyAsync(dst, src, n * sizeof(float), kind, c->stream) != cudaSuccess)
        return VI_MODEL_ERROR;
    if (wait && cudaStreamSynchronize(c->stream) != cudaSuccess) return VI_MODEL_ERROR;
    return VI_OK;
}

static vi_status gpu_write(void *c, float *d, const float *s, size_t n)
{ return transfer(c, d, s, n, cudaMemcpyHostToDevice, true); }
static vi_status gpu_read(void *c, float *d, const float *s, size_t n)
{ return transfer(c, d, s, n, cudaMemcpyDeviceToHost, true); }
static vi_status copy(void *c, float *d, const float *s, size_t n)
{ return transfer(c, d, s, n, cudaMemcpyDeviceToDevice, false); }

static vi_status launch(struct cuda_context *c, enum kernel_id kernel,
                        size_t work, unsigned block, void **parameters)
{
    if (work == 0) return VI_OK;
    size_t grid = work / block + (work % block != 0);
    if (grid > c->max_grid_x) return VI_INVALID;
    return cuLaunchKernel(c->kernels[kernel], (unsigned)grid, 1, 1, block, 1, 1, 0,
                          (CUstream)c->stream, parameters, NULL) == CUDA_SUCCESS ?
           VI_OK : VI_MODEL_ERROR;
}

static vi_status add(void *context, float *x, const float *y, size_t n)
{
    if (n > SIZE_MAX / sizeof(float)) return VI_INVALID;
    void *parameters[] = {&x, &y, &n};
    return launch(context, K_ADD, n, 256, parameters);
}

static vi_status linear(void *context, const float *w, const float *bias,
                        const float *x, float *out, size_t rows, size_t cols)
{
    struct cuda_context *c = context;
    if (!rows || !cols || rows > INT_MAX || cols > INT_MAX) return VI_INVALID;
    const float alpha = 1, beta = 0;
    /* Keep the original fixed GEMV plan, precision and stream ordering. */
    if (cublasSgemv(c->blas, CUBLAS_OP_T, (int)cols, (int)rows, &alpha,
                    w, (int)cols, x, 1, &beta, out, 1) != CUBLAS_STATUS_SUCCESS)
        return VI_MODEL_ERROR;
    return bias ? add(c, out, bias, rows) : VI_OK;
}

static vi_status norm(void *context, const float *x, const float *w,
                      float *out, size_t n, float epsilon)
{
    if (!n || n > SIZE_MAX / sizeof(float)) return VI_INVALID;
    void *parameters[] = {&x, &w, &out, &n, &epsilon};
    return launch(context, K_NORM, 1, 1, parameters);
}

static vi_status rope(void *context, float *x, size_t heads, size_t dim,
                      size_t pos, float theta)
{
    if (!heads || !dim || dim % 2 || heads > SIZE_MAX / sizeof(float) / dim)
        return VI_INVALID;
    size_t pairs = heads * (dim / 2);
    void *parameters[] = {&x, &heads, &dim, &pos, &theta};
    return launch(context, K_ROPE, pairs, 256, parameters);
}

static vi_status attention(void *context, const float *q, const float *k, const float *v,
                           float *out, float *scores, size_t heads, size_t kv_heads,
                           size_t dim, size_t length, size_t capacity)
{
    if (!heads || !kv_heads || !dim || !length || length > capacity || heads % kv_heads ||
        heads > SIZE_MAX / sizeof(float) / dim ||
        kv_heads > SIZE_MAX / sizeof(float) / dim ||
        capacity > SIZE_MAX / sizeof(float) / (kv_heads * dim) ||
        heads > SIZE_MAX / sizeof(float) / capacity) return VI_INVALID;
    void *parameters[] = {&q, &k, &v, &out, &scores, &heads, &kv_heads, &dim, &length, &capacity};
    return launch(context, K_ATTENTION, heads, 32, parameters);
}

static vi_status swiglu(void *context, float *gate, const float *up, size_t n)
{
    if (n > SIZE_MAX / sizeof(float)) return VI_INVALID;
    void *parameters[] = {&gate, &up, &n};
    return launch(context, K_SWIGLU, n, 256, parameters);
}

const vi_model_ops *vi_cuda_model_ops(void)
{
    static const vi_model_ops ops = {
        create, destroy, allocate, release, gpu_write, gpu_read, copy, linear, norm, rope, attention, add, swiglu
    };
    return &ops;
}
