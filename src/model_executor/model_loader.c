#define _POSIX_C_SOURCE 200809L
#define JSMN_STATIC
#define JSMN_STRICT
#include "../../third_party/jsmn/jsmn.h"
#include "model_internal.h"

#include <errno.h>
#include <fcntl.h>
#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

_Static_assert(sizeof(float) == sizeof(uint32_t) && FLT_RADIX == 2 &&
               FLT_MANT_DIG == 24 && FLT_MAX_EXP == 128, "checkpoint loader requires IEEE binary32");

typedef struct { const char *text; jsmntok_t *tokens; int count; } json;
typedef struct { char *text; size_t size; } diagnostic;

static int problem(diagnostic e, const char *format, ...)
{
    if (e.text != NULL && e.size != 0) {
        va_list args;
        va_start(args, format);
        vsnprintf(e.text, e.size, format, args);
        va_end(args);
    }
    return 0;
}
static int parse_json(json *j, const char *text, size_t length)
{
    if (length == 0 || length > 64u * 1024u * 1024u || length > INT_MAX) return 0;
    size_t capacity = length / 2 + 16;
    if (capacity > 1024u * 1024u) capacity = 1024u * 1024u;
    j->text = text;
    j->tokens = calloc(capacity, sizeof(*j->tokens));
    if (j->tokens == NULL) return 0;
    jsmn_parser parser;
    jsmn_init(&parser);
    j->count = jsmn_parse(&parser, text, length, j->tokens, (unsigned)capacity);
    if (j->count <= 0 || j->tokens[0].type != JSMN_OBJECT) return 0;
    int end = j->tokens[0].end;
    for (size_t i = (size_t)end; i < length; ++i)
        if (text[i] != ' ' && text[i] != '\n' && text[i] != '\r' && text[i] != '\t') return 0;
    return 1;
}
static int equal(const json *j, int i, const char *s)
{
    return i >= 0 && i < j->count && (size_t)(j->tokens[i].end - j->tokens[i].start) == strlen(s) &&
        memcmp(j->text + j->tokens[i].start, s, strlen(s)) == 0;
}
static int next(const json *j, int i)
{
    int end = j->tokens[i].end;
    for (++i; i < j->count && j->tokens[i].start < end; ++i) {}
    return i;
}
/* -1 missing, -2 duplicate. Never silently prefer one duplicate field. */
static int member(const json *j, int object, const char *name)
{
    if (object < 0 || object >= j->count || j->tokens[object].type != JSMN_OBJECT) return -1;
    int found = -1;
    for (int i = object + 1; i < j->count && j->tokens[i].start < j->tokens[object].end;) {
        if (i + 1 >= j->count || j->tokens[i].type != JSMN_STRING) return -2;
        if (equal(j, i, name)) {
            if (found != -1) return -2;
            found = i + 1;
        }
        i = next(j, i + 1);
    }
    return found;
}
static int string(const json *j, int i, char *out, size_t size)
{
    if (i < 0 || i >= j->count || j->tokens[i].type != JSMN_STRING) return 0;
    size_t n = (size_t)(j->tokens[i].end - j->tokens[i].start);
    if (n >= size) return 0;
    memcpy(out, j->text + j->tokens[i].start, n);
    out[n] = 0;
    return strchr(out, '\\') == NULL;
}
static int integer(const json *j, int i, size_t *out)
{
    if (i < 0 || i >= j->count || j->tokens[i].type != JSMN_PRIMITIVE) return 0;
    size_t value = 0;
    for (int p = j->tokens[i].start; p < j->tokens[i].end; ++p) {
        unsigned digit = (unsigned)(j->text[p] - '0');
        if (digit > 9 || value > (SIZE_MAX - digit) / 10) return 0;
        value = value * 10 + digit;
    }
    *out = value;
    return j->tokens[i].end > j->tokens[i].start;
}
static int number(const json *j, int i, float *out)
{
    char buffer[96], *end;
    if (i < 0 || i >= j->count || j->tokens[i].type != JSMN_PRIMITIVE) return 0;
    size_t n = (size_t)(j->tokens[i].end - j->tokens[i].start);
    if (n == 0 || n >= sizeof(buffer)) return 0;
    memcpy(buffer, j->text + j->tokens[i].start, n);
    buffer[n] = 0;
    errno = 0;
    float v = strtof(buffer, &end);
    if (errno != 0 || *end != 0 || !isfinite(v)) return 0;
    *out = v;
    return 1;
}
static int boolean(const json *j, const char *name, bool fallback, bool *out)
{
    int i = member(j, 0, name);
    if (i == -1) { *out = fallback; return 1; }
    if (i < 0 || j->tokens[i].type != JSMN_PRIMITIVE) return 0;
    if (equal(j, i, "true")) { *out = true; return 1; }
    if (equal(j, i, "false")) { *out = false; return 1; }
    return 0;
}
static int absent_or_null(const json *j, const char *name)
{
    int i = member(j, 0, name);
    return i == -1 || (i >= 0 && equal(j, i, "null"));
}
static int load_text(const char *path, char **out, size_t *length)
{
    FILE *f = fopen(path, "rb");
    if (f == NULL) return 0;
    struct stat st;
    if (fstat(fileno(f), &st) != 0 || st.st_size <= 0 || st.st_size > 64 * 1024 * 1024) {
        fclose(f); return 0;
    }
    size_t n = (size_t)st.st_size;
    char *data = malloc(n + 1);
    if (data == NULL || fread(data, 1, n, f) != n) { free(data); fclose(f); return 0; }
    fclose(f);
    data[n] = 0;
    *out = data; *length = n;
    return 1;
}
static int path_join(char *out, size_t size, const char *dir, const char *name)
{
    int n = snprintf(out, size, "%s/%s", dir, name);
    return n >= 0 && (size_t)n < size;
}

/* Registry adapters normalize family differences; the executor never branches
 * on a repository/model name. Adding another architecture requires an explicit
 * adapter and feature validation, not an alias that ignores semantic changes. */
typedef struct { const char *architecture, *model_type; vi_model_architecture id; bool qkv_bias; } adapter;
static const adapter adapters[] = {
    {"LlamaForCausalLM", "llama", VI_ARCH_LLAMA, false},
    {"Qwen2ForCausalLM", "qwen2", VI_ARCH_QWEN2, true}
};

static int load_config(const char *directory, vi_model_config *c, diagnostic e)
{
    char path[4096], *text = NULL, architecture[64];
    size_t length;
    json j = {0};
    int ok = 0;
    if (!path_join(path, sizeof(path), directory, "config.json") ||
        !load_text(path, &text, &length) || !parse_json(&j, text, length)) {
        problem(e, "cannot read/parse config.json"); goto done;
    }
    int arch = member(&j, 0, "architectures");
    if (arch < 0 || j.tokens[arch].type != JSMN_ARRAY || j.tokens[arch].size != 1 ||
        !string(&j, arch + 1, architecture, sizeof(architecture))) {
        problem(e, "config must declare one supported architecture"); goto done;
    }
    const adapter *selected = NULL;
    for (size_t i = 0; i < sizeof(adapters) / sizeof(adapters[0]); ++i)
        if (strcmp(architecture, adapters[i].architecture) == 0) selected = &adapters[i];
    if (selected == NULL || !equal(&j, member(&j, 0, "model_type"), selected->model_type)) {
        problem(e, "unsupported architecture/model_type: %s", architecture); goto done;
    }
    c->architecture = selected->id;
#define SIZE_FIELD(name, field) do { if (!integer(&j, member(&j, 0, name), &c->field) || c->field == 0 || c->field > INT_MAX) { problem(e, "invalid config field %s", name); goto done; } } while (0)
    SIZE_FIELD("vocab_size", vocab_size);
    SIZE_FIELD("hidden_size", hidden_size);
    SIZE_FIELD("intermediate_size", intermediate_size);
    SIZE_FIELD("num_hidden_layers", num_layers);
    SIZE_FIELD("num_attention_heads", num_heads);
    SIZE_FIELD("max_position_embeddings", max_seq_len);
#undef SIZE_FIELD
    int kv = member(&j, 0, "num_key_value_heads"), hd = member(&j, 0, "head_dim");
    c->num_kv_heads = c->num_heads;
    if (kv != -1 && !integer(&j, kv, &c->num_kv_heads)) goto invalid;
    if (c->hidden_size % c->num_heads != 0) goto invalid;
    c->head_dim = c->hidden_size / c->num_heads;
    if (hd != -1 && !integer(&j, hd, &c->head_dim)) goto invalid;
    if (c->num_kv_heads == 0 || c->num_heads % c->num_kv_heads != 0 ||
        c->head_dim == 0 || c->head_dim % 2 != 0 ||
        c->head_dim > (size_t)INT_MAX / c->num_heads ||
        c->num_layers > SIZE_MAX / sizeof(vi_layer_weights) ||
        !vi_vocab_size_valid(c->vocab_size)) goto invalid;
    c->rms_norm_epsilon = 1e-6f;
    int eps = member(&j, 0, "rms_norm_eps"), theta = member(&j, 0, "rope_theta");
    if (eps != -1 && !number(&j, eps, &c->rms_norm_epsilon)) goto invalid;
    c->rope_theta = 10000;
    if (theta != -1 && !number(&j, theta, &c->rope_theta)) goto invalid;
    if (c->rms_norm_epsilon <= 0 || c->rope_theta <= 0) goto invalid;
    if (!boolean(&j, "attention_bias", selected->qkv_bias, &c->qkv_bias) ||
        !boolean(&j, "tie_word_embeddings", false, &c->tie_embeddings)) goto invalid;
    c->attention_output_bias = c->architecture == VI_ARCH_LLAMA && c->qkv_bias;
    if (c->architecture == VI_ARCH_QWEN2 && !c->qkv_bias) goto unsupported;
    bool flag;
    if (!boolean(&j, "mlp_bias", false, &flag) || flag ||
        !boolean(&j, "use_sliding_window", false, &flag) || flag ||
        !boolean(&j, "rope_interleaved", false, &flag) || flag ||
        !boolean(&j, "qk_norm", false, &flag) || flag ||
        !absent_or_null(&j, "rope_scaling") || !absent_or_null(&j, "rope_parameters") ||
        !absent_or_null(&j, "quantization_config")) goto unsupported;
    if (!equal(&j, member(&j, 0, "hidden_act"), "silu")) goto unsupported;
    int partial = member(&j, 0, "partial_rotary_factor");
    float fraction = 1;
    if (partial != -1 && (!number(&j, partial, &fraction) || fraction != 1)) goto unsupported;
    int layer_types = member(&j, 0, "layer_types");
    if (layer_types != -1 && !equal(&j, layer_types, "null")) {
        if (layer_types < 0 || j.tokens[layer_types].type != JSMN_ARRAY ||
            (size_t)j.tokens[layer_types].size != c->num_layers) goto unsupported;
        for (int i = layer_types + 1; i < next(&j, layer_types); ++i)
            if (!equal(&j, i, "full_attention")) goto unsupported;
    }
    if (c->architecture == VI_ARCH_LLAMA && !absent_or_null(&j, "sliding_window")) goto unsupported;
    ok = 1; goto done;
unsupported:
    problem(e, "unsupported model features (requires full attention, unscaled half-split RoPE, SwiGLU, no quantization/QK norm)"); goto done;
invalid:
    problem(e, "invalid attention geometry or model configuration");
done:
    free(j.tokens); free(text); return ok;
}

static float convert_half(uint16_t bits)
{
    unsigned sign = bits >> 15, exponent = (bits >> 10) & 31u, mantissa = bits & 1023u;
    float value = exponent == 0 ? ldexpf((float)mantissa, -24)
        : exponent == 31 ? (mantissa ? NAN : INFINITY)
        : ldexpf((float)(1024u + mantissa), (int)exponent - 25);
    return sign ? -value : value;
}

static int load_shard(vi_model *model, const char *path, diagnostic e)
{
    int fd = open(path, O_RDONLY), ok = 0;
    void *mapping = MAP_FAILED;
    size_t size = 0;
    json j = {0};
    struct stat st;
    if (fd < 0 || fstat(fd, &st) != 0 || st.st_size < 8 || (uintmax_t)st.st_size > SIZE_MAX) {
        problem(e, "cannot open safetensors shard: %s", path); goto done;
    }
    size = (size_t)st.st_size;
    mapping = mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (mapping == MAP_FAILED) { problem(e, "cannot mmap %s", path); goto done; }
    const unsigned char *bytes = mapping;
    uint64_t header = 0;
    for (unsigned i = 0; i < 8; ++i) header |= (uint64_t)bytes[i] << (8 * i);
    if (header > size - 8 || !parse_json(&j, (const char *)bytes + 8, (size_t)header)) {
        problem(e, "invalid safetensors header: %s", path); goto done;
    }
    const unsigned char *data = bytes + 8 + (size_t)header;
    size_t data_size = size - 8 - (size_t)header;
    for (int i = 1; i < j.count && j.tokens[i].start < j.tokens[0].end;) {
        int object = i + 1;
        if (object >= j.count) { problem(e, "malformed tensor directory"); goto done; }
        if (equal(&j, i, "__metadata__")) { i = next(&j, object); continue; }
        vi_loaded_tensor tensor = {0};
        if (!string(&j, i, tensor.name, sizeof(tensor.name))) { problem(e, "invalid tensor name"); goto done; }
        for (size_t k = 0; k < model->tensor_count; ++k)
            if (strcmp(model->tensors[k].name, tensor.name) == 0) {
                problem(e, "duplicate tensor: %s", tensor.name); goto done;
            }
        int shape = member(&j, object, "shape"), offsets = member(&j, object, "data_offsets");
        int dtype = member(&j, object, "dtype");
        size_t start, end;
        if (shape < 0 || offsets < 0 || j.tokens[shape].type != JSMN_ARRAY ||
            (j.tokens[shape].size != 1 && j.tokens[shape].size != 2) ||
            j.tokens[offsets].type != JSMN_ARRAY || j.tokens[offsets].size != 2 ||
            !integer(&j, shape + 1, &tensor.rows) || tensor.rows == 0 ||
            !integer(&j, offsets + 1, &start) || !integer(&j, offsets + 2, &end)) {
            problem(e, "invalid tensor shape/offsets: %s", tensor.name); goto done;
        }
        tensor.cols = 1;
        if (j.tokens[shape].size == 2 && !integer(&j, shape + 2, &tensor.cols)) {
            problem(e, "invalid tensor columns"); goto done;
        }
        if (tensor.cols == 0 || tensor.rows > SIZE_MAX / sizeof(float) / tensor.cols) {
            problem(e, "overflowing tensor dimensions"); goto done;
        }
        size_t count = tensor.rows * tensor.cols;
        size_t element_size = equal(&j, dtype, "F32") ? 4 :
            (equal(&j, dtype, "BF16") || equal(&j, dtype, "F16")) ? 2 : 0;
        if (element_size == 0 || start > end || end > data_size ||
            end - start != count * element_size || start % element_size != 0) {
            problem(e, "invalid dtype/extent for %s", tensor.name); goto done;
        }
        tensor.data = malloc(count * sizeof(float));
        if (tensor.data == NULL) { problem(e, "weight allocation failed"); goto done; }
        for (size_t k = 0; k < count; ++k) {
            const unsigned char *p = data + start + k * element_size;
            if (element_size == 4) {
                uint32_t bits = (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
                memcpy(&tensor.data[k], &bits, sizeof(bits));
            } else {
                uint16_t bits = (uint16_t)((unsigned)p[0] | (unsigned)p[1] << 8);
                if (equal(&j, dtype, "BF16")) {
                    uint32_t full = (uint32_t)bits << 16;
                    memcpy(&tensor.data[k], &full, sizeof(full));
                } else tensor.data[k] = convert_half(bits);
            }
            if (!isfinite(tensor.data[k])) {
                free(tensor.data); problem(e, "nonfinite weight in %s", tensor.name); goto done;
            }
        }
        if (model->tensor_count >= 65536) { free(tensor.data); problem(e, "too many tensors"); goto done; }
        vi_loaded_tensor *grown = realloc(model->tensors, (model->tensor_count + 1) * sizeof(*grown));
        if (grown == NULL) { free(tensor.data); problem(e, "tensor directory allocation failed"); goto done; }
        model->tensors = grown;
        model->tensors[model->tensor_count++] = tensor;
        i = next(&j, object);
    }
    ok = 1;
done:
    free(j.tokens);
    if (mapping != MAP_FAILED) munmap(mapping, size);
    if (fd >= 0) close(fd);
    return ok;
}

static int load_weights(vi_model *m, const char *dir, diagnostic e)
{
    char path[4096], *text = NULL;
    size_t length;
    json j = {0};
    char (*shards)[256] = NULL;
    size_t count = 0;
    int ok = 0;
    if (!path_join(path, sizeof(path), dir, "model.safetensors.index.json")) return problem(e, "model path too long");
    if (access(path, F_OK) != 0) {
        if (!path_join(path, sizeof(path), dir, "model.safetensors")) return problem(e, "model path too long");
        return load_shard(m, path, e);
    }
    if (!load_text(path, &text, &length) || !parse_json(&j, text, length)) {
        problem(e, "invalid safetensors index"); goto done;
    }
    int map = member(&j, 0, "weight_map");
    if (map < 0 || j.tokens[map].type != JSMN_OBJECT) { problem(e, "missing weight_map"); goto done; }
    for (int i = map + 1; i < j.count && j.tokens[i].start < j.tokens[map].end;) {
        char name[256];
        if (i + 1 >= j.count || !string(&j, i + 1, name, sizeof(name)) ||
            name[0] == 0 || strchr(name, '/') || strstr(name, "..")) {
            problem(e, "invalid shard filename"); goto done;
        }
        bool exists = false;
        for (size_t k = 0; k < count; ++k) if (strcmp(shards[k], name) == 0) exists = true;
        if (!exists) {
            if (count >= 4096) { problem(e, "too many shards"); goto done; }
            void *grown = realloc(shards, (count + 1) * sizeof(*shards));
            if (grown == NULL) { problem(e, "shard list allocation failed"); goto done; }
            shards = grown;
            strcpy(shards[count++], name);
        }
        i = next(&j, i + 1);
    }
    if (count == 0) { problem(e, "empty weight map"); goto done; }
    for (size_t k = 0; k < count; ++k) {
        if (!path_join(path, sizeof(path), dir, shards[k]) || !load_shard(m, path, e)) goto done;
    }
    ok = 1;
done:
    free(shards); free(j.tokens); free(text); return ok;
}

static const float *tensor(vi_model *m, const char *name, size_t rows, size_t cols, diagnostic e)
{
    for (size_t i = 0; i < m->tensor_count; ++i) {
        vi_loaded_tensor *t = &m->tensors[i];
        if (strcmp(t->name, name) != 0) continue;
        if (t->rows != rows || t->cols != cols) {
            problem(e, "wrong shape for %s: expected [%zu,%zu], got [%zu,%zu]", name, rows, cols, t->rows, t->cols);
            return NULL;
        }
        t->used = true;
        return t->data;
    }
    problem(e, "missing tensor: %s", name);
    return NULL;
}
static int bind_weights(vi_model *m, diagnostic e)
{
    const vi_model_config *c = &m->config;
    size_t d = c->hidden_size, f = c->intermediate_size;
    size_t q = c->num_heads * c->head_dim, kv = c->num_kv_heads * c->head_dim;
    m->layers = calloc(c->num_layers, sizeof(*m->layers));
    if (m->layers == NULL) return problem(e, "layer allocation failed");
    m->embedding = tensor(m, "model.embed_tokens.weight", c->vocab_size, d, e);
    m->output_norm = tensor(m, "model.norm.weight", d, 1, e);
    if (m->embedding == NULL || m->output_norm == NULL) return 0;
    m->lm_head = c->tie_embeddings ? m->embedding : tensor(m, "lm_head.weight", c->vocab_size, d, e);
    if (m->lm_head == NULL) return 0;
    if (c->tie_embeddings) {
        for (size_t i = 0; i < m->tensor_count; ++i) {
            vi_loaded_tensor *t = &m->tensors[i];
            if (strcmp(t->name, "lm_head.weight") == 0) {
                if (t->rows != c->vocab_size || t->cols != d ||
                    (m->device == VI_DEVICE_CPU &&
                     memcmp(t->data, m->embedding, c->vocab_size * d * sizeof(float)) != 0))
                    return problem(e, "tied LM head differs from embedding");
                t->used = true;
            }
        }
    }
    for (size_t i = 0; i < c->num_layers; ++i) {
        vi_layer_weights *w = &m->layers[i];
        char name[192];
#define BIND(field, suffix, rows, cols) do { snprintf(name, sizeof(name), "model.layers.%zu.%s", i, suffix); w->field = tensor(m, name, rows, cols, e); if (w->field == NULL) return 0; } while (0)
        BIND(input_norm, "input_layernorm.weight", d, 1);
        BIND(q, "self_attn.q_proj.weight", q, d);
        BIND(k, "self_attn.k_proj.weight", kv, d);
        BIND(v, "self_attn.v_proj.weight", kv, d);
        BIND(o, "self_attn.o_proj.weight", d, q);
        BIND(post_norm, "post_attention_layernorm.weight", d, 1);
        BIND(gate, "mlp.gate_proj.weight", f, d);
        BIND(up, "mlp.up_proj.weight", f, d);
        BIND(down, "mlp.down_proj.weight", d, f);
        if (c->qkv_bias) {
            BIND(q_bias, "self_attn.q_proj.bias", q, 1);
            BIND(k_bias, "self_attn.k_proj.bias", kv, 1);
            BIND(v_bias, "self_attn.v_proj.bias", kv, 1);
        }
        if (c->attention_output_bias) BIND(o_bias, "self_attn.o_proj.bias", d, 1);
#undef BIND
    }
    for (size_t i = 0; i < m->tensor_count; ++i)
        if (!m->tensors[i].used) return problem(e, "unrecognized/unused tensor: %s", m->tensors[i].name);
    return 1;
}

vi_status vi_model_load(const char *directory, vi_device device, vi_model **out,
                        char *error, size_t capacity)
{
    diagnostic e = {error, capacity};
    if (error && capacity) error[0] = 0;
    if (directory == NULL || out == NULL || (device != VI_DEVICE_CPU && device != VI_DEVICE_CUDA)) {
        problem(e, "invalid load arguments"); return VI_INVALID;
    }
    vi_model *m = calloc(1, sizeof(*m));
    if (m == NULL) { problem(e, "model allocation failed"); return VI_INVALID; }
    m->ops = vi_cpu_model_ops();
    if (!load_config(directory, &m->config, e) || !load_weights(m, directory, e) || !bind_weights(m, e)) goto fail;
    if (device == VI_DEVICE_CUDA) {
#ifdef VI_ENABLE_CUDA
        const vi_model_ops *cuda = vi_cuda_model_ops();
        void *context = NULL;
        if (cuda->create(&context) != VI_OK) { problem(e, "CUDA initialization failed"); goto fail; }
        /* Stage all uploads, then switch ownership so failure cleanup is exact. */
        float **uploaded = calloc(m->tensor_count, sizeof(*uploaded));
        bool success = uploaded != NULL;
        for (size_t i = 0; success && i < m->tensor_count; ++i) {
            size_t count = m->tensors[i].rows * m->tensors[i].cols;
            uploaded[i] = cuda->allocate(context, count);
            success = uploaded[i] != NULL && cuda->write(context, uploaded[i], m->tensors[i].data, count) == VI_OK;
        }
        cuda->destroy(context);
        if (!success) {
            if (uploaded) for (size_t i = 0; i < m->tensor_count; ++i) cuda->release(uploaded[i]);
            free(uploaded); problem(e, "CUDA weight upload failed"); goto fail;
        }
        free(m->layers); m->layers = NULL;
        for (size_t i = 0; i < m->tensor_count; ++i) {
            free(m->tensors[i].data); m->tensors[i].data = uploaded[i];
        }
        free(uploaded); m->ops = cuda; m->device = device;
        /* Metadata and tied-weight equality were validated before upload. */
        if (!bind_weights(m, e)) goto fail;
#else
        problem(e, "CUDA not built; use make CUDA=1 or select --device cpu"); goto fail;
#endif
    }
    *out = m;
    return VI_OK;
fail:
    vi_model_free(m);
    return VI_INVALID;
}

void vi_model_free(vi_model *model)
{
    if (model == NULL) return;
    for (size_t i = 0; i < model->tensor_count; ++i) model->ops->release(model->tensors[i].data);
    free(model->tensors); free(model->layers); free(model);
}
