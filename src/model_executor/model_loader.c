#define _POSIX_C_SOURCE 200809L
#define JSMN_STATIC
#define JSMN_STRICT
#include "../../third_party/jsmn/jsmn.h"
#include "model_internal.h"
#include "model_json.h"

#include <errno.h>
#include <fcntl.h>
#include <float.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

_Static_assert(sizeof(float) == sizeof(uint32_t) && FLT_RADIX == 2 &&
               FLT_MANT_DIG == 24 && FLT_MAX_EXP == 128, "checkpoint loader requires IEEE binary32");

int vi_json_parse(vi_json *j, const char *text, size_t length)
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
int vi_json_equal(const vi_json *j, int i, const char *s)
{
    return i >= 0 && i < j->count && (size_t)(j->tokens[i].end - j->tokens[i].start) == strlen(s) &&
        memcmp(j->text + j->tokens[i].start, s, strlen(s)) == 0;
}
int vi_json_next(const vi_json *j, int i)
{
    int end = j->tokens[i].end;
    for (++i; i < j->count && j->tokens[i].start < end; ++i) {}
    return i;
}
/* -1 missing, -2 duplicate. Never silently prefer one duplicate field. */
int vi_json_member(const vi_json *j, int object, const char *name)
{
    if (object < 0 || object >= j->count || j->tokens[object].type != JSMN_OBJECT) return -1;
    int found = -1;
    for (int i = object + 1; i < j->count && j->tokens[i].start < j->tokens[object].end;) {
        if (i + 1 >= j->count || j->tokens[i].type != JSMN_STRING) return -2;
        if (vi_json_equal(j, i, name)) {
            if (found != -1) return -2;
            found = i + 1;
        }
        i = vi_json_next(j, i + 1);
    }
    return found;
}
int vi_json_string(const vi_json *j, int i, char *out, size_t size)
{
    if (i < 0 || i >= j->count || j->tokens[i].type != JSMN_STRING) return 0;
    size_t n = (size_t)(j->tokens[i].end - j->tokens[i].start);
    if (n >= size) return 0;
    memcpy(out, j->text + j->tokens[i].start, n);
    out[n] = 0;
    return strchr(out, '\\') == NULL;
}
int vi_json_integer(const vi_json *j, int i, size_t *out)
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
int vi_json_number(const vi_json *j, int i, float *out)
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
int vi_json_boolean(const vi_json *j, const char *name, bool fallback, bool *out)
{
    int i = vi_json_member(j, 0, name);
    if (i == -1) { *out = fallback; return 1; }
    if (i < 0 || j->tokens[i].type != JSMN_PRIMITIVE) return 0;
    if (vi_json_equal(j, i, "true")) { *out = true; return 1; }
    if (vi_json_equal(j, i, "false")) { *out = false; return 1; }
    return 0;
}
int vi_json_absent_or_null(const vi_json *j, const char *name)
{
    int i = vi_json_member(j, 0, name);
    return i == -1 || (i >= 0 && vi_json_equal(j, i, "null"));
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

static int load_config(vi_model *m, const char *directory, vi_diagnostic e)
{
    char path[4096], *text = NULL, architecture[64], model_type[64];
    size_t length;
    vi_json j = {0};
    int ok = 0;
    if (!path_join(path, sizeof(path), directory, "config.json") ||
        !load_text(path, &text, &length) || !vi_json_parse(&j, text, length)) {
        vi_model_problem(e, "cannot read/parse config.json"); goto done;
    }
    int arch = vi_json_member(&j, 0, "architectures");
    if (arch < 0 || j.tokens[arch].type != JSMN_ARRAY || j.tokens[arch].size != 1 ||
        !vi_json_string(&j, arch + 1, architecture, sizeof(architecture)) ||
        !vi_json_string(&j, vi_json_member(&j, 0, "model_type"), model_type, sizeof(model_type))) {
        vi_model_problem(e, "config must declare one supported architecture/model_type"); goto done;
    }
    m->implementation = vi_model_registry_find(architecture, model_type);
    if (m->implementation == NULL) {
        vi_model_problem(e, "unsupported architecture/model_type: %s", architecture); goto done;
    }
    ok = m->implementation->executor->configure(m, &j, e);
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

static int load_shard(vi_model *model, const char *path, vi_diagnostic e)
{
    int fd = open(path, O_RDONLY), ok = 0;
    void *mapping = MAP_FAILED;
    size_t size = 0;
    vi_json j = {0};
    struct stat st;
    if (fd < 0 || fstat(fd, &st) != 0 || st.st_size < 8 || (uintmax_t)st.st_size > SIZE_MAX) {
        vi_model_problem(e, "cannot open safetensors shard: %s", path); goto done;
    }
    size = (size_t)st.st_size;
    mapping = mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (mapping == MAP_FAILED) { vi_model_problem(e, "cannot mmap %s", path); goto done; }
    const unsigned char *bytes = mapping;
    uint64_t header = 0;
    for (unsigned i = 0; i < 8; ++i) header |= (uint64_t)bytes[i] << (8 * i);
    if (header > size - 8 || !vi_json_parse(&j, (const char *)bytes + 8, (size_t)header)) {
        vi_model_problem(e, "invalid safetensors header: %s", path); goto done;
    }
    const unsigned char *data = bytes + 8 + (size_t)header;
    size_t data_size = size - 8 - (size_t)header;
    for (int i = 1; i < j.count && j.tokens[i].start < j.tokens[0].end;) {
        int object = i + 1;
        if (object >= j.count) { vi_model_problem(e, "malformed tensor directory"); goto done; }
        if (vi_json_equal(&j, i, "__metadata__")) { i = vi_json_next(&j, object); continue; }
        vi_loaded_tensor tensor = {0};
        if (!vi_json_string(&j, i, tensor.name, sizeof(tensor.name))) { vi_model_problem(e, "invalid tensor name"); goto done; }
        for (size_t k = 0; k < model->tensor_count; ++k)
            if (strcmp(model->tensors[k].name, tensor.name) == 0) {
                vi_model_problem(e, "duplicate tensor: %s", tensor.name); goto done;
            }
        int shape = vi_json_member(&j, object, "shape"), offsets = vi_json_member(&j, object, "data_offsets");
        int dtype = vi_json_member(&j, object, "dtype");
        size_t start, end;
        if (shape < 0 || offsets < 0 || j.tokens[shape].type != JSMN_ARRAY ||
            (j.tokens[shape].size != 1 && j.tokens[shape].size != 2) ||
            j.tokens[offsets].type != JSMN_ARRAY || j.tokens[offsets].size != 2 ||
            !vi_json_integer(&j, shape + 1, &tensor.rows) || tensor.rows == 0 ||
            !vi_json_integer(&j, offsets + 1, &start) || !vi_json_integer(&j, offsets + 2, &end)) {
            vi_model_problem(e, "invalid tensor shape/offsets: %s", tensor.name); goto done;
        }
        tensor.cols = 1;
        if (j.tokens[shape].size == 2 && !vi_json_integer(&j, shape + 2, &tensor.cols)) {
            vi_model_problem(e, "invalid tensor columns"); goto done;
        }
        if (tensor.cols == 0 || tensor.rows > SIZE_MAX / sizeof(float) / tensor.cols) {
            vi_model_problem(e, "overflowing tensor dimensions"); goto done;
        }
        size_t count = tensor.rows * tensor.cols;
        size_t element_size = vi_json_equal(&j, dtype, "F32") ? 4 :
            (vi_json_equal(&j, dtype, "BF16") || vi_json_equal(&j, dtype, "F16")) ? 2 : 0;
        if (element_size == 0 || start > end || end > data_size ||
            end - start != count * element_size || start % element_size != 0) {
            vi_model_problem(e, "invalid dtype/extent for %s", tensor.name); goto done;
        }
        tensor.data = malloc(count * sizeof(float));
        if (tensor.data == NULL) { vi_model_problem(e, "weight allocation failed"); goto done; }
        for (size_t k = 0; k < count; ++k) {
            const unsigned char *p = data + start + k * element_size;
            if (element_size == 4) {
                uint32_t bits = (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
                memcpy(&tensor.data[k], &bits, sizeof(bits));
            } else {
                uint16_t bits = (uint16_t)((unsigned)p[0] | (unsigned)p[1] << 8);
                if (vi_json_equal(&j, dtype, "BF16")) {
                    uint32_t full = (uint32_t)bits << 16;
                    memcpy(&tensor.data[k], &full, sizeof(full));
                } else tensor.data[k] = convert_half(bits);
            }
            if (!isfinite(tensor.data[k])) {
                free(tensor.data); vi_model_problem(e, "nonfinite weight in %s", tensor.name); goto done;
            }
        }
        if (model->tensor_count >= 65536) { free(tensor.data); vi_model_problem(e, "too many tensors"); goto done; }
        vi_loaded_tensor *grown = realloc(model->tensors, (model->tensor_count + 1) * sizeof(*grown));
        if (grown == NULL) { free(tensor.data); vi_model_problem(e, "tensor directory allocation failed"); goto done; }
        model->tensors = grown;
        model->tensors[model->tensor_count++] = tensor;
        i = vi_json_next(&j, object);
    }
    ok = 1;
done:
    free(j.tokens);
    if (mapping != MAP_FAILED) munmap(mapping, size);
    if (fd >= 0) close(fd);
    return ok;
}

static int load_weights(vi_model *m, const char *dir, vi_diagnostic e)
{
    char path[4096], *text = NULL;
    size_t length;
    vi_json j = {0};
    char (*shards)[256] = NULL;
    size_t count = 0;
    int ok = 0;
    if (!path_join(path, sizeof(path), dir, "model.safetensors.index.json")) return vi_model_problem(e, "model path too long");
    if (access(path, F_OK) != 0) {
        if (!path_join(path, sizeof(path), dir, "model.safetensors")) return vi_model_problem(e, "model path too long");
        return load_shard(m, path, e);
    }
    if (!load_text(path, &text, &length) || !vi_json_parse(&j, text, length)) {
        vi_model_problem(e, "invalid safetensors index"); goto done;
    }
    int map = vi_json_member(&j, 0, "weight_map");
    if (map < 0 || j.tokens[map].type != JSMN_OBJECT) { vi_model_problem(e, "missing weight_map"); goto done; }
    for (int i = map + 1; i < j.count && j.tokens[i].start < j.tokens[map].end;) {
        char name[256];
        if (i + 1 >= j.count || !vi_json_string(&j, i + 1, name, sizeof(name)) ||
            name[0] == 0 || strchr(name, '/') || strstr(name, "..")) {
            vi_model_problem(e, "invalid shard filename"); goto done;
        }
        bool exists = false;
        for (size_t k = 0; k < count; ++k) if (strcmp(shards[k], name) == 0) exists = true;
        if (!exists) {
            if (count >= 4096) { vi_model_problem(e, "too many shards"); goto done; }
            void *grown = realloc(shards, (count + 1) * sizeof(*shards));
            if (grown == NULL) { vi_model_problem(e, "shard list allocation failed"); goto done; }
            shards = grown;
            strcpy(shards[count++], name);
        }
        i = vi_json_next(&j, i + 1);
    }
    if (count == 0) { vi_model_problem(e, "empty weight map"); goto done; }
    for (size_t k = 0; k < count; ++k) {
        if (!path_join(path, sizeof(path), dir, shards[k]) || !load_shard(m, path, e)) goto done;
    }
    ok = 1;
done:
    free(shards); free(j.tokens); free(text); return ok;
}

int vi_model_checkpoint_load(vi_model *model, const char *directory, vi_diagnostic error)
{
    return load_config(model, directory, error) && load_weights(model, directory, error) &&
        model->implementation->executor->bind_weights(model, error);
}
