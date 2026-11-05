#ifndef VI_MODEL_JSON_H
#define VI_MODEL_JSON_H
#include "model_internal.h"
#ifndef JSMN_H
#define JSMN_HEADER
#include "../../third_party/jsmn/jsmn.h"
#undef JSMN_HEADER
#endif
struct vi_json { const char *text; jsmntok_t *tokens; int count; };
int vi_json_parse(vi_json *, const char *, size_t);
int vi_json_equal(const vi_json *, int, const char *);
int vi_json_next(const vi_json *, int);
int vi_json_member(const vi_json *, int, const char *);
int vi_json_string(const vi_json *, int, char *, size_t);
int vi_json_integer(const vi_json *, int, size_t *);
int vi_json_number(const vi_json *, int, float *);
int vi_json_boolean(const vi_json *, const char *, bool, bool *);
int vi_json_absent_or_null(const vi_json *, const char *);
#endif
