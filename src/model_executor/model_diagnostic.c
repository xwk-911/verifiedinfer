#include "model_internal.h"

/* These helpers implement the three diagnostic forms used by the loader.
 * Callers supply valid input strings disjoint from the output, as required by
 * the previous snprintf implementation. A zero size or NULL output is a no-op. */
static size_t diagnostic_text(char *output, size_t capacity, size_t used,
                              const char *text)
{
    while (used < capacity - 1 && *text != '\0') {
        output[used] = *text;
        used += 1;
        text += 1;
    }
    return used;
}

static size_t diagnostic_size(char *output, size_t capacity, size_t used,
                              size_t value)
{
    char digits[20];
    size_t count = 0;
    do {
        digits[count] = (char)('0' + value % 10);
        count += 1;
        value /= 10;
    } while (value != 0);
    while (count != 0 && used < capacity - 1) {
        count -= 1;
        output[used] = digits[count];
        used += 1;
    }
    return used;
}

int vi_model_problem(vi_diagnostic diagnostic, const char *text)
{
    if (diagnostic.text != NULL && diagnostic.size != 0) {
        size_t used = diagnostic_text(diagnostic.text, diagnostic.size, 0, text);
        diagnostic.text[used] = '\0';
    }
    return 0;
}

int vi_model_problem_string(vi_diagnostic diagnostic, const char *prefix,
                           const char *value)
{
    if (diagnostic.text != NULL && diagnostic.size != 0) {
        size_t used = diagnostic_text(diagnostic.text, diagnostic.size, 0, prefix);
        used = diagnostic_text(diagnostic.text, diagnostic.size, used, value);
        diagnostic.text[used] = '\0';
    }
    return 0;
}

int vi_model_problem_shape(vi_diagnostic diagnostic, const char *name,
                          size_t rows, size_t cols, size_t actual_rows,
                          size_t actual_cols)
{
    if (diagnostic.text != NULL && diagnostic.size != 0) {
        size_t used = diagnostic_text(diagnostic.text, diagnostic.size, 0,
                                      "wrong shape for ");
        used = diagnostic_text(diagnostic.text, diagnostic.size, used, name);
        used = diagnostic_text(diagnostic.text, diagnostic.size, used, ": expected [");
        used = diagnostic_size(diagnostic.text, diagnostic.size, used, rows);
        used = diagnostic_text(diagnostic.text, diagnostic.size, used, ",");
        used = diagnostic_size(diagnostic.text, diagnostic.size, used, cols);
        used = diagnostic_text(diagnostic.text, diagnostic.size, used, "], got [");
        used = diagnostic_size(diagnostic.text, diagnostic.size, used, actual_rows);
        used = diagnostic_text(diagnostic.text, diagnostic.size, used, ",");
        used = diagnostic_size(diagnostic.text, diagnostic.size, used, actual_cols);
        used = diagnostic_text(diagnostic.text, diagnostic.size, used, "]");
        diagnostic.text[used] = '\0';
    }
    return 0;
}

/* Same bounded output as "model.layers.%zu.%s" in the weight binder. */
void vi_model_layer_name(char *output, size_t layer, const char *suffix)
{
    size_t used = diagnostic_text(output, 192, 0, "model.layers.");
    used = diagnostic_size(output, 192, used, layer);
    used = diagnostic_text(output, 192, used, ".");
    used = diagnostic_text(output, 192, used, suffix);
    output[used] = '\0';
}
