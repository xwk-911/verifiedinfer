#include "model_internal.h"
#include "models/llama_decoder.h"
#include <string.h>

/* Repository aliases belong to the CLI. Register only implemented semantics. */
static const vi_model_implementation implementations[] = {
    {"LlamaForCausalLM", "llama", VI_ARCH_LLAMA, &vi_llama_executor},
    {"Qwen2ForCausalLM", "qwen2", VI_ARCH_QWEN2, &vi_llama_executor}
};

const vi_model_implementation *vi_model_registry_find(const char *architecture,
                                                     const char *model_type)
{
    for (size_t i = 0; i < sizeof(implementations) / sizeof(implementations[0]); ++i) {
        const vi_model_implementation *implementation = &implementations[i];
        if (strcmp(architecture, implementation->architecture) == 0 &&
            strcmp(model_type, implementation->model_type) == 0) return implementation;
    }
    return NULL;
}
