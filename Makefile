.DEFAULT_GOAL := all
CC ?= cc
AR ?= ar
CPPFLAGS ?=
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror
# Preserve the scalar arithmetic plan used by exact regression comparisons.
FPFLAGS = -ffp-contract=off
LDLIBS += -lm
PYTHON ?= .venv/bin/python
CUDA ?= 0
ifeq ($(CUDA),1)
BUILD_DIR ?= build/cuda
CUDA_HOME ?= $(if $(wildcard $(CURDIR)/build/cuda-toolkit/bin/nvcc),$(CURDIR)/build/cuda-toolkit,/usr/local/cuda)
NVCC ?= $(CUDA_HOME)/bin/nvcc
CUDA_HOST_CXX ?= $(if $(wildcard $(CUDA_HOME)/bin/x86_64-conda-linux-gnu-g++),$(CUDA_HOME)/bin/x86_64-conda-linux-gnu-g++,g++)
CUDA_ARCH ?= sm_80
NVCCFLAGS ?= -std=c++17 -O2 --fmad=false -arch=$(CUDA_ARCH)
CPPFLAGS += -DVI_ENABLE_CUDA
CUDA_OBJECT = $(BUILD_DIR)/src/model_executor/ops/cuda.o
LDLIBS += -L$(CUDA_HOME)/lib -L$(CUDA_HOME)/targets/x86_64-linux/lib -lcublas -lcudart -lstdc++
LDLIBS += -Wl,-rpath,$(CUDA_HOME)/lib -Wl,-rpath,$(CUDA_HOME)/targets/x86_64-linux/lib
else
BUILD_DIR ?= build
endif

CORE_SOURCES = src/memory/token_buffer.c src/engine/request.c \
               src/engine/engine.c src/model_executor/sampler.c
MODEL_SOURCES = src/model_executor/model.c src/model_executor/model_registry.c \
                src/model_executor/model_loader.c src/model_executor/model_runner.c \
                src/model_executor/models/llama_decoder.c src/model_executor/ops/cpu.c
UNIT_SOURCES = tests/unit/memory/test_token_buffer.c \
               tests/unit/engine/test_request.c tests/unit/model_executor/test_sampler.c
INTEGRATION_SOURCES = tests/integration/test_engine.c tests/integration/test_tiny_transformer.c
LIB_OBJECTS = $(CORE_SOURCES:%.c=$(BUILD_DIR)/%.o) $(MODEL_SOURCES:%.c=$(BUILD_DIR)/%.o) $(CUDA_OBJECT)
UNIT_OBJECTS = $(UNIT_SOURCES:%.c=$(BUILD_DIR)/%.o)
INTEGRATION_OBJECTS = $(INTEGRATION_SOURCES:%.c=$(BUILD_DIR)/%.o)
SUPPORT_OBJECTS = $(BUILD_DIR)/tests/support/tiny_transformer.o
UNIT_TESTS = $(UNIT_SOURCES:%.c=$(BUILD_DIR)/%)
INTEGRATION_TESTS = $(INTEGRATION_SOURCES:%.c=$(BUILD_DIR)/%)
MODEL_RUNNER = $(BUILD_DIR)/vi-run
LIBRARY = $(BUILD_DIR)/libverifiedinfer.a
ALL_OBJECTS = $(LIB_OBJECTS) $(UNIT_OBJECTS) $(INTEGRATION_OBJECTS) $(SUPPORT_OBJECTS) \
              $(BUILD_DIR)/cli/vi_run.o $(BUILD_DIR)/tests/integration/test_model_runner.o

$(UNIT_OBJECTS) $(INTEGRATION_OBJECTS) $(SUPPORT_OBJECTS): CPPFLAGS += -Itests

.PHONY: all test unit-test integration-test model-test sanitize cuda-ptx clean compile-commands
all: $(LIBRARY) $(MODEL_RUNNER)

compile-commands:
	python3 tools/generate_compile_commands.py $(MAKE)

$(BUILD_DIR)/%.o: %.c
	mkdir -p $(dir $@)
	$(CC) -Iinclude $(CPPFLAGS) $(CFLAGS) $(FPFLAGS) -MMD -MP -c $< -o $@

$(LIBRARY): $(LIB_OBJECTS)
	$(RM) $@
	$(AR) rcs $@ $^

$(BUILD_DIR)/src/model_executor/ops/cuda.o: src/model_executor/ops/cuda.cu src/model_executor/model_internal.h include/verifiedinfer/model_executor/model.h
	mkdir -p $(dir $@)
	$(NVCC) -ccbin $(CUDA_HOST_CXX) -Iinclude $(CPPFLAGS) $(NVCCFLAGS) -MMD -MP -c $< -o $@

$(UNIT_TESTS): %: %.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

$(INTEGRATION_TESTS): %: %.o $(SUPPORT_OBJECTS) $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

$(MODEL_RUNNER): $(BUILD_DIR)/cli/vi_run.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

unit-test: $(UNIT_TESTS)
	@set -e; for binary in $(UNIT_TESTS); do $$binary; done

integration-test: $(INTEGRATION_TESTS)
	@set -e; for binary in $(INTEGRATION_TESTS); do $$binary; done

test: unit-test integration-test

model-test: $(MODEL_RUNNER) $(BUILD_DIR)/tests/integration/test_model_runner
	$(PYTHON) tests/integration/test_model_compat.py --build-dir $(BUILD_DIR) --device $(if $(filter 1,$(CUDA)),cuda,cpu)

$(BUILD_DIR)/tests/integration/test_model_runner.o: CPPFLAGS += -Itests
$(BUILD_DIR)/tests/integration/test_model_runner: $(BUILD_DIR)/tests/integration/test_model_runner.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

cuda-ptx:
	mkdir -p $(BUILD_DIR)/ptx
	$(NVCC) -ccbin $(CUDA_HOST_CXX) -Iinclude $(CPPFLAGS) $(NVCCFLAGS) -ptx src/model_executor/ops/cuda.cu -o $(BUILD_DIR)/ptx/model_ops_cuda.ptx

sanitize:
	$(MAKE) CUDA=0 BUILD_DIR=build/sanitize CFLAGS='-std=c11 -O1 -g -Wall -Wextra -Wpedantic -Werror -fsanitize=address,undefined -fno-omit-frame-pointer' test

# Preserve downloaded toolchains, checkpoints and matching driver libraries.
clean:
	rm -rf $(BUILD_DIR)/src $(BUILD_DIR)/cli $(BUILD_DIR)/tests $(BUILD_DIR)/ptx
	rm -f $(LIBRARY) $(MODEL_RUNNER)

-include $(ALL_OBJECTS:.o=.d)
