.DEFAULT_GOAL := all
CC ?= cc
AR ?= ar
CPPFLAGS ?=
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror
# Keep one explicit scalar arithmetic plan for exact reference comparisons.
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
CUDA_OBJECT = $(BUILD_DIR)/src/model_executor/model_ops_cuda.o
LDLIBS += -L$(CUDA_HOME)/lib -L$(CUDA_HOME)/targets/x86_64-linux/lib -lcublas -lcudart -lstdc++
LDLIBS += -Wl,-rpath,$(CUDA_HOME)/lib -Wl,-rpath,$(CUDA_HOME)/targets/x86_64-linux/lib
else
BUILD_DIR ?= build
endif

CORE_SOURCES = src/memory/token_buffer.c src/engine/request.c \
               src/engine/engine.c src/model_executor/sampler.c
MODEL_SOURCES = src/model_executor/models/mock_model.c \
                src/model_executor/models/dense_model.c \
                src/model_executor/models/causal_lm.c \
                src/model_executor/model_loader.c src/model_executor/model_ops_cpu.c
UNIT_SOURCES = tests/unit/memory/test_token_buffer.c \
               tests/unit/engine/test_request.c \
               tests/unit/model_executor/test_sampler.c
INTEGRATION_SOURCES = tests/integration/test_engine.c tests/integration/test_dense_model.c
EXAMPLE_SOURCES = examples/mock_engine.c examples/run_model.c

LIB_OBJECTS = $(CORE_SOURCES:%.c=$(BUILD_DIR)/%.o) $(MODEL_SOURCES:%.c=$(BUILD_DIR)/%.o) $(CUDA_OBJECT)
UNIT_OBJECTS = $(UNIT_SOURCES:%.c=$(BUILD_DIR)/%.o)
INTEGRATION_OBJECTS = $(INTEGRATION_SOURCES:%.c=$(BUILD_DIR)/%.o)
EXAMPLE_OBJECTS = $(EXAMPLE_SOURCES:%.c=$(BUILD_DIR)/%.o)
UNIT_TESTS = $(UNIT_SOURCES:%.c=$(BUILD_DIR)/%)
INTEGRATION_TESTS = $(INTEGRATION_SOURCES:%.c=$(BUILD_DIR)/%)
DEMOS = $(BUILD_DIR)/mock_engine
MODEL_RUNNER = $(BUILD_DIR)/vi-run
LIBRARY = $(BUILD_DIR)/libverifiedinfer.a
ALL_OBJECTS = $(LIB_OBJECTS) $(UNIT_OBJECTS) $(INTEGRATION_OBJECTS) $(EXAMPLE_OBJECTS) \
              $(BUILD_DIR)/tests/integration/test_model_runner.o

$(UNIT_OBJECTS) $(INTEGRATION_OBJECTS): CPPFLAGS += -Itests

.PHONY: all demo mock test unit-test integration-test model-test sanitize cuda-ptx clean compile-commands
all: $(LIBRARY) $(DEMOS) $(MODEL_RUNNER)

# Export the actual per-file flags without rebuilding or requiring Bear.
compile-commands:
	python3 tools/generate_compile_commands.py $(MAKE)

$(BUILD_DIR)/%.o: %.c
	mkdir -p $(dir $@)
	$(CC) -Iinclude $(CPPFLAGS) $(CFLAGS) $(FPFLAGS) -MMD -MP -c $< -o $@

$(LIBRARY): $(LIB_OBJECTS)
	$(AR) rcs $@ $^

$(BUILD_DIR)/src/model_executor/model_ops_cuda.o: src/model_executor/model_ops_cuda.cu src/model_executor/model_internal.h include/verifiedinfer/model_executor/model.h
	mkdir -p $(dir $@)
	$(NVCC) -ccbin $(CUDA_HOST_CXX) -Iinclude $(CPPFLAGS) $(NVCCFLAGS) -MMD -MP -c $< -o $@

$(UNIT_TESTS) $(INTEGRATION_TESTS): %: %.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $< $(LIBRARY) $(LDFLAGS) $(LDLIBS) -o $@

$(BUILD_DIR)/mock_engine: $(BUILD_DIR)/examples/mock_engine.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

$(MODEL_RUNNER): $(BUILD_DIR)/examples/run_model.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

demo:
ifeq ($(filter mock,$(MAKECMDGOALS)),)
	@echo "Usage: make demo mock"
	@exit 2
else
	@:
endif

mock: $(BUILD_DIR)/mock_engine
	./$(BUILD_DIR)/mock_engine

unit-test: $(UNIT_TESTS)
	@set -e; for binary in $(UNIT_TESTS); do ./$$binary; done

integration-test: $(INTEGRATION_TESTS)
	@set -e; for binary in $(INTEGRATION_TESTS); do ./$$binary; done

test: unit-test integration-test

model-test: $(MODEL_RUNNER) $(BUILD_DIR)/tests/integration/test_model_runner
	$(PYTHON) tests/integration/test_model_compat.py --build-dir $(BUILD_DIR) --device $(if $(filter 1,$(CUDA)),cuda,cpu)

$(BUILD_DIR)/tests/integration/test_model_runner.o: CPPFLAGS += -Itests
$(BUILD_DIR)/tests/integration/test_model_runner: $(BUILD_DIR)/tests/integration/test_model_runner.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

cuda-ptx:
	mkdir -p $(BUILD_DIR)/ptx
	$(NVCC) -ccbin $(CUDA_HOST_CXX) -Iinclude $(CPPFLAGS) $(NVCCFLAGS) -ptx src/model_executor/model_ops_cuda.cu -o $(BUILD_DIR)/ptx/model_ops_cuda.ptx

sanitize:
	$(MAKE) BUILD_DIR=build/sanitize CFLAGS='-std=c11 -O1 -g -Wall -Wextra -Wpedantic -Werror -fsanitize=address,undefined -fno-omit-frame-pointer' test

# Preserve downloaded toolchains and the active NVIDIA compatibility libraries.
clean:
	rm -rf $(BUILD_DIR)/src $(BUILD_DIR)/examples $(BUILD_DIR)/tests $(BUILD_DIR)/ptx
	rm -f $(LIBRARY) $(DEMOS) $(MODEL_RUNNER)

-include $(ALL_OBJECTS:.o=.d)
