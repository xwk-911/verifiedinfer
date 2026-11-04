.DEFAULT_GOAL := all
CC ?= cc
AR ?= ar
CPPFLAGS ?=
CFLAGS ?= -std=c11 -O2 -Wall -Wextra -Wpedantic -Werror
# Keep one explicit scalar arithmetic plan for exact reference comparisons.
FPFLAGS = -ffp-contract=off
LDLIBS += -lm
BUILD_DIR ?= build

CORE_SOURCES = src/memory/token_buffer.c src/engine/request.c \
               src/engine/engine.c src/model_executor/sampler.c
MODEL_SOURCES = src/model_executor/models/mock_model.c \
                src/model_executor/models/dense_model.c
UNIT_SOURCES = tests/unit/memory/test_token_buffer.c \
               tests/unit/engine/test_request.c \
               tests/unit/model_executor/test_sampler.c
INTEGRATION_SOURCES = tests/integration/test_engine.c tests/integration/test_dense_model.c
EXAMPLE_SOURCES = examples/mock_engine.c examples/dense_engine.c

LIB_OBJECTS = $(CORE_SOURCES:%.c=$(BUILD_DIR)/%.o) $(MODEL_SOURCES:%.c=$(BUILD_DIR)/%.o)
UNIT_OBJECTS = $(UNIT_SOURCES:%.c=$(BUILD_DIR)/%.o)
INTEGRATION_OBJECTS = $(INTEGRATION_SOURCES:%.c=$(BUILD_DIR)/%.o)
EXAMPLE_OBJECTS = $(EXAMPLE_SOURCES:%.c=$(BUILD_DIR)/%.o)
UNIT_TESTS = $(UNIT_SOURCES:%.c=$(BUILD_DIR)/%)
INTEGRATION_TESTS = $(INTEGRATION_SOURCES:%.c=$(BUILD_DIR)/%)
DEMOS = $(EXAMPLE_SOURCES:examples/%.c=$(BUILD_DIR)/%)
LIBRARY = $(BUILD_DIR)/libverifiedinfer.a
ALL_OBJECTS = $(LIB_OBJECTS) $(UNIT_OBJECTS) $(INTEGRATION_OBJECTS) $(EXAMPLE_OBJECTS)

$(UNIT_OBJECTS) $(INTEGRATION_OBJECTS): CPPFLAGS += -Itests
$(INTEGRATION_OBJECTS): CPPFLAGS += -Iexamples

.PHONY: all demo dense-demo test unit-test integration-test sanitize clean
all: $(LIBRARY) $(DEMOS)

$(BUILD_DIR)/%.o: %.c
	mkdir -p $(dir $@)
	$(CC) -Iinclude $(CPPFLAGS) $(CFLAGS) $(FPFLAGS) -MMD -MP -c $< -o $@

$(LIBRARY): $(LIB_OBJECTS)
	$(AR) rcs $@ $^

$(UNIT_TESTS) $(INTEGRATION_TESTS): %: %.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $< $(LIBRARY) $(LDFLAGS) $(LDLIBS) -o $@

$(BUILD_DIR)/mock_engine: $(BUILD_DIR)/examples/mock_engine.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

$(BUILD_DIR)/dense_engine: $(BUILD_DIR)/examples/dense_engine.o $(LIBRARY)
	$(CC) $(CFLAGS) $(FPFLAGS) $^ $(LDFLAGS) $(LDLIBS) -o $@

demo: $(BUILD_DIR)/mock_engine
	./$(BUILD_DIR)/mock_engine

dense-demo: $(BUILD_DIR)/dense_engine
	./$(BUILD_DIR)/dense_engine

unit-test: $(UNIT_TESTS)
	@set -e; for binary in $(UNIT_TESTS); do ./$$binary; done

integration-test: $(INTEGRATION_TESTS)
	@set -e; for binary in $(INTEGRATION_TESTS); do ./$$binary; done

test: unit-test integration-test

sanitize:
	$(MAKE) BUILD_DIR=build/sanitize CFLAGS='-std=c11 -O1 -g -Wall -Wextra -Wpedantic -Werror -fsanitize=address,undefined -fno-omit-frame-pointer' test

clean:
	rm -rf build

-include $(ALL_OBJECTS:.o=.d)
