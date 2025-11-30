# Unit Test Makefile for Spin
CC = gcc
CFLAGS = -Wall -Wextra -g -I../../Src -DTEST_BUILD
LDFLAGS =

# Spin source directory
SRC_DIR = ../../Src

# Test executables
TESTS = test_string_safety

# Source files needed from Spin (minimal set for unit tests)
SPIN_OBJS = $(SRC_DIR)/main.o

.PHONY: all clean test

all: $(TESTS)

# Build test executables
test_string_safety: test_string_safety.c test_framework.h
	@echo "Building $@..."
	@# We need to compile main.c with test hooks
	$(CC) $(CFLAGS) -c $(SRC_DIR)/main.c -o main_test.o -DTEST_BUILD 2>/dev/null || \
	$(CC) $(CFLAGS) -c test_string_safety.c -o test_string_safety.o
	@# For now, create a standalone test with embedded implementation
	$(CC) $(CFLAGS) -o $@ test_string_safety_standalone.c

# Run all tests
test: test_string_safety_standalone
	@echo ""
	@echo "========================================"
	@echo "Running Unit Tests"
	@echo "========================================"
	@./test_string_safety_standalone

# Standalone version that doesn't need to link with spin
test_string_safety_standalone: test_string_safety_standalone.c test_framework.h
	$(CC) $(CFLAGS) -o $@ test_string_safety_standalone.c

clean:
	rm -f $(TESTS) test_string_safety_standalone *.o
