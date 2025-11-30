/* Simple C Unit Test Framework for Spin */
#ifndef TEST_FRAMEWORK_H
#define TEST_FRAMEWORK_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Test counters */
static int tests_run = 0;
static int tests_passed = 0;
static int tests_failed = 0;

/* Colors for output */
#define RED "\033[0;31m"
#define GREEN "\033[0;32m"
#define YELLOW "\033[1;33m"
#define NC "\033[0m"

/* Test result macros */
#define TEST_PASS() do { \
    tests_passed++; \
    printf(GREEN "  PASS" NC ": %s\n", __func__); \
} while(0)

#define TEST_FAIL(msg) do { \
    tests_failed++; \
    printf(RED "  FAIL" NC ": %s - %s\n", __func__, msg); \
} while(0)

/* Assertion macros */
#define ASSERT_TRUE(cond) do { \
    tests_run++; \
    if (cond) { TEST_PASS(); } \
    else { TEST_FAIL("expected true, got false"); return; } \
} while(0)

#define ASSERT_FALSE(cond) do { \
    tests_run++; \
    if (!(cond)) { TEST_PASS(); } \
    else { TEST_FAIL("expected false, got true"); return; } \
} while(0)

#define ASSERT_EQ(expected, actual) do { \
    tests_run++; \
    if ((expected) == (actual)) { TEST_PASS(); } \
    else { \
        char msg[256]; \
        snprintf(msg, sizeof(msg), "expected %d, got %d", (int)(expected), (int)(actual)); \
        TEST_FAIL(msg); return; \
    } \
} while(0)

#define ASSERT_STR_EQ(expected, actual) do { \
    tests_run++; \
    if (strcmp((expected), (actual)) == 0) { TEST_PASS(); } \
    else { \
        char msg[512]; \
        snprintf(msg, sizeof(msg), "expected '%s', got '%s'", (expected), (actual)); \
        TEST_FAIL(msg); return; \
    } \
} while(0)

#define ASSERT_NOT_NULL(ptr) do { \
    tests_run++; \
    if ((ptr) != NULL) { TEST_PASS(); } \
    else { TEST_FAIL("expected non-NULL, got NULL"); return; } \
} while(0)

#define ASSERT_NULL(ptr) do { \
    tests_run++; \
    if ((ptr) == NULL) { TEST_PASS(); } \
    else { TEST_FAIL("expected NULL, got non-NULL"); return; } \
} while(0)

/* Test suite macros */
#define TEST_SUITE_BEGIN(name) \
    printf("\n=== Test Suite: %s ===\n", name)

#define TEST_SUITE_END() do { \
    printf("\n--- Results ---\n"); \
    printf("Tests run: %d\n", tests_run); \
    printf(GREEN "Passed: %d" NC "\n", tests_passed); \
    if (tests_failed > 0) printf(RED "Failed: %d" NC "\n", tests_failed); \
    else printf("Failed: %d\n", tests_failed); \
} while(0)

#define RUN_TEST(test_func) do { \
    printf("Running: %s\n", #test_func); \
    test_func(); \
} while(0)

/* Return exit code based on results */
#define TEST_EXIT_CODE() (tests_failed > 0 ? 1 : 0)

#endif /* TEST_FRAMEWORK_H */
