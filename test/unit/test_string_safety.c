/* Unit tests for string safety functions */
#include "test_framework.h"
#include <string.h>
#include <stdlib.h>

/* Test shell_escape function - declared in main.c */
extern char *shell_escape(const char *s);
extern void *emalloc(size_t);

/* Test basic string escaping */
void test_shell_escape_simple(void)
{
    char *result = shell_escape("hello");
    ASSERT_STR_EQ("'hello'", result);
}

/* Test escaping string with single quotes */
void test_shell_escape_with_quotes(void)
{
    char *result = shell_escape("it's");
    /* Single quote becomes: '\'' */
    ASSERT_STR_EQ("'it'\\''s'", result);
}

/* Test escaping empty string */
void test_shell_escape_empty(void)
{
    char *result = shell_escape("");
    ASSERT_STR_EQ("''", result);
}

/* Test escaping string with spaces */
void test_shell_escape_spaces(void)
{
    char *result = shell_escape("hello world");
    ASSERT_STR_EQ("'hello world'", result);
}

/* Test escaping string with special chars */
void test_shell_escape_special(void)
{
    char *result = shell_escape("$PATH;rm -rf");
    ASSERT_STR_EQ("'$PATH;rm -rf'", result);
}

/* Test escaping multiple quotes */
void test_shell_escape_multiple_quotes(void)
{
    char *result = shell_escape("'''");
    /* Each ' becomes '\'' */
    ASSERT_STR_EQ("''\\'''\\'''\\'''", result);
}

/* Test snprintf bounds checking behavior */
void test_snprintf_truncation(void)
{
    char buf[10];
    int ret = snprintf(buf, sizeof(buf), "hello world!");
    /* snprintf returns what would have been written */
    ASSERT_TRUE(ret >= (int)sizeof(buf));
    /* But buffer is safely truncated */
    ASSERT_EQ(9, (int)strlen(buf));
}

/* Test strncat bounds checking */
void test_strncat_bounds(void)
{
    char buf[20] = "hello";
    strncat(buf, " world! extra text", sizeof(buf) - strlen(buf) - 1);
    ASSERT_TRUE(strlen(buf) < sizeof(buf));
}

int main(void)
{
    TEST_SUITE_BEGIN("String Safety Functions");

    RUN_TEST(test_shell_escape_simple);
    RUN_TEST(test_shell_escape_with_quotes);
    RUN_TEST(test_shell_escape_empty);
    RUN_TEST(test_shell_escape_spaces);
    RUN_TEST(test_shell_escape_special);
    RUN_TEST(test_shell_escape_multiple_quotes);
    RUN_TEST(test_snprintf_truncation);
    RUN_TEST(test_strncat_bounds);

    TEST_SUITE_END();
    return TEST_EXIT_CODE();
}
