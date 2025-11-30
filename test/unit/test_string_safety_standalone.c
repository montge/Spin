/* Standalone unit tests for string safety functions
 * This file includes implementations to test without linking to full spin binary
 */
#include "test_framework.h"
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

/* Mock emalloc - just use malloc for tests */
void *emalloc(size_t size)
{
    void *p = malloc(size);
    if (!p) {
        fprintf(stderr, "emalloc: out of memory\n");
        exit(1);
    }
    return p;
}

/* Copy of shell_escape from main.c for testing */
char *shell_escape(const char *s)
{
    size_t len = strlen(s);
    size_t i, j;
    char *escaped;
    size_t quote_count = 0;

    /* Count single quotes to determine buffer size */
    for (i = 0; i < len; i++) {
        if (s[i] == '\'') {
            quote_count++;
        }
    }

    /* Allocate: original + 2 outer quotes + 3 extra chars per inner quote + null */
    escaped = (char *) emalloc(len + 2 + (quote_count * 3) + 1);

    j = 0;
    escaped[j++] = '\'';
    for (i = 0; i < len; i++) {
        if (s[i] == '\'') {
            /* End quote, escaped quote, start quote: '\'' */
            escaped[j++] = '\'';
            escaped[j++] = '\\';
            escaped[j++] = '\'';
            escaped[j++] = '\'';
        } else {
            escaped[j++] = s[i];
        }
    }
    escaped[j++] = '\'';
    escaped[j] = '\0';

    return escaped;
}

/* Copy of safe_append from main.c for testing */
static size_t safe_append(char *buf, size_t bufsize, const char *fmt, ...)
{
    va_list ap;
    size_t cur_len = strlen(buf);
    size_t remaining = bufsize - cur_len;
    int ret;

    if (remaining <= 1)
        return 0;

    va_start(ap, fmt);
    ret = vsnprintf(buf + cur_len, remaining, fmt, ap);
    va_end(ap);

    if (ret < 0)
        return 0;
    return (size_t)ret < remaining ? (size_t)ret : remaining - 1;
}

/* ============ TESTS ============ */

/* Test basic string escaping */
void test_shell_escape_simple(void)
{
    char *result = shell_escape("hello");
    ASSERT_STR_EQ("'hello'", result);
    free(result);
}

/* Test escaping string with single quotes */
void test_shell_escape_with_quotes(void)
{
    char *result = shell_escape("it's");
    /* Single quote becomes: '\'' */
    ASSERT_STR_EQ("'it'\\''s'", result);
    free(result);
}

/* Test escaping empty string */
void test_shell_escape_empty(void)
{
    char *result = shell_escape("");
    ASSERT_STR_EQ("''", result);
    free(result);
}

/* Test escaping string with spaces */
void test_shell_escape_spaces(void)
{
    char *result = shell_escape("hello world");
    ASSERT_STR_EQ("'hello world'", result);
    free(result);
}

/* Test escaping string with special chars */
void test_shell_escape_special(void)
{
    char *result = shell_escape("$PATH;rm -rf");
    ASSERT_STR_EQ("'$PATH;rm -rf'", result);
    free(result);
}

/* Test escaping multiple quotes */
void test_shell_escape_multiple_quotes(void)
{
    char *result = shell_escape("'''");
    /* Each ' becomes '\'' */
    ASSERT_STR_EQ("''\\'''\\'''\\'''", result);
    free(result);
}

/* Test escaping path with backslashes (Windows-style) */
void test_shell_escape_backslash(void)
{
    char *result = shell_escape("C:\\Users\\test");
    ASSERT_STR_EQ("'C:\\Users\\test'", result);
    free(result);
}

/* Test escaping newlines */
void test_shell_escape_newline(void)
{
    char *result = shell_escape("line1\nline2");
    ASSERT_STR_EQ("'line1\nline2'", result);
    free(result);
}

/* Test safe_append basic functionality */
void test_safe_append_basic(void)
{
    char buf[50] = "";
    safe_append(buf, sizeof(buf), "hello");
    ASSERT_STR_EQ("hello", buf);
}

/* Test safe_append multiple calls */
void test_safe_append_multiple(void)
{
    char buf[50] = "";
    safe_append(buf, sizeof(buf), "hello");
    safe_append(buf, sizeof(buf), " ");
    safe_append(buf, sizeof(buf), "world");
    ASSERT_STR_EQ("hello world", buf);
}

/* Test safe_append with format string */
void test_safe_append_format(void)
{
    char buf[50] = "value: ";
    safe_append(buf, sizeof(buf), "%d", 42);
    ASSERT_STR_EQ("value: 42", buf);
}

/* Test safe_append truncation */
void test_safe_append_truncation(void)
{
    char buf[10] = "hi";
    safe_append(buf, sizeof(buf), " there buddy!");
    /* Should be truncated but safe */
    ASSERT_TRUE(strlen(buf) < sizeof(buf));
    ASSERT_EQ(9, (int)strlen(buf));
}

/* Test safe_append when buffer is full */
void test_safe_append_full_buffer(void)
{
    char buf[5] = "1234";  /* Already has 4 chars + null */
    size_t added = safe_append(buf, sizeof(buf), "extra");
    ASSERT_EQ(0, (int)added);  /* Nothing should be added */
    ASSERT_STR_EQ("1234", buf);  /* Original preserved */
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
    /* And null-terminated */
    ASSERT_EQ('\0', buf[9]);
}

/* Test strncat bounds checking */
void test_strncat_bounds(void)
{
    char buf[20] = "hello";
    strncat(buf, " world! extra text", sizeof(buf) - strlen(buf) - 1);
    ASSERT_TRUE(strlen(buf) < sizeof(buf));
    /* Should be truncated */
    ASSERT_EQ(19, (int)strlen(buf));
}

/* Test buffer overflow prevention */
void test_buffer_overflow_prevention(void)
{
    char small_buf[8];
    /* This should not overflow */
    snprintf(small_buf, sizeof(small_buf), "%s", "this is a very long string");
    ASSERT_EQ(7, (int)strlen(small_buf));
    ASSERT_STR_EQ("this is", small_buf);
}

int main(void)
{
    TEST_SUITE_BEGIN("String Safety Functions");

    printf("\n-- shell_escape tests --\n");
    RUN_TEST(test_shell_escape_simple);
    RUN_TEST(test_shell_escape_with_quotes);
    RUN_TEST(test_shell_escape_empty);
    RUN_TEST(test_shell_escape_spaces);
    RUN_TEST(test_shell_escape_special);
    RUN_TEST(test_shell_escape_multiple_quotes);
    RUN_TEST(test_shell_escape_backslash);
    RUN_TEST(test_shell_escape_newline);

    printf("\n-- safe_append tests --\n");
    RUN_TEST(test_safe_append_basic);
    RUN_TEST(test_safe_append_multiple);
    RUN_TEST(test_safe_append_format);
    RUN_TEST(test_safe_append_truncation);
    RUN_TEST(test_safe_append_full_buffer);

    printf("\n-- standard library safety tests --\n");
    RUN_TEST(test_snprintf_truncation);
    RUN_TEST(test_strncat_bounds);
    RUN_TEST(test_buffer_overflow_prevention);

    TEST_SUITE_END();
    return TEST_EXIT_CODE();
}
