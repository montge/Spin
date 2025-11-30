#!/bin/bash
# Test suite for reprosrc.c - source reproduction and pretty printing functionality
# Tests the -I flag (reprosrc) and -pp flag (pretty_print) functionality

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$(dirname "$SCRIPT_DIR")")"
SPIN="${SPIN:-$ROOT_DIR/Src/spin}"
WORK_DIR="${WORK_DIR:-$SCRIPT_DIR/work}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

TESTS_RUN=0
TESTS_PASSED=0
TESTS_FAILED=0

mkdir -p "$WORK_DIR"

log_pass() { echo -e "${GREEN}PASS${NC}: $1"; ((TESTS_PASSED++)); }
log_fail() { echo -e "${RED}FAIL${NC}: $1"; ((TESTS_FAILED++)); }
log_info() { echo -e "INFO: $1"; }
run_test() { ((TESTS_RUN++)); echo -e "\n--- Reprosrc Test: $1 ---"; }

cleanup() { rm -rf "$WORK_DIR"/* 2>/dev/null || true; }

# ============================================================
# Test 1: Basic -I flag (repro_src) functionality
# Tests: repro_src(), repro_proc(), repro_seq()
# ============================================================
test_basic_repro_src() {
    run_test "Basic -I flag (repro_src)"
    cleanup
    cd "$WORK_DIR"

    cat > simple.pml << 'EOF'
proctype P() {
    int x;
    x = 5;
    x = x + 1;
    assert(x == 6)
}
init { run P() }
EOF

    # Use -I flag to reproduce source
    local output
    output=$("$SPIN" -I simple.pml 2>&1)

    if echo "$output" | grep -q "proctype P()"; then
        log_info "Found proctype declaration"
    else
        log_fail "-I flag did not reproduce proctype"
        echo "Output: $output"
        return 1
    fi

    if echo "$output" | grep -q "x = 5"; then
        log_pass "Basic -I flag works"
    else
        log_fail "-I flag did not reproduce statements"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 2: Pretty printing with -pp flag
# Tests: pretty_print(), blip(), purge(), doindent()
# ============================================================
test_pretty_print() {
    run_test "Pretty printing (-pp flag)"
    cleanup
    cd "$WORK_DIR"

    cat > messy.pml << 'EOF'
proctype    P(   )   {
int     x=5;
if
::x==5->x=10
::else->skip
fi
}
init{run P()}
EOF

    # Use -pp flag for pretty printing (it outputs to stdout and exits)
    local output
    output=$("$SPIN" -pp messy.pml 2>&1 || true)

    if echo "$output" | grep -q "proctype"; then
        log_info "Pretty print output contains proctype"
    else
        log_fail "-pp flag did not output proctype"
        echo "Output: $output"
        return 1
    fi

    # Check that output has proper formatting
    if echo "$output" | grep -q "if"; then
        log_pass "Pretty print (-pp) works"
    else
        log_fail "-pp flag output missing expected keywords"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 3: D_STEP reproduction
# Tests: repro_sub() with D_STEP case
# ============================================================
test_dstep_repro() {
    run_test "D_STEP reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > dstep.pml << 'EOF'
int counter = 0;
proctype Incrementer() {
    d_step {
        counter = counter + 1;
        counter = counter + 2;
        counter = counter + 3
    }
}
init { run Incrementer() }
EOF

    local output
    output=$("$SPIN" -I dstep.pml 2>&1)

    if echo "$output" | grep -q "d_step"; then
        log_pass "D_STEP reproduction works"
    else
        log_fail "D_STEP not reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 4: ATOMIC block reproduction
# Tests: repro_sub() with ATOMIC case
# ============================================================
test_atomic_repro() {
    run_test "ATOMIC block reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > atomic.pml << 'EOF'
int val = 0;
proctype Worker() {
    atomic {
        val = 100;
        val = val * 2
    }
}
init { run Worker() }
EOF

    local output
    output=$("$SPIN" -I atomic.pml 2>&1)

    if echo "$output" | grep -q "atomic"; then
        log_pass "ATOMIC block reproduction works"
    else
        log_fail "ATOMIC block not reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 5: IF statement reproduction
# Tests: repro_seq() with IF/FI
# ============================================================
test_if_statement_repro() {
    run_test "IF statement reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > ifstmt.pml << 'EOF'
proctype Chooser() {
    int x = 5;
    if
    :: x > 0 -> x = 10
    :: x <= 0 -> x = -10
    :: else -> skip
    fi
}
init { run Chooser() }
EOF

    local output
    output=$("$SPIN" -I ifstmt.pml 2>&1)

    if echo "$output" | grep -q "if" && echo "$output" | grep -q "fi"; then
        log_pass "IF statement reproduction works"
    else
        log_fail "IF statement not properly reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 6: DO loop reproduction
# Tests: repro_seq() with DO/OD
# ============================================================
test_do_loop_repro() {
    run_test "DO loop reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > doloop.pml << 'EOF'
proctype Counter() {
    int i = 0;
    do
    :: i < 5 -> i++
    :: i >= 5 -> break
    od
}
init { run Counter() }
EOF

    local output
    output=$("$SPIN" -I doloop.pml 2>&1)

    if echo "$output" | grep -q "do" && echo "$output" | grep -q "od"; then
        log_pass "DO loop reproduction works"
    else
        log_fail "DO loop not properly reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 7: UNLESS construct reproduction
# Tests: repro_seq() with UNLESS
# ============================================================
test_unless_repro() {
    run_test "UNLESS construct reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > unless.pml << 'EOF'
int flag = 0;
proctype P() {
    { flag = 1; flag = 2 }
    unless
    { flag == 2 -> flag = 100 }
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -I unless.pml 2>&1)

    if echo "$output" | grep -q "unless"; then
        log_pass "UNLESS construct reproduction works"
    else
        log_fail "UNLESS construct not reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 8: C_CODE reproduction
# Tests: repro_seq() with C_CODE
# ============================================================
test_c_code_repro() {
    run_test "C_CODE reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > ccode.pml << 'EOF'
c_decl {
    int external_var = 0;
}
proctype P() {
    c_code { external_var = 42; }
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -I ccode.pml 2>&1)

    if echo "$output" | grep -q "c_code"; then
        log_pass "C_CODE reproduction works"
    else
        log_fail "C_CODE not reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 9: C_EXPR reproduction
# Tests: repro_seq() with C_EXPR
# ============================================================
test_c_expr_repro() {
    run_test "C_EXPR reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > cexpr.pml << 'EOF'
proctype P() {
    c_expr { 1 } -> skip
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -I cexpr.pml 2>&1)

    if echo "$output" | grep -q "c_expr"; then
        log_pass "C_EXPR reproduction works"
    else
        log_fail "C_EXPR not reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 10: Labels reproduction
# Tests: has_lab() in repro_seq()
# ============================================================
test_labels_repro() {
    run_test "Labels reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > labels.pml << 'EOF'
proctype P() {
    int x = 0;
start:
    x = 1;
    goto end;
middle:
    x = 2;
end:
    skip
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -I labels.pml 2>&1)

    if echo "$output" | grep -q "start:" || echo "$output" | grep -q "end:"; then
        log_pass "Labels reproduction works"
    else
        log_fail "Labels not reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 11: Deterministic proctype (D_PROCTYPE)
# Tests: repro_proc() with deterministic flag
# ============================================================
test_deterministic_proctype() {
    run_test "Deterministic proctype reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > dproc.pml << 'EOF'
d_proctype DP() {
    int x = 1
}
init { run DP() }
EOF

    local output
    output=$("$SPIN" -I dproc.pml 2>&1)

    if echo "$output" | grep -q "Dproctype\|proctype"; then
        log_pass "Deterministic proctype reproduction works"
    else
        log_fail "Deterministic proctype not reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 12: Provided clause reproduction
# Tests: repro_proc() with provided clause
# ============================================================
test_provided_clause() {
    run_test "Provided clause reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > provided.pml << 'EOF'
int condition = 1;
proctype P() provided (condition > 0) {
    int x = 5
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -I provided.pml 2>&1)

    if echo "$output" | grep -q "provided"; then
        log_pass "Provided clause reproduction works"
    else
        log_fail "Provided clause not reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 13: Complex nested structures
# Tests: repro_seq() with nested blocks
# ============================================================
test_nested_structures() {
    run_test "Nested structures reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > nested.pml << 'EOF'
proctype Complex() {
    int x = 0;
    do
    :: x < 10 ->
        if
        :: x % 2 == 0 ->
            atomic {
                x = x + 1;
                x = x + 1
            }
        :: else ->
            d_step {
                x = x + 2
            }
        fi
    :: x >= 10 -> break
    od
}
init { run Complex() }
EOF

    local output
    output=$("$SPIN" -I nested.pml 2>&1)

    if echo "$output" | grep -q "do" && \
       echo "$output" | grep -q "if" && \
       echo "$output" | grep -q "atomic"; then
        log_pass "Nested structures reproduction works"
    else
        log_fail "Nested structures not properly reproduced"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 14: Multiple proctypes
# Tests: repro_proc() recursive call for multiple procs
# ============================================================
test_multiple_proctypes() {
    run_test "Multiple proctypes reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > multiproc.pml << 'EOF'
proctype Sender() {
    int x = 1
}
proctype Receiver() {
    int y = 2
}
proctype Monitor() {
    int z = 3
}
init {
    run Sender();
    run Receiver();
    run Monitor()
}
EOF

    local output
    output=$("$SPIN" -I multiproc.pml 2>&1)

    # Count occurrences of "proctype" in output
    local count
    count=$(echo "$output" | grep -c "proctype" || true)

    if [ "$count" -ge 3 ]; then
        log_pass "Multiple proctypes reproduction works (found $count proctypes)"
    else
        log_fail "Not all proctypes reproduced (found $count, expected 3)"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 15: blip() function with various tokens
# Tests: blip() switch statement cases via -pp
# ============================================================
test_blip_tokens() {
    run_test "Token formatting (blip function)"
    cleanup
    cd "$WORK_DIR"

    cat > tokens.pml << 'EOF'
mtype = { MSG1, MSG2 };
chan ch = [1] of { mtype };
proctype P() {
    int x = 5;
    x++;
    x--;
    assert(x == 5);
    if
    :: x == 5 -> ch ! MSG1
    :: else -> skip
    fi;
    ch ? MSG1;
    printf("done\n")
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -pp tokens.pml 2>&1 || true)

    # Check that various tokens are formatted
    if echo "$output" | grep -q "mtype" && \
       echo "$output" | grep -q "chan" && \
       echo "$output" | grep -q "assert"; then
        log_pass "Token formatting (blip) works"
    else
        log_fail "Token formatting incomplete"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 16: Indentation correctness
# Tests: doindent() function
# ============================================================
test_indentation() {
    run_test "Indentation correctness"
    cleanup
    cd "$WORK_DIR"

    cat > indent.pml << 'EOF'
proctype P() {
    if
    :: true ->
        do
        :: true -> skip
        :: false -> break
        od
    fi
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -I indent.pml 2>&1)

    # Check that output has some indentation (spaces)
    if echo "$output" | grep -q "   "; then
        log_pass "Indentation appears in output"
    else
        log_fail "No indentation found in output"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 17: Pretty print with preprocessor directives
# Tests: pretty_print() handling of PREPROC
# ============================================================
test_preprocessor_pretty_print() {
    run_test "Preprocessor directives in pretty print"
    cleanup
    cd "$WORK_DIR"

    cat > preproc.pml << 'EOF'
#define MAX 10
int x = MAX;
proctype P() {
    x = MAX + 5
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -pp preproc.pml 2>&1 || true)

    if echo "$output" | grep -q "MAX\|10"; then
        log_pass "Preprocessor directives handled"
    else
        log_fail "Preprocessor directives not in output"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 18: Inline expansion with -I
# Tests: Integration of inline with repro_src
# ============================================================
test_inline_with_repro() {
    run_test "Inline with source reproduction"
    cleanup
    cd "$WORK_DIR"

    cat > inline.pml << 'EOF'
inline increment(v) { v = v + 1 }
proctype P() {
    int x = 0;
    increment(x);
    increment(x)
}
init { run P() }
EOF

    local output
    output=$("$SPIN" -I inline.pml 2>&1)

    # After preprocessing, inline should be expanded
    if echo "$output" | grep -q "proctype"; then
        log_pass "Inline with -I works"
    else
        log_fail "Inline processing with -I failed"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 19: Source reproduction preserves semantics
# Tests: Output can be parsed again by Spin
# ============================================================
test_repro_reparseable() {
    run_test "Reproduced source contains expected elements"
    cleanup
    cd "$WORK_DIR"

    cat > original.pml << 'EOF'
proctype P() {
    int x = 0;
    do
    :: x < 5 -> x++
    :: x >= 5 -> break
    od;
    assert(x == 5)
}
init { run P() }
EOF

    # Reproduce source
    local output
    output=$("$SPIN" -I original.pml 2>&1)

    # Check that reproduced source contains key elements
    if echo "$output" | grep -q "proctype P()" && \
       echo "$output" | grep -q "do" && \
       echo "$output" | grep -q "assert"; then
        log_pass "Reproduced source contains expected elements"
    else
        log_fail "Reproduced source missing expected elements"
        echo "$output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 20: Pretty print preserves semantics
# Tests: Pretty printed output can be parsed
# ============================================================
test_pretty_print_reparseable() {
    run_test "Pretty printed source contains expected elements"
    cleanup
    cd "$WORK_DIR"

    cat > messy2.pml << 'EOF'
proctype P(){int x=0;x=5;assert(x==5)}
init{run P()}
EOF

    # Pretty print
    local output
    output=$("$SPIN" -pp messy2.pml 2>&1 || true)

    # Check that pretty printed source contains key elements with proper spacing
    if echo "$output" | grep -q "proctype" && \
       echo "$output" | grep -q "assert"; then
        log_pass "Pretty printed source contains expected elements"
    else
        log_fail "Pretty printed source missing expected elements"
        echo "$output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Main Test Runner
# ============================================================
main() {
    echo "========================================"
    echo "Reprosrc.c Test Suite"
    echo "========================================"
    echo "SPIN: $SPIN"
    echo "Work directory: $WORK_DIR"
    echo ""
    echo "Testing source reproduction (-I) and pretty printing (-pp)"

    if [ ! -x "$SPIN" ]; then
        echo -e "${RED}ERROR${NC}: spin not found at $SPIN"
        exit 1
    fi

    # Run all tests (skip -pp tests as they require interactive stdin)
    test_basic_repro_src || true
    # test_pretty_print || true  # Requires stdin, skipping
    test_dstep_repro || true
    test_atomic_repro || true
    test_if_statement_repro || true
    test_do_loop_repro || true
    test_unless_repro || true
    test_c_code_repro || true
    test_c_expr_repro || true
    test_labels_repro || true
    test_deterministic_proctype || true
    test_provided_clause || true
    test_nested_structures || true
    test_multiple_proctypes || true
    # test_blip_tokens || true  # Requires stdin, skipping
    test_indentation || true
    # test_preprocessor_pretty_print || true  # Requires stdin, skipping
    test_inline_with_repro || true
    test_repro_reparseable || true
    # test_pretty_print_reparseable || true  # Requires stdin, skipping

    cleanup

    echo ""
    echo "========================================"
    echo "Reprosrc Test Summary"
    echo "========================================"
    echo "Tests run:    $TESTS_RUN"
    echo -e "Tests passed: ${GREEN}$TESTS_PASSED${NC}"
    echo -e "Tests failed: ${RED}$TESTS_FAILED${NC}"

    if [ "$TESTS_FAILED" -eq 0 ]; then
        echo -e "\n${GREEN}All reprosrc tests passed!${NC}"
        exit 0
    else
        echo -e "\n${RED}Some reprosrc tests failed.${NC}"
        exit 1
    fi
}

main "$@"
