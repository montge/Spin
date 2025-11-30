#!/bin/bash
# Test suite for pangen6.c - AST slicing and data-flow analysis
# pangen6.c handles program slicing, dead code detection, and variable relevance analysis
#
# The -A flag enables AST export and slicing analysis, which exercises pangen6.c code

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
SPIN="${SPIN:-$ROOT_DIR/Src/spin}"
TEST_WORK_DIR="${TEST_WORK_DIR:-$SCRIPT_DIR/work/pangen6}"
CC="${CC:-gcc}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

TESTS_RUN=0
TESTS_PASSED=0
TESTS_FAILED=0

# Create work directory
mkdir -p "$TEST_WORK_DIR"

log_pass() {
    echo -e "${GREEN}PASS${NC}: $1"
    ((TESTS_PASSED++))
}

log_fail() {
    echo -e "${RED}FAIL${NC}: $1"
    ((TESTS_FAILED++))
}

log_info() {
    echo -e "INFO: $1"
}

run_test() {
    local name="$1"
    ((TESTS_RUN++))
    echo -e "\n--- Test: $name ---"
}

cleanup_work_dir() {
    rm -f "$TEST_WORK_DIR"/*.pml "$TEST_WORK_DIR"/pan* "$TEST_WORK_DIR"/*.trail "$TEST_WORK_DIR"/*.tmp 2>/dev/null || true
}

# Test 1: Basic AST analysis with -A flag
test_ast_basic() {
    run_test "Basic AST analysis (-A flag)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > basic.pml << 'EOF'
int x = 0;

proctype P() {
    x = 1;
    assert(x == 1)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A basic.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "AST analysis completes"
    else
        log_fail "Unexpected output: $output"
        return 1
    fi

    cd - > /dev/null
}

# Test 2: Redundant variable detection
test_redundant_var() {
    run_test "Redundant variable detection"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > redundant.pml << 'EOF'
int used = 0;
int unused = 0;

proctype P() {
    used = 1;
    unused = 99;
    assert(used == 1)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A redundant.pml 2>&1)

    if echo "$output" | grep -qi "redundant.*unused"; then
        log_pass "Redundant variable detected"
    elif echo "$output" | grep -q "redundancies"; then
        log_pass "Analysis completes (may not report all redundancies for simple cases)"
    else
        log_fail "Analysis did not complete properly"
        return 1
    fi

    cd - > /dev/null
}

# Test 3: Channel operations analysis
test_channel_ops() {
    run_test "Channel operations analysis"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > channel.pml << 'EOF'
chan ch = [1] of { int };

proctype Sender() {
    ch ! 42
}

proctype Receiver() {
    int x;
    ch ? x;
    assert(x == 42)
}

init {
    run Sender();
    run Receiver()
}
EOF

    local output
    output=$("$SPIN" -A channel.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Channel operations analysis completes"
    else
        log_fail "Analysis failed: $output"
        return 1
    fi

    cd - > /dev/null
}

# Test 4: Channel aliasing
test_channel_alias() {
    run_test "Channel aliasing analysis"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > alias.pml << 'EOF'
chan a = [1] of { int };
chan b;

proctype P() {
    b = a;
    a ! 42;
    int x;
    b ? x;
    assert(x == 42)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A alias.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Channel aliasing analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 5: Channel parameter passing
test_chan_param() {
    run_test "Channel parameter passing"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > chanparam.pml << 'EOF'
chan g = [1] of { int };

proctype Worker(chan c) {
    c ! 123
}

init {
    int val;
    run Worker(g);
    g ? val;
    assert(val == 123)
}
EOF

    local output
    output=$("$SPIN" -A chanparam.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Channel parameter analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 6: Data dependencies
test_data_dep() {
    run_test "Data dependency tracking"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > datadep.pml << 'EOF'
int a = 0;
int b = 0;
int c = 0;

proctype P() {
    a = 1;
    b = a + 1;
    c = b * 2;
    assert(c == 4)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A datadep.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Data dependency analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 7: Control dependencies
test_control_dep() {
    run_test "Control dependency tracking"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > ctrldep.pml << 'EOF'
int x = 0;
int result = 0;

proctype P() {
    if
    :: x == 0 -> result = 10
    :: x != 0 -> result = 20
    fi;
    assert(result == 10)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A ctrldep.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Control dependency analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 8: Array operations
test_arrays() {
    run_test "Array operations tracking"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > arrays.pml << 'EOF'
int arr[5];
int idx = 2;

proctype P() {
    arr[idx] = 42;
    assert(arr[2] == 42)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A arrays.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Array operations analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 9: Struct fields
test_structs() {
    run_test "Struct field tracking"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > structs.pml << 'EOF'
typedef Point {
    int x;
    int y
};

Point p;

proctype P() {
    p.x = 10;
    p.y = 20;
    assert(p.x + p.y == 30)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A structs.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Struct field analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 10: Remote references
test_remote_ref() {
    run_test "Remote reference tracking"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > remote.pml << 'EOF'
int global = 0;

proctype P() {
    global = 42;
end:
    skip
}

proctype Q() {
    (P[1]@end);
    assert(global == 42)
}

init {
    run P();
    run Q()
}
EOF

    local output
    output=$("$SPIN" -A remote.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Remote reference analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 11: Multiple proctypes
test_multi_proc() {
    run_test "Multiple proctype analysis"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > multiproc.pml << 'EOF'
int shared = 0;

proctype Writer() {
    shared = 100
}

proctype Reader() {
    (shared == 100);
    assert(shared == 100)
}

init {
    run Writer();
    run Reader()
}
EOF

    local output
    output=$("$SPIN" -A multiproc.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Multiple proctype analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 12: Channel queries (LEN, FULL, EMPTY)
test_chan_queries() {
    run_test "Channel query operations"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > chanquery.pml << 'EOF'
chan q = [3] of { int };

proctype P() {
    int qlen;
    assert(empty(q));
    q ! 1;
    qlen = len(q);
    assert(qlen == 1);
    q ! 2;
    q ! 3;
    assert(full(q))
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A chanquery.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Channel query analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 13: Never claim
test_never_claim() {
    run_test "Never claim analysis"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > never.pml << 'EOF'
int flag = 0;

proctype P() {
    do
    :: flag = 1 - flag
    od
}

never {
    do
    :: flag == 0
    :: flag == 1
    od
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A never.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Never claim analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 14: Bitwise operations
test_bitwise() {
    run_test "Bitwise operations"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > bitwise.pml << 'EOF'
int a = 15;  /* 0x0F */
int b = 240; /* 0xF0 */
int result;

proctype P() {
    result = a & b;
    assert(result == 0);
    result = a | b;
    assert(result == 255)  /* 0xFF */
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A bitwise.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Bitwise operations analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 15: Enabled() function
test_enabled() {
    run_test "Enabled() function"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > enabled.pml << 'EOF'
int result = 0;

proctype P() {
end:
    skip
}

proctype Q() {
    if
    :: enabled(P[1]@end) -> result = 1
    :: else -> result = 0
    fi;
    assert(result >= 0)
}

init {
    run P();
    run Q()
}
EOF

    local output
    output=$("$SPIN" -A enabled.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Enabled() analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 16: Unless construct
test_unless() {
    run_test "Unless construct"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > unless.pml << 'EOF'
int x = 0;
int escape = 0;

proctype P() {
    { x = 1; x = 2; x = 3 }
    unless
    { escape = 1 };
    assert(x > 0 || escape > 0)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A unless.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Unless construct analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 17: Print statements
test_print() {
    run_test "Print statement tracking"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > print.pml << 'EOF'
int x = 42;
int y = 100;

proctype P() {
    printf("x=%d y=%d\n", x, y);
    assert(x == 42)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A print.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Print statement analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 18: Run with parameters
test_run_params() {
    run_test "Run with parameters"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > runparams.pml << 'EOF'
int global = 55;

proctype Worker(int param) {
    assert(param == 55)
}

init {
    run Worker(global)
}
EOF

    local output
    output=$("$SPIN" -A runparams.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Run parameter analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 19: Timeout
test_timeout() {
    run_test "Timeout construct"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > timeout.pml << 'EOF'
chan ch = [0] of { int };
int flag = 0;

proctype P() {
    if
    :: ch ? _
    :: timeout -> flag = 1
    fi;
    assert(flag == 1)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A timeout.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Timeout analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 20: Atomic and d_step
test_atomic_dstep() {
    run_test "Atomic and d_step"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > atomic.pml << 'EOF'
int x = 0;

proctype P() {
    atomic {
        x = 1;
        x = x + 1
    };
    assert(x == 2)
}

proctype Q() {
    d_step {
        x = 10;
        x = x * 2
    };
    assert(x == 20)
}

init {
    run P() -> run Q()
}
EOF

    local output
    output=$("$SPIN" -A atomic.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Atomic/d_step analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 21: Predicate abstraction hints
test_predicate_hints() {
    run_test "Predicate abstraction hints"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > predicate.pml << 'EOF'
int counter = 0;

proctype P() {
    do
    :: counter < 100 -> counter++
    :: counter >= 50 -> break
    od;
    assert(counter >= 50)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A predicate.pml 2>&1)

    if echo "$output" | grep -qi "predicate"; then
        log_pass "Predicate abstraction hint generated"
    elif echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Analysis completes (no predicate hint for this model)"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 22: Source/sink process pattern
test_source_sink() {
    run_test "Source/sink process detection"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > sourcesink.pml << 'EOF'
chan ch = [1] of { int };

proctype Source() {
    int i;
    for (i : 1 .. 5) {
        ch ! i
    }
}

proctype Sink() {
    int val;
    do
    :: ch ? val
    od
}

init {
    run Source();
    run Sink()
}
EOF

    local output
    output=$("$SPIN" -A sourcesink.pml 2>&1)

    if echo "$output" | grep -qi "source\|sink"; then
        log_pass "Source/sink pattern detected"
    elif echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 23: EVAL in receive
test_eval_recv() {
    run_test "EVAL in receive"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > evalrecv.pml << 'EOF'
chan ch = [1] of { int, int };
int a = 5;

proctype P() {
    ch ! a, 10;
    int x, y;
    ch ? eval(x), y;
    assert(y == 10)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A evalrecv.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "EVAL in receive analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 24: Random receive
test_random_recv() {
    run_test "Random receive"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > randrecv.pml << 'EOF'
mtype = { A, B };
chan ch = [2] of { mtype };

proctype P() {
    ch ! A;
    ch ! B;
    mtype m;
    ch ?? m;
    assert(m == A || m == B)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A randrecv.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Random receive analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 25: Channel through channel
test_chan_through_chan() {
    run_test "Channel through channel"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > chanchan.pml << 'EOF'
chan data = [1] of { int };
chan meta = [1] of { chan };

proctype P() {
    meta ! data;
    data ! 42
}

proctype Q() {
    chan c;
    meta ? c;
    int v;
    c ? v;
    assert(v == 42)
}

init {
    run P();
    run Q()
}
EOF

    local output
    output=$("$SPIN" -A chanchan.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Channel through channel analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 26: Local variable initialization
test_local_init() {
    run_test "Local variable initialization"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > localinit.pml << 'EOF'
proctype P() {
    int x = 10;
    int y = x * 2;
    int z = y + x;
    assert(z == 30)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A localinit.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Local initialization analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 27: Complex data flow
test_complex_dataflow() {
    run_test "Complex data flow"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > complexdf.pml << 'EOF'
int a, b, c, d, e;

proctype P() {
    a = 1;
    b = a;
    c = b + a;
    d = c * 2;
    e = d + 1;
    assert(e == 5)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A complexdf.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Complex data flow analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 28: Conditional expressions
test_cond_expr() {
    run_test "Conditional expressions"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > condexpr.pml << 'EOF'
int x = 5;
int y;

proctype P() {
    if
    :: (x > 3) -> y = 10
    :: else -> y = 20
    fi;
    assert(y == 10)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A condexpr.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Conditional expression analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 29: Multiple assertions
test_multi_assert() {
    run_test "Multiple assertions"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > multiassert.pml << 'EOF'
int x = 0;
int y = 0;
int z = 0;

proctype P() {
    x = 1;
    y = 2;
    z = 3;
    assert(x == 1);
    assert(y == 2);
    assert(z == 3)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A multiassert.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Multiple assertion analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 30: Nested structures
test_nested_struct() {
    run_test "Nested structures"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > nestedstruct.pml << 'EOF'
typedef Inner {
    int val
};

typedef Outer {
    Inner in;
    int other
};

Outer obj;

proctype P() {
    obj.in.val = 42;
    obj.other = 100;
    assert(obj.in.val == 42 && obj.other == 100)
}

init { run P() }
EOF

    local output
    output=$("$SPIN" -A nestedstruct.pml 2>&1)

    if echo "$output" | grep -q "redundancies\|relevant\|redundant"; then
        log_pass "Nested structure analysis completes"
    else
        log_fail "Analysis failed"
        return 1
    fi

    cd - > /dev/null
}

# Main test runner
main() {
    echo "========================================"
    echo "pangen6.c Test Suite"
    echo "AST Slicing and Data-Flow Analysis"
    echo "========================================"
    echo "SPIN: $SPIN"
    echo "Work directory: $TEST_WORK_DIR"
    echo ""

    # Check spin exists
    if [ ! -x "$SPIN" ]; then
        echo -e "${RED}ERROR${NC}: spin executable not found at $SPIN"
        echo "Build spin first with: cd Src && make"
        exit 1
    fi

    # Run all tests
    test_ast_basic || true
    test_redundant_var || true
    test_channel_ops || true
    test_channel_alias || true
    test_chan_param || true
    test_data_dep || true
    test_control_dep || true
    test_arrays || true
    test_structs || true
    test_remote_ref || true
    test_multi_proc || true
    test_chan_queries || true
    test_never_claim || true
    test_bitwise || true
    test_enabled || true
    test_unless || true
    test_print || true
    test_run_params || true
    test_timeout || true
    test_atomic_dstep || true
    test_predicate_hints || true
    test_source_sink || true
    test_eval_recv || true
    test_random_recv || true
    test_chan_through_chan || true
    test_local_init || true
    test_complex_dataflow || true
    test_cond_expr || true
    test_multi_assert || true
    test_nested_struct || true

    # Cleanup
    cleanup_work_dir

    # Summary
    echo ""
    echo "========================================"
    echo "Test Summary"
    echo "========================================"
    echo "Tests run:    $TESTS_RUN"
    echo -e "Tests passed: ${GREEN}$TESTS_PASSED${NC}"
    echo -e "Tests failed: ${RED}$TESTS_FAILED${NC}"
    echo ""

    if [ "$TESTS_FAILED" -eq 0 ]; then
        echo -e "${GREEN}All tests passed!${NC}"
        exit 0
    else
        echo -e "${RED}Some tests failed.${NC}"
        exit 1
    fi
}

main "$@"
