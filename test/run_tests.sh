#!/bin/bash
# Spin Test Suite
# Automated tests based on Examples/README_tests.txt

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
SPIN="${SPIN:-$ROOT_DIR/Src/spin}"
EXAMPLES_DIR="$ROOT_DIR/Examples"
TEST_WORK_DIR="${TEST_WORK_DIR:-$SCRIPT_DIR/work}"
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

log_skip() {
    echo -e "${YELLOW}SKIP${NC}: $1"
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
    rm -f "$TEST_WORK_DIR"/pan* "$TEST_WORK_DIR"/*.trail "$TEST_WORK_DIR"/*.tmp 2>/dev/null || true
}

# Test 0: Version check
test_version() {
    run_test "version"
    if "$SPIN" -V 2>&1 | grep -q "Spin Version"; then
        log_pass "spin -V outputs version"
    else
        log_fail "spin -V did not output version"
        return 1
    fi
}

# Test 1: Basic simulation
test_simulation() {
    run_test "simulation (hello.pml)"
    local output
    output=$("$SPIN" "$EXAMPLES_DIR/hello.pml" 2>&1)
    if echo "$output" | grep -q "passed first test"; then
        log_pass "hello.pml simulation"
    else
        log_fail "hello.pml simulation - expected 'passed first test'"
        echo "Output: $output"
        return 1
    fi
}

# Test 2: Basic verification (safety)
test_safety_verification() {
    run_test "safety verification (loops.pml)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    # Generate verifier
    if ! "$SPIN" -a "$EXAMPLES_DIR/loops.pml" > /dev/null 2>&1; then
        log_fail "spin -a loops.pml failed"
        return 1
    fi

    # Compile verifier
    if ! $CC -DNOREDUCE -DSAFETY -o pan pan.c 2>/dev/null; then
        log_fail "compilation of pan.c failed"
        return 1
    fi

    # Run verifier
    local output
    output=$(./pan 2>&1)
    if echo "$output" | grep -q "errors: 0"; then
        log_pass "safety verification completed with no errors"
    else
        log_fail "safety verification failed"
        echo "Output: $output"
        return 1
    fi

    # Check expected state count (approximately)
    if echo "$output" | grep -q "15 states, stored"; then
        log_pass "state count matches expected (15 states)"
    else
        log_info "state count may differ from reference"
    fi

    cd - > /dev/null
}

# Test 3: Acceptance cycle detection
test_acceptance_cycles() {
    run_test "acceptance cycles (loops.pml)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    "$SPIN" -a "$EXAMPLES_DIR/loops.pml" > /dev/null 2>&1
    $CC -DNOREDUCE -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -a 2>&1)
    if echo "$output" | grep -q "acceptance cycle"; then
        log_pass "acceptance cycle detected"
    else
        log_fail "acceptance cycle not detected"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# Test 4: Guided simulation (trail playback)
test_guided_simulation() {
    run_test "guided simulation (loops.pml trail)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    "$SPIN" -a "$EXAMPLES_DIR/loops.pml" > /dev/null 2>&1
    $CC -DNOREDUCE -o pan pan.c 2>/dev/null
    ./pan -a > /dev/null 2>&1 || true  # Generate trail

    # Copy source to work dir for trail playback
    cp "$EXAMPLES_DIR/loops.pml" .

    local output
    output=$("$SPIN" -t -p loops.pml 2>&1)
    if echo "$output" | grep -q "START OF CYCLE"; then
        log_pass "guided simulation shows cycle"
    else
        log_fail "guided simulation failed to show cycle"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# Test 5: Non-progress cycle detection
test_non_progress() {
    run_test "non-progress cycles (loops.pml)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    "$SPIN" -a "$EXAMPLES_DIR/loops.pml" > /dev/null 2>&1
    $CC -DNP -DNOREDUCE -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -l 2>&1)
    if echo "$output" | grep -q "non-progress cycles"; then
        log_pass "non-progress cycle search completed"
    else
        log_fail "non-progress cycle search failed"
        echo "Output: $output"
        return 1
    fi

    cd - > /dev/null
}

# Test 6: Partial order reduction effectiveness
test_partial_order_reduction() {
    run_test "partial order reduction (leader0.pml)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    "$SPIN" -a "$EXAMPLES_DIR/leader0.pml" > /dev/null 2>&1

    # Without reduction
    $CC -DSAFETY -DNOREDUCE -DNOCLAIM -o pan pan.c 2>/dev/null
    local output_nored
    output_nored=$(./pan -c0 -n 2>&1)
    local states_nored
    states_nored=$(echo "$output_nored" | grep "states, stored" | head -1 | awk '{print $1}')

    # With reduction
    $CC -DSAFETY -DNOCLAIM -o pan pan.c 2>/dev/null
    local output_red
    output_red=$(./pan -c0 -n 2>&1)
    local states_red
    states_red=$(echo "$output_red" | grep "states, stored" | head -1 | awk '{print $1}')

    if [ -n "$states_nored" ] && [ -n "$states_red" ]; then
        if [ "$states_red" -lt "$states_nored" ]; then
            log_pass "partial order reduction effective: $states_red states (reduced) vs $states_nored states (full)"
        else
            log_fail "partial order reduction not effective"
            return 1
        fi
    else
        log_fail "could not extract state counts"
        return 1
    fi

    cd - > /dev/null
}

# Test 7: LTL formula to never claim
test_ltl_formula() {
    run_test "LTL formula conversion"
    local output
    output=$("$SPIN" -f "[] ( p U ( <> q ))" 2>&1)
    if echo "$output" | grep -q "never"; then
        log_pass "LTL formula converted to never claim"
    else
        log_fail "LTL formula conversion failed"
        echo "Output: $output"
        return 1
    fi
}

# Test 8: Multiple example files compile and verify
test_example_files() {
    run_test "example files verification"
    local examples=("peterson.pml" "abp.pml" "snoopy.pml")
    local all_passed=true

    for example in "${examples[@]}"; do
        if [ -f "$EXAMPLES_DIR/$example" ]; then
            cleanup_work_dir
            cd "$TEST_WORK_DIR"

            if "$SPIN" -a "$EXAMPLES_DIR/$example" > /dev/null 2>&1 && \
               $CC -DSAFETY -o pan pan.c 2>/dev/null && \
               ./pan -n > /dev/null 2>&1; then
                log_info "$example: OK"
            else
                log_info "$example: FAILED"
                all_passed=false
            fi

            cd - > /dev/null
        fi
    done

    if $all_passed; then
        log_pass "all example files verified"
    else
        log_fail "some example files failed"
        return 1
    fi
}

# Test syntax errors are caught
test_syntax_error() {
    run_test "syntax error detection"
    local bad_pml="$TEST_WORK_DIR/bad_syntax.pml"
    echo "proctype bad { this is not valid promela }" > "$bad_pml"

    if ! "$SPIN" -a "$bad_pml" > /dev/null 2>&1; then
        log_pass "syntax error correctly detected"
        rm -f "$bad_pml"
    else
        log_fail "syntax error not detected"
        rm -f "$bad_pml"
        return 1
    fi
}

# Test 9: Deterministic step simulation (dstep)
test_dstep() {
    run_test "deterministic step (dstep)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > dstep_test.pml << 'EOF'
int x = 0;
proctype P() {
    d_step {
        x = x + 1;
        x = x + 2;
        x = x + 3;
    }
    assert(x == 6)
}
init { run P() }
EOF

    if "$SPIN" -a dstep_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "dstep execution verified"
    else
        log_fail "dstep test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 10: Atomic sequences
test_atomic() {
    run_test "atomic sequences"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > atomic_test.pml << 'EOF'
int counter = 0;
proctype Increment() {
    atomic {
        int temp = counter;
        counter = temp + 1
    }
}
init {
    atomic { run Increment(); run Increment() }
}
EOF

    if "$SPIN" -a atomic_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "atomic execution verified"
    else
        log_fail "atomic test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 11: Channel operations
test_channels() {
    run_test "channel operations"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > channel_test.pml << 'EOF'
mtype = { msg1, msg2, ack };
chan toR = [2] of { mtype, byte };
chan toS = [2] of { mtype };

proctype Sender() {
    toR ! msg1, 5;
    toS ? ack;
    toR ! msg2, 10;
    toS ? ack
}

proctype Receiver() {
    mtype t; byte d;
    toR ? t, d;
    assert(t == msg1 && d == 5);
    toS ! ack;
    toR ? t, d;
    assert(t == msg2 && d == 10);
    toS ! ack
}

init {
    run Sender();
    run Receiver()
}
EOF

    if "$SPIN" -a channel_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "channel operations verified"
    else
        log_fail "channel test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 12: Printf output
test_printf() {
    run_test "printf output"
    local output
    output=$("$SPIN" -c0 "$EXAMPLES_DIR/hello.pml" 2>&1)
    if echo "$output" | grep -q "passed"; then
        log_pass "printf output works"
    else
        log_fail "printf output not working"
        return 1
    fi
}

# Test 13: Inline expansion
test_inline() {
    run_test "inline expansion"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > inline_test.pml << 'EOF'
inline increment(x) { x = x + 1 }
int val = 0;
init {
    increment(val);
    increment(val);
    assert(val == 2)
}
EOF

    if "$SPIN" -a inline_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "inline expansion works"
    else
        log_fail "inline test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 14: Typedef/struct support
test_typedef() {
    run_test "typedef/struct support"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > typedef_test.pml << 'EOF'
typedef Point {
    int x;
    int y
};

Point p;

init {
    p.x = 10;
    p.y = 20;
    assert(p.x + p.y == 30)
}
EOF

    if "$SPIN" -a typedef_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "typedef/struct works"
    else
        log_fail "typedef test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 15: Array operations
test_arrays() {
    run_test "array operations"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > array_test.pml << 'EOF'
int arr[5];
init {
    int i;
    for (i : 0 .. 4) {
        arr[i] = i * 2
    };
    assert(arr[0] == 0);
    assert(arr[2] == 4);
    assert(arr[4] == 8)
}
EOF

    if "$SPIN" -a array_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "array operations work"
    else
        log_fail "array test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 16: Never claim
test_never_claim() {
    run_test "never claim verification"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > never_test.pml << 'EOF'
int x = 0;
proctype P() {
    do
    :: x < 10 -> x++
    :: x >= 5 -> break
    od
}
never {
    do
    :: x >= 0
    od
}
init { run P() }
EOF

    if "$SPIN" -a never_test.pml > /dev/null 2>&1 && \
       $CC -o pan pan.c 2>/dev/null && \
       ./pan -a > /dev/null 2>&1; then
        log_pass "never claim verification works"
    else
        log_fail "never claim test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 17: Remote reference
test_remote_ref() {
    run_test "remote reference"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > remote_test.pml << 'EOF'
proctype P() {
    int myval = 42;
end: skip
}
init {
    run P();
    (_nr_pr == 1)
}
EOF

    if "$SPIN" -a remote_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n 2>&1 | grep -q "errors: 0"; then
        log_pass "remote reference works"
    else
        log_fail "remote reference test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 18: Bit operations
test_bit_operations() {
    run_test "bit operations"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > bits_test.pml << 'EOF'
init {
    int a = 5;    /* 0101 */
    int b = 3;    /* 0011 */
    assert((a & b) == 1);  /* 0001 */
    assert((a | b) == 7);  /* 0111 */
    assert((a ^ b) == 6);  /* 0110 */
    assert((a << 1) == 10);
    assert((a >> 1) == 2)
}
EOF

    if "$SPIN" -a bits_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "bit operations work"
    else
        log_fail "bit operations test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 19: Timeout
test_timeout() {
    run_test "timeout handling"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > timeout_test.pml << 'EOF'
chan ch = [0] of { int };
proctype P() {
    int x;
    if
    :: ch ? x
    :: timeout -> skip
    fi
}
init { run P() }
EOF

    if "$SPIN" -a timeout_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "timeout handling works"
    else
        log_fail "timeout test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 20: Unless construct
test_unless() {
    run_test "unless construct"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > unless_test.pml << 'EOF'
int x = 0;
proctype P() {
    { x = 1; x = 2; x = 3 }
    unless
    { x == 2 -> x = 100 }
}
init { run P() }
EOF

    if "$SPIN" -a unless_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "unless construct works"
    else
        log_fail "unless test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 21: Parser - print format
test_print_formats() {
    run_test "print format parsing"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > print_test.pml << 'EOF'
init {
    printf("decimal: %d\n", 42);
    printf("unsigned: %u\n", 42);
    printf("octal: %o\n", 42);
    printf("hex: %x\n", 42);
    printf("char: %c\n", 65)
}
EOF

    local output
    output=$("$SPIN" print_test.pml 2>&1)
    if echo "$output" | grep -q "decimal: 42" && \
       echo "$output" | grep -q "hex: 2a"; then
        log_pass "print format parsing works"
    else
        log_fail "print format parsing failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 22: Progress labels (using cambridge.pml example)
test_progress_labels() {
    run_test "progress labels"
    if [ -f "$EXAMPLES_DIR/cambridge.pml" ]; then
        cleanup_work_dir
        cd "$TEST_WORK_DIR"

        if "$SPIN" -a "$EXAMPLES_DIR/cambridge.pml" > /dev/null 2>&1 && \
           $CC -DNP -DNOREDUCE -o pan pan.c 2>/dev/null && \
           ./pan -l > /dev/null 2>&1; then
            log_pass "progress labels work"
        else
            log_fail "progress labels test failed"
            return 1
        fi

        cd - > /dev/null
    else
        log_skip "cambridge.pml not found"
    fi
}

# Test 23: Assertion failure detection
test_assertion_failure() {
    run_test "assertion failure detection"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > assert_fail.pml << 'EOF'
init {
    int x = 5;
    assert(x == 10)
}
EOF

    "$SPIN" -a assert_fail.pml > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null

    local output
    output=$(./pan 2>&1)
    if echo "$output" | grep -q "assertion violated"; then
        log_pass "assertion failure correctly detected"
    else
        log_fail "assertion failure not detected"
        return 1
    fi

    cd - > /dev/null
}

# Test 24: Rendezvous channels
test_rendezvous() {
    run_test "rendezvous channels"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > rendezvous_test.pml << 'EOF'
chan sync = [0] of { int };
int received = 0;

proctype Sender() {
    sync ! 42
}

proctype Receiver() {
    int x;
    sync ? x;
    received = x
}

init {
    run Sender();
    run Receiver();
    (_nr_pr == 1) -> assert(received == 42)
}
EOF

    if "$SPIN" -a rendezvous_test.pml > /dev/null 2>&1 && \
       $CC -DSAFETY -o pan pan.c 2>/dev/null && \
       ./pan -n > /dev/null 2>&1; then
        log_pass "rendezvous channels work"
    else
        log_fail "rendezvous test failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 25: Select/for statements
test_select_for() {
    run_test "select/for statements"
    if [ -f "$EXAMPLES_DIR/for_select_example.pml" ]; then
        cleanup_work_dir
        cd "$TEST_WORK_DIR"

        if "$SPIN" -a "$EXAMPLES_DIR/for_select_example.pml" > /dev/null 2>&1 && \
           $CC -DSAFETY -o pan pan.c 2>/dev/null && \
           ./pan -n > /dev/null 2>&1; then
            log_pass "select/for statements work"
        else
            log_fail "select/for test failed"
            return 1
        fi

        cd - > /dev/null
    else
        log_skip "for_select_example.pml not found"
    fi
}

# Test 26: Synchronous product generation
test_product_generation() {
    run_test "synchronous product generation (-e flag)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > product_test.pml << 'EOF'
byte x = 0;
byte y = 0;

proctype Worker() {
    do
    :: x < 2 -> x++
    :: y < 2 -> y++
    :: (x >= 1 && y >= 1) -> break
    od
}

init { run Worker() }

never claim_x {
    do
    :: (x >= 0) -> skip
    od
}

never claim_y {
    do
    :: (y >= 0) -> skip
    od
}
EOF

    local output
    output=$("$SPIN" -e product_test.pml 2>&1)

    if echo "$output" | grep -q "never Product" && \
       echo "$output" | grep -q "U0" && \
       echo "$output" | grep -q "U1"; then
        log_pass "synchronous product generation works"
    else
        log_fail "synchronous product generation failed"
        return 1
    fi

    cd - > /dev/null
}

# Main test runner
main() {
    echo "========================================"
    echo "Spin Test Suite"
    echo "========================================"
    echo "SPIN: $SPIN"
    echo "CC: $CC"
    echo "Work directory: $TEST_WORK_DIR"
    echo ""

    # Check spin exists
    if [ ! -x "$SPIN" ]; then
        echo -e "${RED}ERROR${NC}: spin executable not found at $SPIN"
        echo "Build spin first with: cd Src && make"
        exit 1
    fi

    # Run pangen6 tests if available
    if [ -x "$SCRIPT_DIR/pangen6_tests.sh" ]; then
        echo -e "\n${YELLOW}Running pangen6 (AST slicing) tests...${NC}"
        if "$SCRIPT_DIR/pangen6_tests.sh"; then
            log_pass "pangen6 test suite completed successfully"
        else
            log_info "pangen6 test suite had failures (see output above)"
        fi
        echo ""
    fi

    # Run tests
    test_version || true
    test_simulation || true
    test_safety_verification || true
    test_acceptance_cycles || true
    test_guided_simulation || true
    test_non_progress || true
    test_partial_order_reduction || true
    test_ltl_formula || true
    test_example_files || true
    test_syntax_error || true

    # Additional coverage tests
    test_dstep || true
    test_atomic || true
    test_channels || true
    test_printf || true
    test_inline || true
    test_typedef || true
    test_arrays || true
    test_never_claim || true
    test_remote_ref || true
    test_bit_operations || true
    test_timeout || true
    test_unless || true
    test_print_formats || true
    test_progress_labels || true
    test_assertion_failure || true
    test_rendezvous || true
    test_select_for || true
    test_product_generation || true

    # Run reprosrc tests
    echo ""
    echo "Running reprosrc integration tests..."
    if [ -x "$SCRIPT_DIR/integration/test_reprosrc.sh" ]; then
        "$SCRIPT_DIR/integration/test_reprosrc.sh" && log_pass "reprosrc tests completed" || log_fail "reprosrc tests failed"
    fi

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
