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
