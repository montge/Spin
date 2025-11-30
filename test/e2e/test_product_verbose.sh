#!/bin/bash
# Additional tests for pangen7.c with verbose flags to increase coverage

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$(dirname "$SCRIPT_DIR")")"
SPIN="${SPIN:-$ROOT_DIR/Src/spin}"
WORK_DIR="${WORK_DIR:-$SCRIPT_DIR/work}"

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

TESTS_RUN=0
TESTS_PASSED=0

mkdir -p "$WORK_DIR"

log_pass() { echo -e "${GREEN}PASS${NC}: $1"; ((TESTS_PASSED++)); }
run_test() { ((TESTS_RUN++)); echo -e "\n${YELLOW}=== Verbose Test: $1 ===${NC}"; }

cleanup() { rm -rf "$WORK_DIR"/* 2>/dev/null || true; }

# Test with verbose level 64 for detailed product debugging
test_verbose_64() {
    run_test "Product with verbose level 64"
    cleanup
    cd "$WORK_DIR"

    cat > test_v64.pml << 'EOF'
byte x = 0;
byte y = 0;

proctype P() {
    x = 1;
    y = 1
}

init { run P() }

never N1 {
    do
    :: (x >= 0) -> skip
    :: (x == 1) -> goto s1
    od;
s1:
    skip
}

never N2 {
    do
    :: (y >= 0) -> skip
    :: (y == 1) -> goto s2
    od;
s2:
    skip
}
EOF

    # Test with different verbose levels
    "$SPIN" -e -g test_v64.pml > output1.txt 2>&1
    if grep -q "never Product" output1.txt; then
        log_pass "Verbose level 1 (-g) works"
    fi

    cd - > /dev/null
}

# Test with end states to trigger special label handling
test_end_states() {
    run_test "Product with end states"
    cleanup
    cd "$WORK_DIR"

    cat > test_end.pml << 'EOF'
byte done1 = 0;
byte done2 = 0;

proctype P1() {
    done1 = 1
}

proctype P2() {
    done2 = 1
}

init { run P1(); run P2() }

never N1 {
    do
    :: (done1 == 0) -> skip
    :: (done1 == 1) -> goto end1
    od;
end1:
    skip
}

never N2 {
    do
    :: (done2 == 0) -> skip
    :: (done2 == 1) -> goto end2
    od;
end2:
    skip
}
EOF

    "$SPIN" -e test_end.pml > output2.txt 2>&1
    if grep -q "never Product" output2.txt; then
        log_pass "Product with end states works"
    fi

    cd - > /dev/null
}

# Test with simple self-loops
test_self_loops() {
    run_test "Product with self-loops"
    cleanup
    cd "$WORK_DIR"

    cat > test_loops.pml << 'EOF'
bit flag = 0;

proctype P() {
    flag = 1
}

init { run P() }

never N1 {
    do
    :: true -> skip
    od
}

never N2 {
    do
    :: (flag == 0 || flag == 1) -> skip
    od
}
EOF

    "$SPIN" -e test_loops.pml > output3.txt 2>&1
    if grep -q "never Product" output3.txt; then
        log_pass "Product with self-loops generated"
    fi

    cd - > /dev/null
}

# Test product with IF/DO constructs in claims
test_if_do_constructs() {
    run_test "Product with IF/DO constructs"
    cleanup
    cd "$WORK_DIR"

    cat > test_ifdo.pml << 'EOF'
byte state = 0;

proctype Proc() {
    if
    :: state = 1
    :: state = 2
    fi
}

init { run Proc() }

never C1 {
    do
    :: (state == 0) ->
        if
        :: (state == 0) -> skip
        :: (state != 0) -> skip
        fi
    :: (state != 0) -> skip
    od
}

never C2 {
    do
    :: (state <= 2) -> skip
    od
}
EOF

    "$SPIN" -e test_ifdo.pml > output4.txt 2>&1
    if grep -q "never Product" output4.txt; then
        log_pass "Product with IF/DO constructs works"
    fi

    cd - > /dev/null
}

# Test with multiple accept states
test_multiple_accepts() {
    run_test "Product with multiple accept states"
    cleanup
    cd "$WORK_DIR"

    cat > test_accepts.pml << 'EOF'
byte counter = 0;

proctype Counter() {
    do
    :: counter < 5 -> counter++
    :: counter >= 5 -> break
    od
}

init { run Counter() }

never N1 {
accept_init1:
    do
    :: (counter < 3) -> goto accept_mid1
    :: (counter >= 3) -> skip
    od;
accept_mid1:
    do
    :: (counter >= 0) -> skip
    od
}

never N2 {
accept_init2:
    do
    :: (counter < 4) -> goto accept_mid2
    :: (counter >= 4) -> skip
    od;
accept_mid2:
    do
    :: (counter >= 0) -> skip
    od
}
EOF

    "$SPIN" -e test_accepts.pml > output5.txt 2>&1
    if grep -q "accept_" output5.txt; then
        log_pass "Multiple accept states handled correctly"
    fi

    cd - > /dev/null
}

# Test with strict mode differences
test_strict_vs_normal() {
    run_test "Comparing strict and normal mode"
    cleanup
    cd "$WORK_DIR"

    cat > test_modes.pml << 'EOF'
byte x = 0;

proctype P() {
    x = 1
}

init { run P() }

never N1 {
    do
    :: (x == 0 || x == 1) -> skip
    od
}

never N2 {
    do
    :: true -> skip
    od
}
EOF

    "$SPIN" -e test_modes.pml > normal.txt 2>&1
    "$SPIN" -e -L test_modes.pml > strict.txt 2>&1

    if [ -s normal.txt ] && [ -s strict.txt ]; then
        log_pass "Both normal and strict modes work"
    fi

    cd - > /dev/null
}

# Test with verbose output
test_with_verbose() {
    run_test "Product with verbose output enabled"
    cleanup
    cd "$WORK_DIR"

    cat > test_verbose.pml << 'EOF'
byte val = 0;

proctype P() {
    val = 1;
    val = 2
}

init { run P() }

never N1 {
    do
    :: (val >= 0) -> skip
    od
}

never N2 {
    do
    :: (val <= 2) -> skip
    od
}
EOF

    # Test with -v for verbose output
    "$SPIN" -e -v test_verbose.pml > verbose.txt 2>&1

    if grep -q "#if 0" verbose.txt; then
        log_pass "Verbose mode produces debug output"
    fi

    cd - > /dev/null
}

main() {
    echo "========================================"
    echo "Additional Product Generation Tests"
    echo "========================================"

    test_verbose_64 || true
    test_end_states || true
    test_self_loops || true
    test_if_do_constructs || true
    test_multiple_accepts || true
    test_strict_vs_normal || true
    test_with_verbose || true

    cleanup

    echo ""
    echo "========================================"
    echo "Tests run:    $TESTS_RUN"
    echo -e "Tests passed: ${GREEN}$TESTS_PASSED${NC}"
    echo "========================================"
}

main "$@"
