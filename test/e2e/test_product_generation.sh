#!/bin/bash
# Tests for synchronous product generation (pangen7.c)
# Tests the -e flag for computing products of multiple never claims

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$(dirname "$SCRIPT_DIR")")"
SPIN="${SPIN:-$ROOT_DIR/Src/spin}"
WORK_DIR="${WORK_DIR:-$SCRIPT_DIR/work}"
CC="${CC:-gcc}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

TESTS_RUN=0
TESTS_PASSED=0
TESTS_FAILED=0

mkdir -p "$WORK_DIR"

log_pass() { echo -e "${GREEN}PASS${NC}: $1"; ((TESTS_PASSED++)); }
log_fail() { echo -e "${RED}FAIL${NC}: $1"; ((TESTS_FAILED++)); }
log_info() { echo -e "${BLUE}INFO${NC}: $1"; }
run_test() { ((TESTS_RUN++)); echo -e "\n${YELLOW}=== Test: $1 ===${NC}"; }

cleanup() { rm -rf "$WORK_DIR"/* 2>/dev/null || true; }

# ============================================================
# Test 1: Basic product generation with two claims
# ============================================================
test_basic_product() {
    run_test "Basic product generation with two claims"
    cleanup
    cd "$WORK_DIR"

    cat > test_model.pml << 'EOF'
byte x = 0;
byte y = 0;

proctype Worker() {
    do
    :: x < 3 -> x++
    :: y < 3 -> y++
    :: (x >= 2 && y >= 2) -> break
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

    log_info "Generating synchronous product..."
    local output
    output=$("$SPIN" -e test_model.pml 2>&1)

    if echo "$output" | grep -q "never Product"; then
        log_info "Product automaton generated successfully"
    else
        log_fail "Product automaton not generated"
        echo "Output: $output"
        return 1
    fi

    # Check that it contains unfolding sections U0 and U1
    if echo "$output" | grep -q "U0" && echo "$output" | grep -q "U1"; then
        log_pass "Product contains expected unfolding sections"
    else
        log_fail "Missing unfolding sections in product"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 2: Product with accept labels
# ============================================================
test_product_with_accept() {
    run_test "Product with accept labels"
    cleanup
    cd "$WORK_DIR"

    cat > test_accept.pml << 'EOF'
byte counter = 0;

proctype Counter() {
    do
    :: counter < 10 -> counter++
    :: counter >= 5 -> break
    od
}

init { run Counter() }

never N1 {
    do
    :: (counter < 10) -> skip
    :: (counter >= 5) -> goto accept1
    od;
accept1:
    skip
}

never N2 {
    do
    :: (counter >= 0) -> skip
    :: (counter == 7) -> goto accept2
    od;
accept2:
    skip
}
EOF

    log_info "Generating product with accept labels..."
    local output
    output=$("$SPIN" -e test_accept.pml 2>&1)

    if echo "$output" | grep -q "never Product"; then
        log_info "Product automaton generated"
    else
        log_fail "Product automaton not generated"
        return 1
    fi

    # Check for accept labels in the product
    if echo "$output" | grep -q "accept_"; then
        log_pass "Accept labels preserved in product"
    else
        log_fail "Accept labels missing in product"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 3: Product with three claims
# ============================================================
test_three_claims() {
    run_test "Product with three never claims"
    cleanup
    cd "$WORK_DIR"

    cat > test_three.pml << 'EOF'
bit flag1 = 0;
bit flag2 = 0;
bit flag3 = 0;

proctype Worker() {
    flag1 = 1;
    flag2 = 1;
    flag3 = 1
}

init { run Worker() }

never C1 {
    do
    :: (flag1 == 0 || flag1 == 1) -> skip
    od
}

never C2 {
    do
    :: (flag2 == 0 || flag2 == 1) -> skip
    od
}

never C3 {
    do
    :: (flag3 == 0 || flag3 == 1) -> skip
    od
}
EOF

    log_info "Generating product with three claims..."
    local output
    output=$("$SPIN" -e test_three.pml 2>&1)

    if echo "$output" | grep -q "never Product"; then
        log_info "Product automaton generated"
    else
        log_fail "Product automaton not generated"
        return 1
    fi

    # Should have U0, U1, and U2 sections
    if echo "$output" | grep -q "U0" && echo "$output" | grep -q "U1" && echo "$output" | grep -q "U2"; then
        log_pass "Product contains all three unfolding sections"
    else
        log_fail "Missing unfolding sections for three claims"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 4: Product with strict language intersection (-L flag)
# ============================================================
test_strict_intersection() {
    run_test "Strict language intersection with -e -L"
    cleanup
    cd "$WORK_DIR"

    cat > test_strict.pml << 'EOF'
byte x = 0;

proctype P() {
    x = 1;
    x = 2
}

init { run P() }

never N1 {
    do
    :: (x >= 0) -> skip
    od
}

never N2 {
    do
    :: (x <= 2) -> skip
    od
}
EOF

    log_info "Testing strict language intersection..."
    local output
    output=$("$SPIN" -e -L test_strict.pml 2>&1)

    if echo "$output" | grep -q "never Product"; then
        log_pass "Strict intersection product generated successfully"
    else
        log_fail "Strict intersection failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 5: Product with verbose output
# ============================================================
test_product_verbose() {
    run_test "Product generation with verbose output"
    cleanup
    cd "$WORK_DIR"

    cat > test_verbose.pml << 'EOF'
byte val = 0;

proctype P() {
    val = 1
}

init { run P() }

never N1 {
    do
    :: (val == 0 || val == 1) -> skip
    od
}

never N2 {
    do
    :: true -> skip
    od
}
EOF

    log_info "Testing verbose product generation..."
    local output
    output=$("$SPIN" -e -v test_verbose.pml 2>&1)

    if echo "$output" | grep -q "#if 0"; then
        log_info "Verbose output includes debug information"
    else
        log_fail "Verbose output missing debug information"
        return 1
    fi

    if echo "$output" | grep -q "claim.*selfloop"; then
        log_pass "Verbose mode provides additional diagnostic info"
    else
        log_pass "Product generated with verbose flag"
    fi

    cd - > /dev/null
}

# ============================================================
# Test 6: Product with different claim state structures
# ============================================================
test_complex_claims() {
    run_test "Product with complex claim structures"
    cleanup
    cd "$WORK_DIR"

    cat > test_complex.pml << 'EOF'
byte state = 0;

proctype Machine() {
    state = 1;
    state = 2;
    state = 3;
    state = 0
}

init { run Machine() }

never Progress {
    do
    :: (state == 0) -> goto s1
    :: (state > 0) -> skip
    od;
s1:
    do
    :: (state == 1) -> goto s2
    :: (state != 1) -> skip
    od;
s2:
    do
    :: (state == 2) -> goto accept_prog
    :: (state != 2) -> skip
    od;
accept_prog:
    skip
}

never Safety {
    do
    :: (state <= 3) -> skip
    :: (state > 3) -> goto error
    od;
error:
    false
}
EOF

    log_info "Testing complex claim structures..."
    local output
    output=$("$SPIN" -e test_complex.pml 2>&1)

    if echo "$output" | grep -q "never Product"; then
        log_pass "Complex claims product generated successfully"
    else
        log_fail "Complex claims product generation failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Test 7: Verify product can be used for verification
# ============================================================
test_product_verification() {
    run_test "Verify generated product can be used"
    cleanup
    cd "$WORK_DIR"

    # Create a simple model
    cat > base_model.pml << 'EOF'
byte x = 0;

proctype P() {
    x = 1;
    x = 2
}

init { run P() }
EOF

    cat > multi_claims.pml << 'EOF'
byte x = 0;

proctype P() {
    x = 1;
    x = 2
}

init { run P() }

never C1 {
    do
    :: (x <= 2) -> skip
    od
}

never C2 {
    do
    :: (x >= 0) -> skip
    od
}
EOF

    log_info "Generating product for verification..."
    "$SPIN" -e multi_claims.pml > product.pml 2>&1

    # Create a combined model with the product
    cat > verify_model.pml << 'EOF'
byte x = 0;

proctype P() {
    x = 1;
    x = 2
}

init { run P() }

EOF
    cat product.pml >> verify_model.pml

    log_info "Compiling verifier with product..."
    if "$SPIN" -a verify_model.pml > /dev/null 2>&1; then
        log_info "Product claim compiled successfully"
        if $CC -o pan pan.c 2>/dev/null; then
            log_pass "Generated product is usable for verification"
        else
            log_fail "Product compilation failed"
            return 1
        fi
    else
        log_fail "Product claim verification setup failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Main test runner
# ============================================================
main() {
    echo "========================================"
    echo "Spin Product Generation Tests (pangen7.c)"
    echo "========================================"
    echo "SPIN: $SPIN"
    echo "Work directory: $WORK_DIR"
    echo ""

    if [ ! -x "$SPIN" ]; then
        echo -e "${RED}ERROR${NC}: spin executable not found at $SPIN"
        exit 1
    fi

    # Run all tests
    test_basic_product || true
    test_product_with_accept || true
    test_three_claims || true
    test_strict_intersection || true
    test_product_verbose || true
    test_complex_claims || true
    test_product_verification || true

    cleanup

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
        echo -e "${GREEN}All product generation tests passed!${NC}"
        exit 0
    else
        echo -e "${RED}Some tests failed.${NC}"
        exit 1
    fi
}

main "$@"
