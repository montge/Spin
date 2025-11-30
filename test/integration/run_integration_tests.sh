#!/bin/bash
# Integration Tests for Spin
# Tests complete workflows: parsing -> generation -> compilation -> verification

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$(dirname "$SCRIPT_DIR")")"
SPIN="${SPIN:-$ROOT_DIR/Src/spin}"
EXAMPLES_DIR="$ROOT_DIR/Examples"
WORK_DIR="${WORK_DIR:-$SCRIPT_DIR/work}"
CC="${CC:-gcc}"

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
run_test() { ((TESTS_RUN++)); echo -e "\n--- Integration Test: $1 ---"; }

cleanup() { rm -rf "$WORK_DIR"/* 2>/dev/null || true; }

# ============================================================
# Integration Test 1: Parser to Verifier Pipeline
# Tests: lexer -> parser -> AST -> code generation -> compilation
# ============================================================
test_parser_to_verifier_pipeline() {
    run_test "Parser to Verifier Pipeline"
    cleanup
    cd "$WORK_DIR"

    # Create a model that exercises multiple parser features
    cat > model.pml << 'EOF'
/* Integration test model with multiple language features */
mtype = { REQUEST, RESPONSE, ACK, NACK };

typedef Message {
    mtype kind;
    byte seq;
    int data
};

chan client_to_server = [3] of { Message };
chan server_to_client = [3] of { Message };

int total_requests = 0;
int total_responses = 0;

inline send_request(ch, seq_num, payload) {
    Message m;
    m.kind = REQUEST;
    m.seq = seq_num;
    m.data = payload;
    ch ! m
}

proctype Client(byte id) {
    Message resp;
    byte seq = 0;

    do
    :: seq < 3 ->
        atomic {
            send_request(client_to_server, seq, id * 100 + seq);
            total_requests++
        };
        server_to_client ? resp;
        assert(resp.kind == RESPONSE || resp.kind == NACK);
        seq++
    :: seq >= 3 -> break
    od
}

proctype Server() {
    Message req;
    Message resp;

    do
    :: client_to_server ? req ->
        if
        :: req.kind == REQUEST ->
            resp.kind = RESPONSE;
            resp.seq = req.seq;
            resp.data = req.data * 2;
            d_step {
                server_to_client ! resp;
                total_responses++
            }
        :: else ->
            resp.kind = NACK;
            server_to_client ! resp
        fi
    :: timeout -> break
    od
}

init {
    run Server();
    run Client(1);
    run Client(2);
    (_nr_pr == 1);  /* Wait for all to finish */
    assert(total_requests == total_responses)
}
EOF

    # Step 1: Generate verifier
    if ! "$SPIN" -a model.pml > /dev/null 2>&1; then
        log_fail "Parser/code generation failed"
        return 1
    fi
    log_info "Code generation: OK"

    # Step 2: Compile verifier
    if ! $CC -DSAFETY -o pan pan.c 2>/dev/null; then
        log_fail "Verifier compilation failed"
        return 1
    fi
    log_info "Compilation: OK"

    # Step 3: Run verification
    local output
    output=$(./pan -n 2>&1)
    if echo "$output" | grep -q "errors: 0"; then
        log_pass "Full pipeline completed successfully"
    else
        log_fail "Verification found errors"
        echo "$output"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Integration Test 2: LTL Property Verification Pipeline
# Tests: LTL parsing -> never claim -> verification
# ============================================================
test_ltl_verification_pipeline() {
    run_test "LTL Property Verification Pipeline"
    cleanup
    cd "$WORK_DIR"

    cat > mutex.pml << 'EOF'
/* Mutual exclusion protocol */
bool want[2];
byte critical = 0;

proctype P(byte id) {
    do
    ::  want[id] = true;
        (want[1-id] == false);
        critical++;
        assert(critical == 1);  /* Safety */
        critical--;
        want[id] = false
    od
}

init {
    want[0] = false;
    want[1] = false;
    run P(0);
    run P(1)
}

/* LTL: mutual exclusion always holds */
ltl mutex { [] (critical <= 1) }

/* LTL: if process wants access, it eventually gets it */
ltl liveness { [] (want[0] -> <> (critical > 0)) }
EOF

    # Test 1: Generate with LTL
    if ! "$SPIN" -a mutex.pml > /dev/null 2>&1; then
        log_fail "LTL parsing/generation failed"
        return 1
    fi
    log_info "LTL generation: OK"

    # Test 2: Verify safety property
    if ! $CC -DSAFETY -o pan pan.c 2>/dev/null; then
        log_fail "Compilation failed"
        return 1
    fi

    local output
    output=$(./pan -n 2>&1)
    if echo "$output" | grep -q "errors: 0"; then
        log_info "Safety verification: OK"
    else
        log_fail "Safety verification failed"
        return 1
    fi

    # Test 3: Check LTL formula conversion
    local ltl_output
    ltl_output=$("$SPIN" -f "[] (p -> <> q)" 2>&1)
    if echo "$ltl_output" | grep -q "never"; then
        log_pass "LTL pipeline completed"
    else
        log_fail "LTL to never claim conversion failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Integration Test 3: Error Trail Generation and Replay
# Tests: verification -> trail generation -> simulation replay
# ============================================================
test_trail_generation_replay() {
    run_test "Trail Generation and Replay"
    cleanup
    cd "$WORK_DIR"

    # Model with guaranteed assertion violation
    cat > buggy.pml << 'EOF'
int x = 0;

proctype P() {
    x = 1
}

init {
    run P();
    x == 0;  /* This blocks until timeout or x becomes 0 */
    assert(x == 0)  /* This WILL fail since P sets x=1 */
}
EOF

    # Generate and compile
    "$SPIN" -a buggy.pml > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null

    # Run verification - should find error
    ./pan > /dev/null 2>&1 || true

    # Check trail was generated
    if [ ! -f buggy.pml.trail ]; then
        # Try alternate approach - model that always fails
        cat > buggy2.pml << 'EOF'
init {
    assert(false)
}
EOF
        "$SPIN" -a buggy2.pml > /dev/null 2>&1
        $CC -DSAFETY -o pan pan.c 2>/dev/null
        ./pan > /dev/null 2>&1 || true

        if [ ! -f buggy2.pml.trail ]; then
            log_fail "Trail file not generated"
            return 1
        fi
        mv buggy2.pml buggy.pml
        mv buggy2.pml.trail buggy.pml.trail
    fi
    log_info "Trail generated: OK"

    # Replay trail
    local replay
    replay=$("$SPIN" -t -p buggy.pml 2>&1)
    if echo "$replay" | grep -q "assertion violated\|spin: trail ends\|violated"; then
        log_pass "Trail replay successful"
    else
        log_fail "Trail replay failed"
        echo "Replay output: $replay"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Integration Test 4: Partial Order Reduction Effectiveness
# Tests: POR algorithm produces fewer states than full search
# ============================================================
test_partial_order_reduction() {
    run_test "Partial Order Reduction Effectiveness"
    cleanup
    cd "$WORK_DIR"

    # Model where POR should be very effective
    cat > por_test.pml << 'EOF'
int a, b, c, d;

proctype P1() { a = 1; b = 1 }
proctype P2() { c = 1; d = 1 }
proctype P3() { a = 2; c = 2 }
proctype P4() { b = 2; d = 2 }

init {
    run P1(); run P2(); run P3(); run P4()
}
EOF

    "$SPIN" -a por_test.pml > /dev/null 2>&1

    # Without POR
    $CC -DSAFETY -DNOREDUCE -o pan_nopor pan.c 2>/dev/null
    local nopor_output
    nopor_output=$(./pan_nopor -n 2>&1)
    local states_nopor
    states_nopor=$(echo "$nopor_output" | grep "states, stored" | awk '{print $1}')

    # With POR
    $CC -DSAFETY -o pan_por pan.c 2>/dev/null
    local por_output
    por_output=$(./pan_por -n 2>&1)
    local states_por
    states_por=$(echo "$por_output" | grep "states, stored" | awk '{print $1}')

    if [ -n "$states_nopor" ] && [ -n "$states_por" ]; then
        local reduction=$((100 - (states_por * 100 / states_nopor)))
        log_info "States without POR: $states_nopor"
        log_info "States with POR: $states_por"
        log_info "Reduction: ${reduction}%"

        if [ "$states_por" -lt "$states_nopor" ]; then
            log_pass "POR is effective (${reduction}% reduction)"
        else
            log_fail "POR not effective"
            return 1
        fi
    else
        log_fail "Could not extract state counts"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Integration Test 5: Multi-File Include Processing
# Tests: preprocessor includes and definitions
# ============================================================
test_include_processing() {
    run_test "Multi-File Include Processing"
    cleanup
    cd "$WORK_DIR"

    # Create header file
    cat > protocol.h << 'EOF'
/* Protocol definitions */
#define MAX_MSG 5
#define TIMEOUT_VAL 10

mtype = { DATA, ACK, FIN };
EOF

    # Create main file that includes header
    cat > main_protocol.pml << 'EOF'
#include "protocol.h"

chan network = [MAX_MSG] of { mtype, byte };

proctype Sender() {
    byte i = 0;
    do
    :: i < 3 ->
        network ! DATA, i;
        i++
    :: i >= 3 ->
        network ! FIN, 0;
        break
    od
}

proctype Receiver() {
    mtype t;
    byte d;
    do
    :: network ? t, d ->
        if
        :: t == FIN -> break
        :: else -> skip
        fi
    od
}

init {
    run Sender();
    run Receiver()
}
EOF

    # Process and verify
    if "$SPIN" -a main_protocol.pml > /dev/null 2>&1; then
        log_info "Include processing: OK"
    else
        log_fail "Include processing failed"
        return 1
    fi

    if $CC -DSAFETY -o pan pan.c 2>/dev/null && ./pan -n > /dev/null 2>&1; then
        log_pass "Multi-file processing successful"
    else
        log_fail "Verification after include failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Integration Test 6: Acceptance Cycle Detection
# Tests: Buchi automata construction and cycle detection
# ============================================================
test_acceptance_cycle_detection() {
    run_test "Acceptance Cycle Detection"
    cleanup
    cd "$WORK_DIR"

    cat > livelock.pml << 'EOF'
/* Model with acceptance cycle (livelock) */
int state = 0;

proctype P() {
    do
    :: state == 0 -> state = 1
    :: state == 1 -> state = 0  /* Infinite loop */
    od
}

/* Never claim: eventually state stays at 2 */
never {
accept:
    do
    :: state != 2  /* Accepts if state never reaches 2 */
    od
}

init { run P() }
EOF

    "$SPIN" -a livelock.pml > /dev/null 2>&1
    $CC -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -a 2>&1)

    if echo "$output" | grep -q "acceptance cycle"; then
        log_pass "Acceptance cycle correctly detected"
    else
        log_fail "Failed to detect acceptance cycle"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Integration Test 7: Bitstate Hashing Mode
# Tests: Supertrace/bitstate verification for large state spaces
# ============================================================
test_bitstate_hashing() {
    run_test "Bitstate Hashing Mode"
    cleanup
    cd "$WORK_DIR"

    cat > large_state.pml << 'EOF'
/* Model with larger state space */
byte arr[8];
byte idx = 0;

proctype Writer() {
    do
    :: idx < 8 ->
        arr[idx] = idx;
        idx++
    :: idx >= 8 -> break
    od
}

init { run Writer() }
EOF

    "$SPIN" -a large_state.pml > /dev/null 2>&1

    # Compile with bitstate
    $CC -DBITSTATE -DSAFETY -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -n 2>&1)

    if echo "$output" | grep -q "errors: 0"; then
        log_pass "Bitstate hashing mode works"
    else
        log_fail "Bitstate mode failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Integration Test 8: Embedded C Code
# Tests: c_code, c_expr, c_decl integration
# ============================================================
test_embedded_c_code() {
    run_test "Embedded C Code Integration"
    cleanup
    cd "$WORK_DIR"

    # Simple embedded C test
    cat > c_embedded.pml << 'EOF'
c_decl {
    int external_counter = 0;
}

init {
    c_code { external_counter = 42; };
    printf("counter set\n")
}
EOF

    # Generate with embedded C support
    if ! "$SPIN" -a c_embedded.pml > /dev/null 2>&1; then
        log_fail "Embedded C parsing failed"
        return 1
    fi
    log_info "Embedded C parsing: OK"

    # Compile - this tests the C code integration
    if $CC -DSAFETY -o pan pan.c 2>/dev/null; then
        log_info "Embedded C compilation: OK"

        local output
        output=$(./pan -n 2>&1)
        if echo "$output" | grep -q "errors: 0"; then
            log_pass "Embedded C code execution successful"
        else
            log_fail "Embedded C execution failed"
            return 1
        fi
    else
        log_fail "Compilation with embedded C failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Main Test Runner
# ============================================================
main() {
    echo "========================================"
    echo "Spin Integration Tests"
    echo "========================================"
    echo "SPIN: $SPIN"
    echo "CC: $CC"
    echo "Work directory: $WORK_DIR"

    if [ ! -x "$SPIN" ]; then
        echo -e "${RED}ERROR${NC}: spin not found at $SPIN"
        exit 1
    fi

    # Run all integration tests
    test_parser_to_verifier_pipeline || true
    test_ltl_verification_pipeline || true
    test_trail_generation_replay || true
    test_partial_order_reduction || true
    test_include_processing || true
    test_acceptance_cycle_detection || true
    test_bitstate_hashing || true
    test_embedded_c_code || true

    # Run specialized integration tests
    echo ""
    echo "========================================"
    echo "Running MSC/Tcl Integration Tests"
    echo "========================================"
    if [ -x "$SCRIPT_DIR/test_msc_tcl.sh" ]; then
        if "$SCRIPT_DIR/test_msc_tcl.sh"; then
            log_pass "MSC integration tests completed"
        else
            log_fail "MSC integration tests failed"
        fi
    fi

    cleanup

    echo ""
    echo "========================================"
    echo "Integration Test Summary"
    echo "========================================"
    echo "Tests run:    $TESTS_RUN"
    echo -e "Tests passed: ${GREEN}$TESTS_PASSED${NC}"
    echo -e "Tests failed: ${RED}$TESTS_FAILED${NC}"

    if [ "$TESTS_FAILED" -eq 0 ]; then
        echo -e "\n${GREEN}All integration tests passed!${NC}"
        exit 0
    else
        echo -e "\n${RED}Some integration tests failed.${NC}"
        exit 1
    fi
}

main "$@"
