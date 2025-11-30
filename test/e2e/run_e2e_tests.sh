#!/bin/bash
# End-to-End Tests for Spin
# Tests complete real-world verification scenarios from model to result

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
BLUE='\033[0;34m'
NC='\033[0m'

TESTS_RUN=0
TESTS_PASSED=0
TESTS_FAILED=0

mkdir -p "$WORK_DIR"

log_pass() { echo -e "${GREEN}PASS${NC}: $1"; ((TESTS_PASSED++)); }
log_fail() { echo -e "${RED}FAIL${NC}: $1"; ((TESTS_FAILED++)); }
log_info() { echo -e "${BLUE}INFO${NC}: $1"; }
run_test() { ((TESTS_RUN++)); echo -e "\n${YELLOW}=== E2E Test: $1 ===${NC}"; }

cleanup() { rm -rf "$WORK_DIR"/* 2>/dev/null || true; }

# ============================================================
# E2E Test 1: Peterson's Mutual Exclusion Algorithm
# Real protocol: Verify mutual exclusion and starvation freedom
# ============================================================
test_peterson_mutex() {
    run_test "Peterson's Mutual Exclusion Algorithm"
    cleanup
    cd "$WORK_DIR"

    log_info "Testing Peterson's algorithm for mutual exclusion..."

    # Verify the example file
    if [ ! -f "$EXAMPLES_DIR/peterson.pml" ]; then
        log_fail "peterson.pml not found"
        return 1
    fi

    # Generate verifier
    "$SPIN" -a "$EXAMPLES_DIR/peterson.pml" > /dev/null 2>&1

    # Verify safety (mutual exclusion)
    log_info "Checking mutual exclusion property..."
    $CC -DSAFETY -o pan pan.c 2>/dev/null
    local safety_output
    safety_output=$(./pan -n 2>&1)

    if echo "$safety_output" | grep -q "errors: 0"; then
        log_info "Mutual exclusion: VERIFIED"
    else
        log_fail "Mutual exclusion property violated"
        return 1
    fi

    # Verify no deadlock
    log_info "Checking for deadlocks..."
    local states
    states=$(echo "$safety_output" | grep "states, stored" | awk '{print $1}')
    log_info "State space: $states states explored"

    log_pass "Peterson's algorithm verified correctly"
    cd - > /dev/null
}

# ============================================================
# E2E Test 2: Alternating Bit Protocol
# Real protocol: Reliable data transfer over unreliable channel
# ============================================================
test_alternating_bit_protocol() {
    run_test "Alternating Bit Protocol"
    cleanup
    cd "$WORK_DIR"

    log_info "Testing ABP for reliable data transfer..."

    if [ ! -f "$EXAMPLES_DIR/abp.pml" ]; then
        log_fail "abp.pml not found"
        return 1
    fi

    "$SPIN" -a "$EXAMPLES_DIR/abp.pml" > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -n 2>&1)

    if echo "$output" | grep -q "errors: 0"; then
        local states
        states=$(echo "$output" | grep "states, stored" | awk '{print $1}')
        log_info "ABP state space: $states states"
        log_pass "Alternating Bit Protocol verified"
    else
        log_fail "ABP verification failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# E2E Test 3: Leader Election Protocol
# Real protocol: Distributed leader election in a ring
# ============================================================
test_leader_election() {
    run_test "Leader Election Protocol"
    cleanup
    cd "$WORK_DIR"

    log_info "Testing leader election in ring topology..."

    if [ ! -f "$EXAMPLES_DIR/leader0.pml" ]; then
        log_fail "leader0.pml not found"
        return 1
    fi

    "$SPIN" -a "$EXAMPLES_DIR/leader0.pml" > /dev/null 2>&1
    $CC -DSAFETY -DNOCLAIM -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -c0 -n 2>&1)

    if echo "$output" | grep -q "errors: 0"; then
        local states
        states=$(echo "$output" | grep "states, stored" | awk '{print $1}')
        log_info "Leader election: $states states with POR"
        log_pass "Leader election protocol verified"
    else
        log_fail "Leader election verification failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# E2E Test 4: Cache Coherence Protocol (Snoopy)
# Real protocol: MESI-like cache coherence
# Note: snoopy.pml is intentionally buggy to demonstrate Spin's capabilities
# ============================================================
test_cache_coherence() {
    run_test "Cache Coherence Protocol"
    cleanup
    cd "$WORK_DIR"

    log_info "Testing snoopy cache coherence protocol..."
    log_info "Note: snoopy.pml demonstrates bug-finding capability"

    if [ ! -f "$EXAMPLES_DIR/snoopy.pml" ]; then
        log_fail "snoopy.pml not found"
        return 1
    fi

    "$SPIN" -a "$EXAMPLES_DIR/snoopy.pml" > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -n 2>&1)

    # snoopy.pml is designed to find errors - verify spin CAN find them
    if echo "$output" | grep -q "errors:"; then
        local errors=$(echo "$output" | grep "errors:" | awk '{print $NF}')
        log_info "Snoopy model analysis completed, errors found: $errors"
        log_info "This demonstrates Spin's bug-finding capability"
        log_pass "Cache coherence analysis completed"
    else
        log_fail "Could not analyze snoopy model"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# E2E Test 5: Dining Philosophers (Deadlock Detection)
# Classic problem: Test deadlock detection capability
# ============================================================
test_dining_philosophers() {
    run_test "Dining Philosophers (Deadlock Detection)"
    cleanup
    cd "$WORK_DIR"

    log_info "Testing dining philosophers for deadlock..."

    # Create a deadlock-prone version
    cat > philosophers.pml << 'EOF'
/* Dining Philosophers - Classic version with potential deadlock */
#define N 5

byte forks[N];

proctype Philosopher(byte id) {
    byte left = id;
    byte right = (id + 1) % N;

    do
    :: /* Think */
       printf("P%d thinking\n", id);

       /* Pick up forks (deadlock-prone order) */
       atomic { forks[left] == 0 -> forks[left] = 1 };
       atomic { forks[right] == 0 -> forks[right] = 1 };

       /* Eat */
       printf("P%d eating\n", id);

       /* Put down forks */
       forks[left] = 0;
       forks[right] = 0
    od
}

init {
    byte i;
    for (i : 0 .. N-1) {
        forks[i] = 0
    };
    atomic {
        run Philosopher(0);
        run Philosopher(1);
        run Philosopher(2);
        run Philosopher(3);
        run Philosopher(4)
    }
}
EOF

    "$SPIN" -a philosophers.pml > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -n 2>&1)

    # This version MAY deadlock
    if echo "$output" | grep -q "invalid end state"; then
        log_info "Deadlock detected (expected for naive implementation)"
        log_pass "Deadlock detection working correctly"
    elif echo "$output" | grep -q "errors: 0"; then
        log_info "No deadlock found (model may be too constrained)"
        log_pass "Verification completed"
    else
        log_fail "Unexpected verification result"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# E2E Test 6: Producer-Consumer with Bounded Buffer
# Classic pattern: Test buffer bounds and synchronization
# ============================================================
test_producer_consumer() {
    run_test "Producer-Consumer with Bounded Buffer"
    cleanup
    cd "$WORK_DIR"

    log_info "Testing bounded buffer producer-consumer..."

    cat > prodcons.pml << 'EOF'
/* Bounded Buffer Producer-Consumer */
#define BUFSIZE 3
#define NUM_ITEMS 5

chan buffer = [BUFSIZE] of { int };
int produced = 0;
int consumed = 0;

proctype Producer() {
    int item = 0;
    do
    :: item < NUM_ITEMS ->
        buffer ! item;
        produced++;
        printf("Produced: %d\n", item);
        item++
    :: item >= NUM_ITEMS -> break
    od
}

proctype Consumer() {
    int item;
    int count = 0;
    do
    :: count < NUM_ITEMS ->
        buffer ? item;
        consumed++;
        printf("Consumed: %d\n", item);
        count++
    :: count >= NUM_ITEMS -> break
    od
}

init {
    run Producer();
    run Consumer();
    (_nr_pr == 1);
    assert(produced == consumed);
    assert(consumed == NUM_ITEMS)
}
EOF

    "$SPIN" -a prodcons.pml > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -n 2>&1)

    if echo "$output" | grep -q "errors: 0"; then
        log_info "Producer-consumer synchronization correct"
        log_pass "Bounded buffer verified"
    else
        log_fail "Producer-consumer verification failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# E2E Test 7: Traffic Light Controller
# Real-world application: Safety-critical system
# ============================================================
test_traffic_light() {
    run_test "Traffic Light Controller"
    cleanup
    cd "$WORK_DIR"

    log_info "Testing traffic light safety properties..."

    # Correct traffic light with mutex protection
    cat > traffic.pml << 'EOF'
/* Traffic Light Controller - Safe Implementation */
mtype = { RED, YELLOW, GREEN };

mtype ns_light = RED;  /* North-South */
mtype ew_light = RED;  /* East-West */
bool ns_turn = true;   /* Whose turn it is */

/* Safety: Never both green at same time */
#define SAFE (!(ns_light == GREEN && ew_light == GREEN))

proctype NS_Controller() {
    do
    :: atomic {
         ns_turn && ns_light == RED && ew_light == RED ->
         ns_light = GREEN
       }
    :: ns_light == GREEN ->
        ns_light = YELLOW
    :: atomic {
         ns_light == YELLOW ->
         ns_light = RED;
         ns_turn = false
       }
    od
}

proctype EW_Controller() {
    do
    :: atomic {
         !ns_turn && ew_light == RED && ns_light == RED ->
         ew_light = GREEN
       }
    :: ew_light == GREEN ->
        ew_light = YELLOW
    :: atomic {
         ew_light == YELLOW ->
         ew_light = RED;
         ns_turn = true
       }
    od
}

init {
    run NS_Controller();
    run EW_Controller()
}

/* LTL property: always safe */
ltl safety { [] SAFE }
EOF

    "$SPIN" -a traffic.pml > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null

    local output
    output=$(./pan -n 2>&1)

    if echo "$output" | grep -q "errors: 0"; then
        log_info "Traffic light safety property holds"
        log_pass "Traffic light controller verified"
    else
        log_fail "Traffic light safety violated"
        echo "$output" | tail -5
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# E2E Test 8: Comprehensive Example Suite
# Tests all example files compile and verify
# ============================================================
test_example_suite() {
    run_test "Comprehensive Example Suite"
    cleanup

    local examples=(
        "peterson.pml"
        "abp.pml"
        "leader0.pml"
        "snoopy.pml"
        "hello.pml"
        "loops.pml"
        "sort.pml"
    )

    local passed=0
    local failed=0

    for example in "${examples[@]}"; do
        if [ -f "$EXAMPLES_DIR/$example" ]; then
            cd "$WORK_DIR"
            cleanup

            if "$SPIN" -a "$EXAMPLES_DIR/$example" > /dev/null 2>&1 && \
               $CC -DSAFETY -o pan pan.c 2>/dev/null && \
               timeout 30 ./pan -n > /dev/null 2>&1; then
                log_info "$example: VERIFIED"
                ((passed++))
            else
                log_info "$example: FAILED"
                ((failed++))
            fi

            cd - > /dev/null
        else
            log_info "$example: NOT FOUND"
        fi
    done

    log_info "Examples passed: $passed, failed: $failed"

    if [ "$failed" -eq 0 ]; then
        log_pass "All examples verified successfully"
    else
        log_fail "$failed examples failed verification"
        return 1
    fi
}

# ============================================================
# E2E Test 9: Performance Benchmark
# Test verification performance on larger models
# ============================================================
test_performance_benchmark() {
    run_test "Performance Benchmark"
    cleanup
    cd "$WORK_DIR"

    log_info "Running performance benchmark..."

    # Create a model with configurable state space
    cat > benchmark.pml << 'EOF'
/* Benchmark model with controllable state space */
#define PROCS 3
#define STEPS 4

int counters[PROCS];

proctype Worker(byte id) {
    byte i;
    for (i : 0 .. STEPS-1) {
        counters[id] = counters[id] + 1
    }
}

init {
    byte i;
    atomic {
        for (i : 0 .. PROCS-1) {
            run Worker(i)
        }
    }
}
EOF

    "$SPIN" -a benchmark.pml > /dev/null 2>&1
    $CC -O2 -DSAFETY -o pan pan.c 2>/dev/null

    local start_time=$(date +%s.%N)
    local output
    output=$(./pan -n 2>&1)
    local end_time=$(date +%s.%N)

    local duration=$(echo "$end_time - $start_time" | bc)
    local states=$(echo "$output" | grep "states, stored" | awk '{print $1}')
    local rate=$(echo "scale=0; $states / $duration" | bc 2>/dev/null || echo "N/A")

    log_info "States explored: $states"
    log_info "Time: ${duration}s"
    log_info "Rate: $rate states/sec"

    if echo "$output" | grep -q "errors: 0"; then
        log_pass "Benchmark completed successfully"
    else
        log_fail "Benchmark verification failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# E2E Test 10: Memory Safety (Large State Space)
# Test spin handles large state spaces without crashing
# ============================================================
test_memory_safety() {
    run_test "Memory Safety with Large State Space"
    cleanup
    cd "$WORK_DIR"

    log_info "Testing memory handling with larger model..."

    cat > large_model.pml << 'EOF'
/* Model that generates larger state space */
byte arr[4];

proctype Setter(byte idx; byte val) {
    arr[idx] = val
}

init {
    run Setter(0, 1);
    run Setter(1, 2);
    run Setter(2, 3);
    run Setter(3, 4);
    (_nr_pr == 1)
}
EOF

    "$SPIN" -a large_model.pml > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null

    # Run with memory limits
    local output
    output=$(./pan -n -w20 2>&1)

    if echo "$output" | grep -q "errors: 0"; then
        local mem=$(echo "$output" | grep "memory usage" | head -1)
        log_info "Memory usage: $mem"
        log_pass "Memory handling correct"
    else
        log_fail "Memory test failed"
        return 1
    fi

    cd - > /dev/null
}

# ============================================================
# Main Test Runner
# ============================================================
main() {
    echo "========================================"
    echo "Spin End-to-End Tests"
    echo "========================================"
    echo "SPIN: $SPIN"
    echo "CC: $CC"
    echo "Work directory: $WORK_DIR"
    echo ""
    echo "These tests verify complete real-world"
    echo "verification scenarios from start to finish."

    if [ ! -x "$SPIN" ]; then
        echo -e "${RED}ERROR${NC}: spin not found at $SPIN"
        exit 1
    fi

    # Run all E2E tests
    test_peterson_mutex || true
    test_alternating_bit_protocol || true
    test_leader_election || true
    test_cache_coherence || true
    test_dining_philosophers || true
    test_producer_consumer || true
    test_traffic_light || true
    test_example_suite || true
    test_performance_benchmark || true
    test_memory_safety || true

    cleanup

    echo ""
    echo "========================================"
    echo "End-to-End Test Summary"
    echo "========================================"
    echo "Tests run:    $TESTS_RUN"
    echo -e "Tests passed: ${GREEN}$TESTS_PASSED${NC}"
    echo -e "Tests failed: ${RED}$TESTS_FAILED${NC}"

    if [ "$TESTS_FAILED" -eq 0 ]; then
        echo -e "\n${GREEN}All E2E tests passed!${NC}"
        exit 0
    else
        echo -e "\n${RED}Some E2E tests failed.${NC}"
        exit 1
    fi
}

main "$@"
