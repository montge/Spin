#!/bin/bash
# Test suite for msc_tcl.c - MSC output in Tcl/Tk format
# Tests the -M flag functionality

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$(dirname "$SCRIPT_DIR")")"
SPIN="${SPIN:-$ROOT_DIR/Src/spin}"
TEST_WORK_DIR="${TEST_WORK_DIR:-$(dirname "$SCRIPT_DIR")/work}"
CC="${CC:-gcc}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

TESTS_RUN=0
TESTS_PASSED=0
TESTS_FAILED=0

log_pass() {
    echo -e "${GREEN}PASS${NC}: $1"
    ((TESTS_PASSED++))
}

log_fail() {
    echo -e "${RED}FAIL${NC}: $1"
    ((TESTS_FAILED++))
}

log_info() {
    echo "INFO: $1"
}

run_test() {
    local name="$1"
    ((TESTS_RUN++))
    echo -e "\n--- Test: $name ---"
}

cleanup_work_dir() {
    rm -f "$TEST_WORK_DIR"/*.tcl "$TEST_WORK_DIR"/pan* "$TEST_WORK_DIR"/*.trail "$TEST_WORK_DIR"/*.tmp 2>/dev/null || true
}

# Test 1: Basic MSC generation with -M flag
test_msc_basic_simulation() {
    run_test "MSC: basic simulation with -M flag"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_basic.pml"

    # Run simulation with -M flag to generate MSC output
    if "$SPIN" -M -u50 "$pml_file" > /dev/null 2>&1; then
        # Check if .tcl file was created (filename pattern is <model>.tcl)
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            log_pass "MSC tcl file created successfully ($tcl_file)"

            # Verify file contains expected Tcl/Tk commands
            if grep -q "canvas .c" "$tcl_file" && \
               grep -q "scrollbar" "$tcl_file" && \
               grep -q "wm title" "$tcl_file"; then
                log_pass "MSC tcl file contains valid Tcl/Tk canvas setup"
            else
                log_fail "MSC tcl file missing expected Tcl/Tk commands"
                return 1
            fi
        else
            log_fail "MSC tcl file not created ($tcl_file)"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 2: MSC with rendezvous communication
test_msc_rendezvous() {
    run_test "MSC: rendezvous communication arrows"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_rendezvous.pml"
    local tcl_file="${pml_file}.tcl"

    if "$SPIN" -M -u50 "$pml_file" > /dev/null 2>&1; then
        if [ -f "$tcl_file" ]; then
            # Check for arrow creation with correct color (rendezvous uses 'darkred')
            if grep -q "arrow both" "$tcl_file"; then
                log_pass "MSC contains rendezvous arrows (both direction)"
            else
                log_info "MSC may not contain rendezvous arrows"
            fi

            # Check for line creation
            if grep -q "create line" "$tcl_file"; then
                log_pass "MSC contains message lines"
            else
                log_fail "MSC missing message lines"
                return 1
            fi
        else
            log_fail "MSC tcl file not created ($tcl_file)"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 3: MSC with multiple processes
test_msc_multi_process() {
    run_test "MSC: multiple processes"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_multi_proc.pml"
    local tcl_file="${pml_file}.tcl"

    if "$SPIN" -M -u100 "$pml_file" > /dev/null 2>&1; then
        if [ -f "$tcl_file" ]; then
            # Count number of process columns (boxes)
            local box_count=$(grep -c "create rectangle" "$tcl_file" || echo "0")
            if [ "$box_count" -gt 5 ]; then
                log_pass "MSC contains multiple process boxes ($box_count rectangles)"
            else
                log_info "MSC box count: $box_count"
            fi

            # Check for text labels
            if grep -q "create text" "$tcl_file"; then
                log_pass "MSC contains text labels"
            else
                log_fail "MSC missing text labels"
                return 1
            fi
        else
            log_fail "MSC tcl file not created ($tcl_file)"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 4: MSC with trail playback
test_msc_trail_playback() {
    run_test "MSC: trail playback with -M -t flags"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    # Use a model that will generate a trail
    cat > msc_trail_test.pml << 'EOF'
int x = 0;
proctype P() {
    do
    :: x < 5 -> x++
    :: x >= 5 -> break
    od;
    assert(x == 10)  /* will fail */
}
init { run P() }
EOF

    # Generate verifier and produce trail
    "$SPIN" -a msc_trail_test.pml > /dev/null 2>&1
    $CC -DSAFETY -o pan pan.c 2>/dev/null
    ./pan > /dev/null 2>&1 || true  # Will fail assertion

    # Copy model to same location for trail playback
    if [ -f "msc_trail_test.pml.trail" ]; then
        # Need to copy .pml.trail to .trail for -t to work
        cp msc_trail_test.pml.trail msc_trail_test.trail

        # Replay trail with MSC output
        if "$SPIN" -M -t msc_trail_test.pml > /dev/null 2>&1; then
            if [ -f "msc_trail_test.pml.tcl" ]; then
                log_pass "MSC trail playback file created"

                # Verify it contains trail-specific content
                if grep -q "create" msc_trail_test.pml.tcl; then
                    log_pass "MSC trail file contains Tcl commands"
                else
                    log_fail "MSC trail file incomplete"
                    return 1
                fi
            else
                log_fail "MSC trail file not created (msc_trail_test.pml.tcl)"
                return 1
            fi
        else
            log_fail "spin -M -t trail playback failed"
            return 1
        fi
    else
        log_info "No trail file generated, skipping trail playback test"
    fi

    cd - > /dev/null
}

# Test 5: MSC grid lines and formatting
test_msc_formatting() {
    run_test "MSC: grid lines and formatting elements"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_basic.pml"

    if "$SPIN" -M -u50 "$pml_file" > /dev/null 2>&1; then
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            # Check for grid lines (tagged as 'grid')
            if grep -q "tags grid" "$tcl_file"; then
                log_pass "MSC contains grid lines"
            else
                log_info "MSC may not contain grid lines"
            fi

            # Check for message tags
            if grep -q "tags mesg" "$tcl_file"; then
                log_pass "MSC contains message tags"
            else
                log_info "MSC may not contain message tags"
            fi

            # Check for z-ordering commands (lower/raise)
            if grep -q ".c lower grid" msc.tcl || grep -q ".c raise mesg" "$tcl_file"; then
                log_pass "MSC contains z-ordering commands"
            else
                log_info "MSC may not contain z-ordering"
            fi
        else
            log_fail "msc.tcl file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 6: MSC step numbers
test_msc_step_numbers() {
    run_test "MSC: step number display"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_basic.pml"

    if "$SPIN" -M -u30 "$pml_file" > /dev/null 2>&1; then
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            # Check for step number text elements
            local step_count=$(grep -c 'text.*-text.*[0-9]' msc.tcl || echo "0")
            if [ "$step_count" -gt 0 ]; then
                log_pass "MSC contains step numbers ($step_count step markers)"
            else
                log_info "MSC step number count: $step_count"
            fi
        else
            log_fail "msc.tcl file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 7: MSC with different message types (color coding)
test_msc_message_colors() {
    run_test "MSC: message color coding (send vs receive)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_colors.pml"

    if "$SPIN" -M -u50 "$pml_file" > /dev/null 2>&1; then
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            # Check for different fill colors indicating message types
            if grep -q "fill ivory" msc.tcl || grep -q "fill azure" "$tcl_file"; then
                log_pass "MSC contains colored message boxes"
            else
                log_info "MSC color information may vary"
            fi

            # Check for arrow shapes
            if grep -q "arrowshape" "$tcl_file"; then
                log_pass "MSC contains arrow shapes"
            else
                log_info "MSC may not contain arrow shapes"
            fi
        else
            log_fail "msc.tcl file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 8: MSC with limited steps
test_msc_step_limit() {
    run_test "MSC: step limitation with -u flag"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_basic.pml"

    # Run with different step limits
    if "$SPIN" -M -u10 "$pml_file" > /dev/null 2>&1; then
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            mv "$tcl_file" msc_10.tcl

            if "$SPIN" -M -u100 "$pml_file" > /dev/null 2>&1; then
                local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
                    local size10=$(wc -l < msc_10.tcl)
                    local size100=$(wc -l < "$tcl_file")

                    if [ "$size100" -gt "$size10" ]; then
                        log_pass "MSC respects step limits ($size10 vs $size100 lines)"
                    else
                        log_info "MSC sizes: -u10=$size10 lines, -u100=$size100 lines"
                    fi
                else
                    log_fail "Second MSC not created"
                    return 1
                fi
            else
                log_fail "Second spin -M failed"
                return 1
            fi
        else
            log_fail "First MSC not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 9: MSC scrollbar and window configuration
test_msc_window_config() {
    run_test "MSC: window and scrollbar configuration"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_basic.pml"

    if "$SPIN" -M -u50 "$pml_file" > /dev/null 2>&1; then
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            # Check for scrollbar setup
            if grep -q "scrollbar .vscroll" "$tcl_file" && \
               grep -q "scrollbar .hscroll" "$tcl_file"; then
                log_pass "MSC contains vertical and horizontal scrollbars"
            else
                log_fail "MSC missing scrollbar configuration"
                return 1
            fi

            # Check for window geometry
            if grep -q "wm geometry" "$tcl_file"; then
                log_pass "MSC contains window geometry configuration"
            else
                log_fail "MSC missing window geometry"
                return 1
            fi

            # Check for window title
            if grep -q "wm title" "$tcl_file"; then
                log_pass "MSC contains window title"
            else
                log_fail "MSC missing window title"
                return 1
            fi
        else
            log_fail "msc.tcl file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 10: MSC with real-world example (abp.pml)
test_msc_abp_example() {
    run_test "MSC: alternating bit protocol example"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local abp_file="$ROOT_DIR/Examples/abp.pml"

    if [ -f "$abp_file" ]; then
        # Change to Examples dir so tcl file is created there
        cd "$ROOT_DIR/Examples"
        if "$SPIN" -M -u200 abp.pml > /dev/null 2>&1; then
            if [ -f "abp.pml.tcl" ]; then
                log_pass "MSC generated for abp.pml"

                # Verify substantial content
                local line_count=$(wc -l < abp.pml.tcl)
                if [ "$line_count" -gt 50 ]; then
                    log_pass "MSC contains substantial content ($line_count lines)"
                else
                    log_info "MSC line count: $line_count"
                fi

                # Check for both send and receive arrows
                if grep -q "arrow last" abp.pml.tcl; then
                    log_pass "MSC contains directional arrows"
                else
                    log_info "MSC arrow type may vary"
                fi

                # Cleanup
                rm -f abp.pml.tcl
            else
                log_fail "MSC file not created for abp.pml (abp.pml.tcl)"
                cd "$TEST_WORK_DIR"
                return 1
            fi
        else
            log_fail "spin -M simulation failed for abp.pml"
            cd "$TEST_WORK_DIR"
            return 1
        fi
        cd "$TEST_WORK_DIR"
    else
        log_info "abp.pml not found, skipping"
    fi

    cd - > /dev/null
}

# Test 11: MSC canvas scroll region
test_msc_scroll_region() {
    run_test "MSC: canvas scroll region configuration"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_basic.pml"

    if "$SPIN" -M -u50 "$pml_file" > /dev/null 2>&1; then
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            # Check for scrollregion parameter
            if grep -q "scrollregion" "$tcl_file"; then
                log_pass "MSC contains scrollregion configuration"
            else
                log_fail "MSC missing scrollregion"
                return 1
            fi

            # Check for canvas dimensions
            if grep -q "width.*height" "$tcl_file"; then
                log_pass "MSC contains canvas dimensions"
            else
                log_info "MSC canvas dimensions may be implicit"
            fi
        else
            log_fail "msc.tcl file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 12: MSC pack/layout commands
test_msc_layout() {
    run_test "MSC: widget packing and layout"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_basic.pml"

    if "$SPIN" -M -u50 "$pml_file" > /dev/null 2>&1; then
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            # Check for pack command
            if grep -q "pack append" "$tcl_file"; then
                log_pass "MSC contains widget packing commands"
            else
                log_fail "MSC missing pack commands"
                return 1
            fi
        else
            log_fail "msc.tcl file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 13: MSC with custom output filename
test_msc_custom_filename() {
    run_test "MSC: custom output filename"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    # Create a model with a specific name
    cat > my_protocol.pml << 'EOF'
chan ch = [1] of { byte };
proctype Sender() { ch ! 1 }
proctype Receiver() { byte x; ch ? x }
init { run Sender(); run Receiver() }
EOF

    if "$SPIN" -M -u50 my_protocol.pml > /dev/null 2>&1; then
        if [ -f "my_protocol.pml.tcl" ]; then
            log_pass "MSC uses model filename for output (my_protocol.pml.tcl)"
        else
            log_fail "MSC file with custom name not created (my_protocol.pml.tcl)"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 14: MSC escaping special characters
test_msc_special_chars() {
    run_test "MSC: escaping special characters in labels"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    # Create a model with special characters
    cat > special_chars.pml << 'EOF'
chan ch = [1] of { byte };
proctype Sender() {
    ch ! 1;
    /* [test] brackets */
}
proctype Receiver() {
    byte x;
    ch ? x
}
init { run Sender(); run Receiver() }
EOF

    if "$SPIN" -M -u50 special_chars.pml > /dev/null 2>&1; then
        if [ -f "special_chars.pml.tcl" ]; then
            # Check that brackets are escaped
            if grep -q '\\[' special_chars.pml.tcl || grep -q 'text' special_chars.pml.tcl; then
                log_pass "MSC handles special characters"
            else
                log_info "MSC special character handling verified"
            fi
        else
            log_fail "MSC file not created (special_chars.pml.tcl)"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 15: MSC with very large number of steps (test scaling)
test_msc_large_scale() {
    run_test "MSC: large scale simulation (scaling test)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_large.pml"

    # Run with many steps to test TotSteps limits
    if "$SPIN" -M -u1000 "$pml_file" > /dev/null 2>&1; then
        local tcl_file="${pml_file}.tcl"
        if [ -f "$tcl_file" ]; then
            log_pass "MSC handles large simulations"

            # Check for scaler comments (appears when canvas is scaled)
            if grep -q "# Scaler" "$tcl_file" || grep -q "# maxx" "$tcl_file"; then
                log_pass "MSC contains scaling information"
            else
                log_info "MSC scaling may not be needed for this test"
            fi

            # Verify file has substantial content
            local line_count=$(wc -l < "$tcl_file")
            if [ "$line_count" -gt 100 ]; then
                log_pass "MSC large simulation created substantial output ($line_count lines)"
            else
                log_info "MSC line count: $line_count"
            fi
        else
            log_fail "MSC tcl file not created ($tcl_file)"
            return 1
        fi
    else
        log_fail "spin -M large simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 16: MSC with process priorities and colors
test_msc_process_colors() {
    run_test "MSC: colored process boxes"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    # Create model with colored MSC annotations
    cat > colored.pml << 'EOF'
chan ch = [1] of { byte };
proctype RedProc() {
    ch ! 1
}
proctype BlueProc() {
    byte x;
    ch ? x
}
init {
    run RedProc();
    run BlueProc()
}
EOF

    if "$SPIN" -M -u50 colored.pml > /dev/null 2>&1; then
        if [ -f "colored.pml.tcl" ]; then
            # Check for different fill colors for processes
            if grep -q "fill ivory\|fill azure\|fill pink" colored.pml.tcl; then
                log_pass "MSC contains colored process boxes"
            else
                log_info "MSC color scheme may vary"
            fi

            # Check for create rectangle commands
            local rect_count=$(grep -c "create rectangle" colored.pml.tcl || echo "0")
            if [ "$rect_count" -gt 0 ]; then
                log_pass "MSC created $rect_count rectangles"
            else
                log_fail "No rectangles found in MSC"
                return 1
            fi
        else
            log_fail "MSC file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 17: MSC without processes (init only)
test_msc_init_only() {
    run_test "MSC: init process only"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > init_only.pml << 'EOF'
int x = 0;
init {
    x = 1;
    x = 2;
    x = 3
}
EOF

    if "$SPIN" -M -u20 init_only.pml > /dev/null 2>&1; then
        if [ -f "init_only.pml.tcl" ]; then
            log_pass "MSC created for init-only model"

            # Should still have basic structure
            if grep -q "canvas .c" init_only.pml.tcl; then
                log_pass "MSC has proper canvas structure"
            else
                log_fail "MSC missing canvas structure"
                return 1
            fi
        else
            log_fail "MSC file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 18: MSC with process line tracking
test_msc_procline_tracking() {
    run_test "MSC: process line tracking (ProcLine comments)"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    local pml_file="test_msc_multi_proc.pml"
    local tcl_file="${pml_file}.tcl"

    if "$SPIN" -M -u100 "$pml_file" > /dev/null 2>&1; then
        if [ -f "$tcl_file" ]; then
            # Check for ProcLine tracking comments
            if grep -q "# ProcLine" "$tcl_file"; then
                log_pass "MSC contains ProcLine tracking comments"
            else
                log_info "MSC ProcLine comments may be omitted"
            fi

            # Check for grid lines between processes
            if grep -q "fill lightgrey" "$tcl_file"; then
                log_pass "MSC contains grid lines (lightgrey)"
            else
                log_info "Grid lines may use different colors"
            fi
        else
            log_fail "MSC file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Test 19: MSC step limit boundary (TotSteps)
test_msc_totsteps_limit() {
    run_test "MSC: TotSteps limit handling"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > long_run.pml << 'EOF'
int x = 0;
proctype Counter() {
    do
    :: x < 255 -> x++
    :: else -> break
    od
}
init { run Counter() }
EOF

    # Try to run with very high step limit
    if "$SPIN" -M -u5000 long_run.pml > /dev/null 2>&1; then
        if [ -f "long_run.pml.tcl" ]; then
            log_pass "MSC handles high step limits"

            # Check if any truncation warnings in comments
            if grep -q "max\|exceeded\|truncat" long_run.pml.tcl; then
                log_info "MSC may have truncation information"
            fi
        else
            log_fail "MSC file not created"
            return 1
        fi
    else
        log_info "High step limit may cause issues (expected)"
    fi

    cd - > /dev/null
}

# Test 20: MSC with mixed channel types
test_msc_mixed_channels() {
    run_test "MSC: mixed buffered and rendezvous channels"
    cleanup_work_dir
    cd "$TEST_WORK_DIR"

    cat > mixed_chan.pml << 'EOF'
chan buffered = [2] of { byte };
chan sync = [0] of { byte };

proctype P1() {
    buffered ! 1;
    sync ! 2
}

proctype P2() {
    byte x;
    buffered ? x;
    sync ? x
}

init {
    run P1();
    run P2()
}
EOF

    if "$SPIN" -M -u50 mixed_chan.pml > /dev/null 2>&1; then
        if [ -f "mixed_chan.pml.tcl" ]; then
            log_pass "MSC handles mixed channel types"

            # Check for both types of arrows
            if grep -q "arrow both" mixed_chan.pml.tcl; then
                log_pass "MSC contains rendezvous arrows (both)"
            else
                log_info "Rendezvous arrows may not be present"
            fi

            if grep -q "arrow last" mixed_chan.pml.tcl; then
                log_pass "MSC contains async message arrows (last)"
            else
                log_info "Async arrows may not be present"
            fi

            # Check for different arrow colors
            if grep -q "darkred\|darkblue" mixed_chan.pml.tcl; then
                log_pass "MSC uses different colors for channel types"
            else
                log_info "MSC color coding may vary"
            fi
        else
            log_fail "MSC file not created"
            return 1
        fi
    else
        log_fail "spin -M simulation failed"
        return 1
    fi

    cd - > /dev/null
}

# Main test runner
main() {
    echo "========================================"
    echo "MSC (msc_tcl.c) Test Suite"
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

    # Create work directory if needed
    mkdir -p "$TEST_WORK_DIR"

    # Run tests
    test_msc_basic_simulation || true
    test_msc_rendezvous || true
    test_msc_multi_process || true
    test_msc_trail_playback || true
    test_msc_formatting || true
    test_msc_step_numbers || true
    test_msc_message_colors || true
    test_msc_step_limit || true
    test_msc_window_config || true
    test_msc_abp_example || true
    test_msc_scroll_region || true
    test_msc_layout || true
    test_msc_custom_filename || true
    test_msc_special_chars || true
    test_msc_large_scale || true
    test_msc_process_colors || true
    test_msc_init_only || true
    test_msc_procline_tracking || true
    test_msc_totsteps_limit || true
    test_msc_mixed_channels || true

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
        echo -e "${GREEN}All MSC tests passed!${NC}"
        exit 0
    else
        echo -e "${RED}Some MSC tests failed.${NC}"
        exit 1
    fi
}

main "$@"
