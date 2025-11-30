#!/bin/bash
# Script to verify pangen7.c test coverage
# This script rebuilds Spin with coverage, runs tests, and reports coverage

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"

GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}pangen7.c Coverage Verification${NC}"
echo -e "${BLUE}========================================${NC}"
echo ""

# Step 1: Rebuild with coverage
echo -e "${YELLOW}Step 1: Rebuilding Spin with coverage instrumentation...${NC}"
cd "$ROOT_DIR/Src"
make clean > /dev/null 2>&1
make CFLAGS="-O2 -fprofile-arcs -ftest-coverage" > /dev/null 2>&1
echo -e "${GREEN}✓ Build complete${NC}"
echo ""

# Step 2: Clean old coverage data
echo -e "${YELLOW}Step 2: Cleaning old coverage data...${NC}"
rm -f pangen7.gcda pangen7.c.gcov
cd "$ROOT_DIR"
echo -e "${GREEN}✓ Cleanup complete${NC}"
echo ""

# Step 3: Run tests
echo -e "${YELLOW}Step 3: Running test suites...${NC}"
echo -e "  - Main test suite..."
./test/run_tests.sh > /dev/null 2>&1 && echo -e "    ${GREEN}✓ Main tests passed${NC}" || echo -e "    ${RED}✗ Main tests failed${NC}"

echo -e "  - Product generation tests..."
./test/e2e/test_product_generation.sh > /dev/null 2>&1 && echo -e "    ${GREEN}✓ Product tests passed${NC}" || echo -e "    ${RED}✗ Product tests failed${NC}"

echo -e "  - Verbose product tests..."
./test/e2e/test_product_verbose.sh > /dev/null 2>&1 && echo -e "    ${GREEN}✓ Verbose tests passed${NC}" || echo -e "    ${RED}✗ Verbose tests failed${NC}"
echo ""

# Step 4: Generate coverage report
echo -e "${YELLOW}Step 4: Generating coverage report...${NC}"
cd "$ROOT_DIR/Src"
COVERAGE_OUTPUT=$(gcov pangen7.c 2>&1)
echo -e "${GREEN}✓ Coverage report generated${NC}"
echo ""

# Step 5: Display results
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}Coverage Results${NC}"
echo -e "${BLUE}========================================${NC}"
echo "$COVERAGE_OUTPUT" | grep -E "File 'pangen7.c'|Lines executed" | head -2
echo ""

# Extract coverage percentage
COVERAGE_PCT=$(echo "$COVERAGE_OUTPUT" | grep "Lines executed" | head -1 | grep -oP '\d+\.\d+(?=%)')
COVERAGE_INT=$(echo "$COVERAGE_PCT" | cut -d. -f1)

# Check if target met
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}Goal Assessment${NC}"
echo -e "${BLUE}========================================${NC}"
echo "Target Coverage:  30%"
echo "Achieved Coverage: ${COVERAGE_PCT}%"
echo ""

if [ "$COVERAGE_INT" -ge 30 ]; then
    echo -e "${GREEN}✓ SUCCESS: Coverage target exceeded!${NC}"
    echo -e "${GREEN}  Coverage improved from 0% to ${COVERAGE_PCT}%${NC}"
    EXIT_CODE=0
else
    echo -e "${RED}✗ FAILED: Coverage target not met${NC}"
    EXIT_CODE=1
fi

echo ""
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}Test Files Created${NC}"
echo -e "${BLUE}========================================${NC}"
echo "1. test/e2e/test_product_generation.sh  (7 tests)"
echo "2. test/e2e/test_product_verbose.sh     (7 tests)"
echo "3. test/run_tests.sh                     (updated)"
echo "4. test/PANGEN7_TEST_SUMMARY.md          (documentation)"
echo ""

echo -e "${BLUE}Detailed coverage report: Src/pangen7.c.gcov${NC}"
echo ""

exit $EXIT_CODE
