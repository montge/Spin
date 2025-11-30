all:
	cd Src; make

install:
	cd Src; make install

clean:
	cd Src; make clean
	rm -rf test/work coverage cppcheck-report.xml

# Run test suite (unit + integration + e2e + functional)
test: all test-unit test-integration test-e2e test-functional

# Functional tests (basic spin functionality)
test-functional: all
	@echo "=== Running Functional Tests ==="
	./test/run_tests.sh

# Unit tests (C function testing)
test-unit:
	@echo "=== Running Unit Tests ==="
	cd test/unit && make test

# Integration tests (workflow testing)
test-integration: all
	@echo "=== Running Integration Tests ==="
	./test/integration/run_integration_tests.sh

# End-to-end tests (real-world scenarios)
test-e2e: all
	@echo "=== Running End-to-End Tests ==="
	./test/e2e/run_e2e_tests.sh

# Quick test (just functional)
test-quick: all
	./test/run_tests.sh

# Build with coverage instrumentation
coverage-build:
	cd Src; make clean
	cd Src; make CFLAGS="-O0 -g --coverage -DNXT -Wall" LDFLAGS="--coverage"

# Run tests and generate coverage report
coverage: coverage-build
	./test/run_tests.sh || true
	mkdir -p coverage
	lcov --capture --directory Src --output-file coverage/coverage.info --ignore-errors source
	lcov --remove coverage/coverage.info '/usr/*' --output-file coverage/coverage.info --ignore-errors unused || true
	genhtml coverage/coverage.info --output-directory coverage/html --ignore-errors source --synthesize-missing
	@echo "Coverage report: coverage/html/index.html"

# Quick coverage summary without HTML report
coverage-summary: coverage-build
	./test/run_tests.sh || true
	gcov -n Src/*.c 2>/dev/null | grep -A 1 "File '"

# Static analysis with cppcheck
cppcheck:
	cppcheck --enable=warning,style,performance,portability \
		--suppress=missingIncludeSystem \
		--suppress=unusedFunction \
		Src/*.c

# Static analysis with cppcheck (verbose XML report)
cppcheck-xml:
	cppcheck --enable=warning,style,performance,portability \
		--suppress=missingIncludeSystem \
		--suppress=unusedFunction \
		--xml --xml-version=2 \
		Src/*.c 2> cppcheck-report.xml
	@echo "Report saved to cppcheck-report.xml"

# Build with strict warnings
strict:
	cd Src; make clean
	cd Src; make CFLAGS="-O2 -DNXT -Wall -Wextra -Wformat=2 -Wformat-security -Wshadow -pedantic"

# Run clang static analyzer
scan-build:
	cd Src; make clean
	cd Src; scan-build make

.PHONY: all install clean test test-unit test-integration test-e2e test-functional test-quick coverage coverage-build coverage-summary cppcheck cppcheck-xml strict scan-build
