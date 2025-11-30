all:
	cd Src; make

install:
	cd Src; make install

clean:
	cd Src; make clean
	rm -rf test/work coverage cppcheck-report.xml

# Run test suite
test: all
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

.PHONY: all install clean test coverage coverage-build coverage-summary cppcheck cppcheck-xml strict scan-build
