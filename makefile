all:
	cd Src; make

install:
	cd Src; make install

clean:
	cd Src; make clean
	rm -rf test/work coverage

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
	genhtml coverage/coverage.info --output-directory coverage/html --ignore-errors source
	@echo "Coverage report: coverage/html/index.html"

# Quick coverage summary without HTML report
coverage-summary: coverage-build
	./test/run_tests.sh || true
	gcov -n Src/*.c 2>/dev/null | grep -A 1 "File '"

.PHONY: all install clean test coverage coverage-build coverage-summary
