# Contributing to Spin

Thank you for your interest in contributing to Spin.

## Getting Started

### Prerequisites

- GCC or Clang compiler
- Yacc or Bison
- Make

### Building

```bash
cd Src
make
```

### Running Tests

```bash
make test
```

### Code Coverage

```bash
make coverage
# Open coverage/html/index.html in a browser
```

## Submitting Changes

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/my-feature`)
3. Make your changes
4. Run tests (`make test`)
5. Commit your changes
6. Push to your fork
7. Open a Pull Request

## Code Style

- Follow existing code style in the codebase
- Use meaningful variable and function names
- Add comments for complex logic
- Keep functions focused and reasonably sized

## Testing

- Add tests for new functionality when possible
- Ensure all existing tests pass before submitting
- Test on multiple platforms if making platform-specific changes

## Reporting Issues

- Use GitHub Issues to report bugs
- Include Spin version (`spin -V`)
- Include operating system and compiler version
- Provide minimal reproducible example if possible

## Security Issues

Please report security vulnerabilities privately. See [SECURITY.md](SECURITY.md) for details.
