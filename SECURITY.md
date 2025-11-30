# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 6.5.x   | :white_check_mark: |
| < 6.5   | :x:                |

## Reporting a Vulnerability

If you discover a security vulnerability in Spin, please report it responsibly:

1. **Do not** open a public GitHub issue for security vulnerabilities
2. Email the maintainers directly with:
   - Description of the vulnerability
   - Steps to reproduce
   - Potential impact
   - Any suggested fixes (optional)

## Known Security Considerations

Spin is a model checking tool that:
- Parses user-provided ProMeLa specifications
- Generates C code that users compile and run
- May execute system commands for preprocessing

When using Spin:
- Only run Spin on trusted input files
- Review generated verifier code before compilation
- Be cautious with specifications from untrusted sources

## Security Updates

Security fixes will be released as patch versions. Check the [releases](https://github.com/montge/Spin/releases) page for updates.
