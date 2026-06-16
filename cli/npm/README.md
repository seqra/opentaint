<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/seqra/opentaint/main/logos/opentaint-logo-dark.svg">
    <source media="(prefers-color-scheme: light)" srcset="https://raw.githubusercontent.com/seqra/opentaint/main/logos/opentaint-logo-light.svg">
    <img src="https://raw.githubusercontent.com/seqra/opentaint/main/logos/opentaint-logo-light.svg" alt="OpenTaint" height="100">
  </picture>
</p>

<h3 align="center">The open source taint analysis engine for the AI era</h3>

<p align="center">
  Formal taint analysis for application security — finds what AST-pattern matchers miss, lets LLM agents enact vulnerabilities as rules, and scales where neither can alone.
</p>

<p align="center">
  <a href="https://www.npmjs.com/package/@seqra/opentaint"><img src="https://img.shields.io/npm/v/@seqra/opentaint.svg" alt="npm version"></a>
  <a href="https://github.com/seqra/opentaint/blob/main/LICENSE.md"><img src="https://img.shields.io/badge/License-Apache%202.0-blue.svg" alt="License: Apache 2.0"></a>
  <a href="https://discord.gg/6BXDfbP4p9"><img src="https://img.shields.io/discord/1403357427176575036?logo=discord&label=Discord" alt="Discord"></a>
</p>

<p align="center">
  <a href="https://github.com/seqra/opentaint">
    <picture>
      <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/seqra/opentaint/main/public/opentaint-demo-light.gif">
      <source media="(prefers-color-scheme: light)" srcset="https://raw.githubusercontent.com/seqra/opentaint/main/public/opentaint-demo-dark.gif">
      <img src="https://raw.githubusercontent.com/seqra/opentaint/main/public/opentaint-demo-dark.gif" alt="OpenTaint taint analysis demo">
    </picture>
  </a>
</p>

---

This package is the npm distribution of the OpenTaint CLI. Installing it pulls in
a prebuilt, self-contained binary for your platform that bundles the analyzer,
rules, and a Java runtime — no separate Java installation required.

## Install

Run instantly with `npx` — no install required:

```bash
npx @seqra/opentaint scan
```

Or install globally:

```bash
npm install -g @seqra/opentaint
opentaint --version
```

The correct binary for your platform is selected automatically through optional
dependencies. Supported platforms:

| OS      | Architectures |
| ------- | ------------- |
| Linux   | x64, arm64    |
| macOS   | x64, arm64    |
| Windows | x64, arm64    |

> **Note:** Do not install with `--no-optional` / `--omit=optional`. The
> platform binary ships as an optional dependency; omitting it leaves the
> launcher with nothing to run.

## Usage

Scan the project in the current directory:

```bash
opentaint scan
```

Write results to a SARIF file:

```bash
opentaint scan --output results.sarif
```

See all commands and flags:

```bash
opentaint --help
```

## AI agent workflows

OpenTaint ships agent skills that turn static analysis into an end-to-end
application-security workflow. Add them to your agent with:

```bash
npx skills add https://github.com/seqra/opentaint
```

The `appsec-agent` skill orchestrates a full assessment: build the project, run
OpenTaint, discover the attack surface, add targeted rules, model missing library
data flows, triage findings, and optionally generate dynamic proof-of-concept
checks for confirmed vulnerabilities.

## Updating

```bash
npm install -g @seqra/opentaint@latest
```

## Documentation & support

- **Documentation:** https://github.com/seqra/opentaint/blob/main/docs/README.md
- **Issues:** https://github.com/seqra/opentaint/issues
- **Community:** [Discord](https://discord.gg/6BXDfbP4p9)
- **Email:** [seqradev@gmail.com](mailto:seqradev@gmail.com)

## License

The CLI is released under the [MIT License](https://github.com/seqra/opentaint/blob/main/cli/LICENSE).
The core analysis engine is released under the
[Apache 2.0 License](https://github.com/seqra/opentaint/blob/main/LICENSE.md).
