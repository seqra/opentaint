Before anything else, confirm `opentaint` is on PATH (`command -v opentaint` / `opentaint --version`). If it's missing, don't proceed silently — tell the user and ask to install it, offering the command for their platform; run an install only on explicit confirmation:

macOS / Linux — try in order:

1. Homebrew — `brew install --cask seqra/tap/opentaint`
2. npm — `npm install -g @seqra/opentaint`
3. shell script — `curl -fsSL https://opentaint.org/install.sh | bash`

Windows — try in order:

1. npm — `npm install -g @seqra/opentaint`
2. PowerShell script — `irm https://opentaint.org/install.ps1 | iex`

After installing, run `opentaint health` to confirm the autobuilder/analyzer/rules/runtime resolve.
