# Selected packed static guidance model

Status: **SELECTED DESIGN / NO KOTLIN IMPLEMENTATION**.

Run `python3 spec/lean/proposals/packed-static-guidance-20261103/check.py`.
The checker uses Lean 4.33.1, one CPU, and at most 768 MiB for Lean.

Read the [implementation design](../../../../docs/design/bidirectional-packed-static-guidance-design-20261103.md)
and [proof report](REPORT.md). `PackedStaticGuidance.lean` is a standalone
constructive finite model. The current native query/index adapter is the
reference, not kernel-verified code.

The model compiles a complete ordered normalized row stream into an executable
geometry table and primitive references. It proves lossless decode, full
owner/port retention, arbitrary ordered query/early-stop equality, and every
finite composition prefix using the same oracle. It proves radix pair encoding
and a metadata/reference allocation-unit bound. It does not model JVM bytes,
GC release, AP algebra or project convergence.

`checks.json` and `audit.txt` are generated portable receipts. Do not register
this design as proof of a Kotlin implementation. No analyzer, Gradle, JFR, MAT
or project measurement is run by the checker.
