# Security

leanzempic generates code, and its runtime uses `unsafeCoerce` and mutable buffers by design.

## What to expect

* The generated Haskell trusts the compiler: values moved through `Any` are not checked. The
  runtime is written to be correct for the code the backend emits, not to defend against arbitrary
  input.
* Arrays and strings are not thread safe.
* A bug in the ownership analysis (see `SOUNDNESS.md`) could produce a wrong result, silently. That is
  a correctness bug that a security-sensitive program must treat seriously; run with
  `set_option zempic.own false` if you need to rule it out.
* Do not use this to compile Lean code you would not otherwise trust: it runs Lean's elaborator at
  compile time, like any Lean project.

## Reporting a vulnerability

Please do not open a public issue for a suspected vulnerability. Email keith.adler@icloud.com, or use
GitHub's private vulnerability reporting for this repository. Expect an acknowledgement within a
few days; this is a single-maintainer project.

## Supported versions

Pre-release: only the latest commit on `main`.
