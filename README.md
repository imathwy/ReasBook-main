# ReasBook — Lean/mathlib v4.29.0

**Toolchain:** `leanprover/lean4:v4.29.0`
**Mathlib:** v4.29.0
**Status:** Klenke probability theory formalization included
**Last build:** `lake build Books` passes with Lean 4.29.0 and mathlib v4.29.0

This branch contains the formalization of Achim Klenke's *Probability Theory: A
Comprehensive Course* (3rd ed., 2020). The canonical source tree is
`ReasBook/Books/ProbabilityTheory_Klenke_2020/Items/`; legacy chapter compatibility
directories and temporary proof files are not included.

## Build

```bash
cd ReasBook
lake update
lake build Books
```

Full Lean build and web build run on the self-hosted runner; locally, `./build.sh` / `./build-web.sh`
replicate the same phases (see `scripts/`).
