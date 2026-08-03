# Optimization Theory and Methods: Nonlinear Programming (Sun--Yuan, 2006)

Lean 4 formalization of Wenyu Sun and Ya-xiang Yuan's *Optimization Theory and Methods: Nonlinear Programming*.

- Contributor: `imathwy`
- Upstream base: `optpku/ReasBook@11a65a5` (branch `v4.30.0`)
- Lean/mathlib: `v4.30.0` / `v4.30.0`
- Main module: `OptimizationTheoryAndMethods_SunYuan_2006.Book`
- Declarations/examples: 7,908
- Lean code: 710 files, 187,113 lines
- Theorems/lemmas: 5,187
- Proof completion: approximately 94.20%
- Explicit `sorry`: 301

The completion percentage is `1 - explicit sorry occurrences / theorem-and-lemma declarations`.
All 707 source files are retained. The default aggregate imports 322 source modules; source
modules still requiring v4.30 porting or causing duplicate-name collisions remain in the tree for
later work but are not imported by `Book.lean`.

Build command:

```bash
cd ReasBook
lake build ReasBook
```
