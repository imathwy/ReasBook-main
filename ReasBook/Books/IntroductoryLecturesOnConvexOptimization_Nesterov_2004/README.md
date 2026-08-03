# Introductory Lectures on Convex Optimization (Nesterov, 2004)

Lean 4 formalization of Yurii Nesterov's *Introductory Lectures on Convex Optimization*.

- Contributor: `imathwy`
- Upstream base: `optpku/ReasBook@11a65a5` (branch `v4.30.0`)
- Lean/mathlib: `v4.30.0` / `v4.30.0`
- Main module: `IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Book`
- Declarations/examples: 10,064
- Lean code: 1,645 files, 87,388 lines
- Theorems/lemmas: 6,972
- Proof completion: approximately 98.91%
- Explicit `sorry`: 76

The completion percentage is `1 - explicit sorry occurrences / theorem-and-lemma declarations`.
All 1,642 source files are retained. The default aggregate imports 1,248 source modules; source
modules still requiring v4.30 porting or causing duplicate-name collisions remain in the tree for
later work but are not imported by `Book.lean`.

Build command:

```bash
cd ReasBook
lake build ReasBook
```
