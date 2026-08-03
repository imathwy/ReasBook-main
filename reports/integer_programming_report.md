# Integer Programming report

- Book: Michele Conforti, Gerard Cornuejols, Giacomo Zambelli, *Integer Programming* (Springer GTM 271, 2014).
- Location: `ReasBook/Books/IntegerProgramming_Conforti_2014/`
- Contributor: TropicalFatFish
- Lean files: 592
- Declaration count: 7912
- Code length: 267043 lines
- Remaining `sorry`/`admit` lines: 439
- Proof percentage: 506/663 proof-pipeline items succeeded = 76.3% for chapters 3-10; current source still allows `sorry`.

Build: `lake build ReasBook` succeeds on Lean v4.30.0.

Notes: this branch keeps only this book's source under `ReasBook/Books/` and removes other books/papers from the Lean project so the repository builds against the unified Lean v4.30.0 stack for this book. The full generated source tree is included; `Book.lean` is a compile-safe aggregate entry while version-sensitive chapter proof scripts are repaired.
