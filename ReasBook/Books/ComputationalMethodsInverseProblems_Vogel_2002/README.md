# Computational Methods for Inverse Problems

Curtis R. Vogel, first edition (2002), SIAM.

Lean 4 formalization covering the inverse-problem framework, regularization,
Tikhonov methods, iterative methods, spectral filter methods, parameter choice,
variational methods, and iterative solution methods across Chapters 1–9.
The project uses Lean/mathlib `v4.32.0` and keeps the chapter structure of the
book in the [`Book/`](Book/) directory.

## Contributors

- Yifan Bai (@TTony2019)
- Wanli Ma
- Zichen Wang

## Statistics

- **Lean files:** 683 `.lean` files, 114,644 lines
- **Theorem/lemma/example declarations:** 3,109
- **Remaining placeholders:** 105 `sorry` occurrences
- **Lean toolchain:** `leanprover/lean4:v4.32.0`

## Build

From this directory, download the mathlib cache and build the book entry point:

```bash
lake exe cache get
lake -R build
```

[`Book.lean`](Book.lean) imports all chapter modules. Some source files in the
current snapshot still contain Lean errors and duplicate declarations, so a
full build is not yet clean; the diagnostics identify the affected chapter
files.

## Project files

- [`lakefile.toml`](lakefile.toml) — Lake project configuration
- [`book.yml`](book.yml) — book metadata and statistics
- [`Book.lean`](Book.lean) — aggregate entry point for all formalized chapters
- [`Book/`](Book/) — chapter-by-chapter formalization
