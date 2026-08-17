module

public import Book.Ch9.Definition_9_5_1.Iteration

public section

/-! Definition 9.5.1-extra-1. Canonical source-facing anchor.

The Chapter 9 Richardson-Lucy update `(9.42)` is now owned by the directly
importable foundation module `Book.Ch9.Definition_9_5_1.Iteration`. This file
keeps the numbered source item as a thin bridge to that canonical owner rather
than re-declaring the same matrix formulas.
-/

/- Definition 9.5.1-extra-1.

The source defines the one-step Richardson-Lucy update

`f⁺ j = (f j / k j) * ∑ i, K i j * (d i / (K *ᵥ f) i)`,

with `k j = ∑ i, K i j`. The faithful repository owner for that source-facing
construction is `RichardsonLucy.update`, with `RichardsonLucy.columnSum` as the
companion normalization factor. -/
#check RichardsonLucy.update

/- Companion owner for the normalization factor `k j = ∑ i, K i j`. -/
#check RichardsonLucy.columnSum

/- Companion theorem for the source's equation `(9.43)`. -/
#check RichardsonLucy.sum_mulVec_update_eq_sum_data

/- Companion theorem exposing the transpose/backprojection form of `(9.42)`. -/
#check RichardsonLucy.update_eq_transpose_mulVec
