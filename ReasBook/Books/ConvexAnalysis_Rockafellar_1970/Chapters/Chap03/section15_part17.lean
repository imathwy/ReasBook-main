/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part16

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise

/-- Text 15.0.30: Let `f : ℝⁿ → [0, +∞]` be a nonnegative closed convex function with `f 0 = 0`,
and let `fᵒ` be its polar in the extended sense, defined by

`fᵒ x⋆ = inf { μ⋆ ≥ 0 | ⟪x, x⋆⟫ ≤ 1 + μ⋆ * f x for all x }`.

Then for all `x ∈ dom f` and `x⋆ ∈ dom fᵒ`, one has
`⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆`.

In this development, `ℝⁿ` is `Fin n → ℝ`, `fᵒ` is `polarConvex f`, and effective-domain
assumptions are modeled by `f x ≠ ⊤` and `polarConvex f x⋆ ≠ ⊤`. -/
theorem inner_le_one_add_mul_polarConvex_of_nonneg_closedConvex_zero {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) (hx : f x ≠ ⊤)
    (hxStar : polarConvex f xStar ≠ ⊤) :
    ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (1 : EReal) + f x * polarConvex f xStar := by
  simpa using
    (inner_le_one_add_mul_polarConvex (f := f) (x := x) (xStar := xStar) hx hxStar)

end Section15
end Chap03
