import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics
open Filter

local notation "DimPair" => ℕ × ℕ

/- Proposition 7.6 lies in the chapter's asymptotic-complexity comparison domain.

Sampled owner-style declarations:
- mathlib `Asymptotics.IsBigO`, the canonical asymptotic owner behind `f =O[l] g`;
- mathlib `Filter.comap`, the canonical way to express the regime where only the first coordinate
  tends to infinity;
- mathlib `Filter.principal`, the canonical way to impose the side condition
  `0 < p < n (n + 1) / 2`.

Best owner abstraction:
- source-facing: the comparison between the gradient-method total complexity bound
  `n^2 p^2 + (1 / δ) n^(5 / 2) (p + n) log n` and the short-step interior-point bound
  `p n^(5 / 2) (p + n) log (n / δ)`;
- core/canonical: `Asymptotics.IsBigO` on the chapter's admissible-dimension filter;
- bridge/view: none beyond the filter owner itself.

Primitive data:
- the admissible dimension regime `0 < p < n (n + 1) / 2` with `n → ∞`;
- an accuracy profile `δ(n, p)`;
- the gradient-method total arithmetic-work profile `TG`.

Derived API:
- the eventual dominance of the gradient-method upper bound by the short-step interior-point
  complexity model under the source condition `δ ≥ O(1 / p)`.

The source proposition compares two displayed complexity formulas rather than introducing a new
wrapper notion. This file therefore keeps the canonical filter owner for the admissible regime and
states the comparison directly on mathlib's `=O` surface.
-/

/-- The filter expressing statements that hold for all sufficiently large `n` and every positive
`p` satisfying `p < n (n + 1) / 2`. -/
def restrictedDimensionFilter : Filter DimPair :=
  comap Prod.fst atTop ⊓
    principal
      (setOf fun dims : DimPair ↦
        0 < dims.2 ∧ dims.2 < dims.1 * (dims.1 + 1) / 2)

-- Proof sketch: use the eventual lower bound `C / p ≤ δ(n, p)` and the positivity of `p` on
-- `restrictedDimensionFilter` to compare `(1 / δ(n, p))` with a constant multiple of `p`.
-- Then use `δ(n, p) ≤ n` to control `log n` by `log (n / δ(n, p))` up to absolute constants.
-- On the admissible regime `p < n (n + 1) / 2`, the polynomial term `n^2 p^2` is absorbed by
-- `p n^(5 / 2) (p + n) log (n / δ(n, p))`, so the displayed gradient-method bound is dominated by
-- the displayed short-step interior-point bound.
/-- Proposition 7.6 [Chapter7_1.json:40]: along the admissible regime
`0 < p < n (n + 1) / 2` with `n → ∞`, if the total arithmetic complexity `T_G(n, p)` of method
`(7.1.30)` is bounded by
`O(n^2 p^2 + (1 / δ(n, p)) n^(5 / 2) (p + n) log n)` and the required relative accuracy profile
`δ(n, p)` is eventually bounded above by `n` and below by a positive constant multiple of `1 / p`,
then `T_G(n, p)` is also bounded by the short-step path-following complexity scale
`O(p n^(5 / 2) (p + n) log (n / δ(n, p)))`. In this asymptotic sense, the gradient-type method is
preferable whenever `δ ≥ O(1 / p)`. -/
theorem gradientMethod_isBigO_shortStepPathFollowing_of_accuracy_eventually_ge_const_inv_p
    (δ TG : DimPair → ℝ) {C : ℝ} (hC : 0 < C)
    (hδ_upper : ∀ᶠ dims in restrictedDimensionFilter, δ dims ≤ (dims.1 : ℝ))
    (hδ_lower : ∀ᶠ dims in restrictedDimensionFilter, C / (dims.2 : ℝ) ≤ δ dims)
    (hTG :
      TG =O[restrictedDimensionFilter]
        (fun dims ↦
          (dims.1 : ℝ) ^ (2 : ℕ) * (dims.2 : ℝ) ^ (2 : ℕ) +
            (1 / δ dims) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
              ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ))) :
    TG =O[restrictedDimensionFilter]
      (fun dims ↦
        (dims.2 : ℝ) * Real.rpow (dims.1 : ℝ) (5 / 2 : ℝ) *
          ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log ((dims.1 : ℝ) / δ dims)) := sorry

end
