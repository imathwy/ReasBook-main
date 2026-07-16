import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Proposition_7_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics
open Filter

local notation "DimPair" => ℕ × ℕ

/- Proposition 7.4 lies in the chapter's support-function smoothing / one-step work asymptotics
domain.

Sampled owner-style declarations:
- `SupportFunctionSmoothingMethod` in `Algorithm_7_3`, the chapter owner of Method `S_N(R)`;
- mathlib `Asymptotics.IsBigO`, the canonical asymptotic owner behind `f =O[l] g`;
- `restrictedDimensionFilter` in `Proposition_7_6.lean`, the chapter owner of the admissible
  dimension regime `0 < p < n (n + 1) / 2` with `n → ∞`;
- `frobeniusGramPreliminaryArithmeticWorkBound` in `Proposition_7_5.lean`, the nearby
  source-facing work owner for the Frobenius-Gram subroutine that contributes to one step of the
  method.

Best owner abstraction:
- source-facing: the direct one-step work profile
  `(n, p) ↦ gradientWork (n, p) + projectionWork (n, p) + auxiliaryWork (n, p)`;
- core/canonical: `Asymptotics.IsBigO` on `restrictedDimensionFilter`;
- bridge/view: none beyond reading the source prose as the sum of its three component costs.

Primitive data:
- the three component cost profiles for one step of the method.

Derived API:
- the final `=O` bound by `n^2 (n + p)` on the chapter's restricted-dimension filter.

There is no genuine upstream owner in this chapter for the arithmetic work of one Algorithm 7.3
iteration. The previous version introduced a namespace-packaged alias for the sum of three
arbitrary profiles, but that alias carried no additional method data and violated the no-wrapper
rule. This refinement therefore keeps the proposition directly on the source-facing sum profile
while still reusing the canonical filter owner `restrictedDimensionFilter` from Proposition 7.6.
-/

-- Proof sketch: add the three assumed `O`-bounds for the gradient, projection, and auxiliary
-- vector computations. On the restricted regime `p < n (n + 1) / 2`, the quadratic term `p^2`
-- is absorbed by `n^3 + n^2 p`, and `n^3 + n^2 p = n^2 (n + p)`.
/-- Proposition 7.4: along the restricted-dimension regime where `n → ∞` and
`0 < p < n (n + 1) / 2`, if one iteration of Method `S_N(R)` has gradient work
`O(p n^2)`, Frobenius-projection work `O(n^3)`, and auxiliary `ℝ^p` arithmetic work `O(p^2)`,
then the total one-step arithmetic work, obtained by summing those three component profiles, is
`O(n^2 (n + p))`. -/
theorem supportFunctionSmoothingIterationWork_isBigO_n_sq_mul_n_add_p
    (gradientWork projectionWork auxiliaryWork : DimPair → ℝ)
    (hgradient : gradientWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.2 : ℝ) * (dims.1 : ℝ) ^ (2 : ℕ)))
    (hprojection : projectionWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (3 : ℕ)))
    (hauxiliary : auxiliaryWork =O[restrictedDimensionFilter]
      (fun dims ↦ (dims.2 : ℝ) ^ (2 : ℕ))) :
    (fun dims ↦ gradientWork dims + projectionWork dims + auxiliaryWork dims) =O[
      restrictedDimensionFilter]
      (fun dims ↦ (dims.1 : ℝ) ^ (2 : ℕ) * ((dims.1 : ℝ) + dims.2)) := by
  sorry

end
