import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_16
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_17
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_7_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.9 lies in the Chapter 5 simplex-monomial / positive-orthant directional-
derivative domain.

Sampled owner declarations:
* `lineDerivWithin` from mathlib, the canonical owner for within-domain directional derivatives
  along affine lines;
* `ambientMonomialXi` from `Definition_5_4_7_17`, the ambient owner whose restriction to
  `positiveOrthant n` is the source-facing monomial `ξ_[a]`;
* `relativeDirection` together with the notation `δ[x](h)` from `Definition_5_4_7_14`, the
  source-facing scaled direction;
* `Finset.centerMass` and `centerMass_relativeDirection_eq_sum` from `Definition_5_4_7_18`, the
  canonical weighted-mean owner and its simplex-specialized bridge for `δ_x(h)`.

Source/core/bridge triage:
* source-facing: the logarithmic derivative identity `D log ξ_a(x)[h] = ⟪a, δ_x(h)⟫`;
* core/canonical: `lineDerivWithin ℝ`;
* bridge/view: the ambient representative `Real.log ∘ ambientMonomialXi a` of `log ξ_a` on the
  strict positive orthant, and the center-of-mass expression for the simplex-weighted mean.

The public theorem is therefore a bridge statement over the canonical owner `lineDerivWithin`;
it should not introduce a parallel owner for the logarithmic derivative or a duplicate wrapper
for the weighted mean. -/

-- Proof sketch: on the positive orthant, rewrite `log ξ_a(y)` as the logarithm of the product
-- defining `ξ_a`; then differentiate along the affine line `x + t • h` inside the orthant and
-- identify `δ[x](h)` with the vector whose `i`-th coordinate is `h i / x i`, so the resulting
-- weighted sum is the canonical simplex center of mass `Finset.univ.centerMass a (δ[x](h))`.
/-- Theorem 5.4.7.9: for `a ∈ Δₙ`, the directional derivative of `log ξ_a` at a strictly positive
point `x` along the ambient direction `h`, taken within the positive orthant, is the
simplex-weighted mean `Finset.univ.centerMass a (δ_x(h)) = ⟪a, δ_x(h)⟫`. -/
theorem lineDerivWithin_log_monomialXi_eq_centerMass_relativeDirection
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    lineDerivWithin ℝ (Real.log ∘ ambientMonomialXi a) Xₙ x h =
      Finset.univ.centerMass a (δ[x](h)) := by
  sorry

end
