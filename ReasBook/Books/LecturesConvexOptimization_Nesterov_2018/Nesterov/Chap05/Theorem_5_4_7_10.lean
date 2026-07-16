import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_4_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.10 lies in the Chapter 5 simplex-monomial / positive-orthant directional-
derivative domain.

Sampled owner declarations:
* `lineDerivWithin` from mathlib, the canonical owner for within-domain directional derivatives
  along affine lines;
* `ambientMonomialXi` and `ξ_[a]` from `Definition_5_4_7_17`, the ambient/source-facing owners
  for the simplex monomial;
* `lineDerivWithin_log_monomialXi_eq_centerMass_relativeDirection` from `Theorem_5_4_7_9`, the
  adjacent owner-level logarithmic derivative identity this theorem builds on;
* `Finset.centerMass` together with the notation `δ[x](h)` from `Definition_5_4_7_14` and
  `Definition_5_4_7_18`, the canonical weighted-mean owner and the source-facing relative
  direction.

Source/core/bridge triage:
* source-facing: the textbook identity `D ξ_a(x)[h] = ξ_a(x) ⟪a, δ_x(h)⟫`;
* core/canonical: `lineDerivWithin ℝ (ambientMonomialXi a) Xₙ x h`;
* bridge/view: the source-facing value `ξ_[a] x` and the logarithmic derivative theorem from
  `Theorem_5_4_7_9`.

This file therefore stays as a thin bridge theorem over the ambient owner `lineDerivWithin`; it
keeps no parallel logarithmic-derivative wrapper, and it treats Theorem 5.4.7.9 as the upstream
owner-level input rather than restating that API locally.
-/

-- Proof sketch: combine the scalar chain rule for `exp` with the logarithmic derivative identity
-- from `Theorem_5_4_7_9`, using that on the strict positive orthant
-- `ambientMonomialXi a = Real.exp ∘ (Real.log ∘ ambientMonomialXi a)`, and then rewrite the
-- value term by `ambientMonomialXi_eq_monomialXi`.
/-- Theorem 5.4.7.10: for `a ∈ Δₙ`, the directional derivative of the monomial `ξ_a` at a
strictly positive point `x` along `h` is
`ξ_a(x) Finset.univ.centerMass a (δ_x(h)) = ξ_a(x) ⟪a, δ_x(h)⟫`. -/
theorem lineDerivWithin_monomialXi_eq_monomialXi_mul_centerMass_relativeDirection
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    lineDerivWithin ℝ (ambientMonomialXi a) Xₙ x h =
      ξ_[a] x * Finset.univ.centerMass a (δ[x](h)) := by
  sorry

end
