import Mathlib.Tactic.Recall
import Nesterov.Chap06.Definition_6_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

/- Text 6.1.5.2 lies in Chapter 6's finite-dimensional log-sum-exp stabilization domain.

Sampled owner-style declarations:
- `coordinateMaximum` in `Chap06/Proposition_6_23`, the chapter owner for the maximal coordinate;
- `centeredByCoordinateMaximum` in `Chap06/Proposition_6_23`, the canonical max-centered vector;
- `η` in `Chap06/Definition_6_27`, the recalled log-sum-exp potential;
- `eta_eq_coordinateMaximum_add_eta_centered` and
  `gradient_eta_eq_gradient_eta_centered` in `Chap06/Proposition_6_23`, the canonical stable
  shift identities.

Best owner abstraction:
- source-facing: the stable max-shift identity for the scaled log-sum-exp potential;
- core/canonical: `coordinateMaximum`, `centeredByCoordinateMaximum`, `η`, and the two stable
  shift theorems from `Proposition_6_23`;
- bridge/view: the coordinate observations that the centered vector is nonpositive and has a zero
  coordinate.

This item reuses the chapter owners directly for the stable shift formulas and keeps only the
centered-coordinate consequences as local statement skeletons.
-/

section

variable {m : ℕ} [NeZero m]

local notation "U" => EuclideanSpace ℝ (Fin m)

/- Text 6.1.5.2-Stable Log-Sum-Exp Shift Trick: if `v` is obtained by subtracting the maximal
coordinate `coordinateMaximum u` from every component of `u`, then the scaled log-sum-exp
potential satisfies the stable identity
`η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u)`. -/
recall eta_eq_coordinateMaximum_add_eta_centered

-- Proof sketch: `coordinateMaximum u` is the maximum of the finite coordinate family, so each
-- coordinate `u j` is bounded above by it. Rewriting
-- `centeredByCoordinateMaximum u j = u j - coordinateMaximum u` gives the claim.
/-- Every coordinate of the vector centered by its maximal coordinate is nonpositive. -/
theorem centeredByCoordinateMaximum_nonpos
    (u : U) (j : Fin m) :
    centeredByCoordinateMaximum u j ≤ 0 := sorry

-- Proof sketch: on the finite index type `Fin m`, the maximum defining `coordinateMaximum u` is
-- attained. At a maximizing coordinate, subtracting `coordinateMaximum u` leaves `0`.
/-- The vector centered by its maximal coordinate has at least one zero coordinate. -/
theorem centeredByCoordinateMaximum_exists_eq_zero
    (u : U) :
    ∃ j : Fin m, centeredByCoordinateMaximum u j = 0 := sorry

/- Subtracting the maximal coordinate from every component preserves the gradient of the scaled
log-sum-exp potential, so the same stable shift trick applies to gradient computation. -/
recall gradient_eta_eq_gradient_eta_centered

end
