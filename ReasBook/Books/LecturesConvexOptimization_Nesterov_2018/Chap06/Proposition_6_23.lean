import Mathlib
import Nesterov.Chap05.Definition_5_4_7_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped Gradient

noncomputable section

/- Proposition 6.23 lies in Chapter 6's finite-family log-sum-exp / stable max-shift domain.

Sampled owner-style declarations:
- `logSumExp` and `logSumExp_apply` in `Chap05/Definition_5_4_7_11`, the project owner for the
  unscaled finite log-sum-exp potential on `EuclideanSpace ℝ (Fin n)`;
- `convexOn_log_sum_exp_of_convexOn` in `Chap03/Proposition_3_21`, the project owner theorem for
  finite-family log-sum-exp on a common domain;
- `smoothMaxInnerApproximation` in `Chap07/Definition_7_42`, the later project smoothing owner
  using the canonical positive-parameter surface `{μ : ℝ // 0 < μ}`;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, the analogous Chapter 6
  positive-parameter log-sum-exp owner for spectral smoothing;
- `entropyRegularizedSimplexObjective_softmax_eq_value` in `Chap06/Lemma_6_4`, a direct
  downstream use of the scaled log-sum-exp owner.

Best owner abstraction:
- source-facing: `coordinateMaximum`, `centeredByCoordinateMaximum`, `η`, and the stable
  shift/gradient identities of Proposition 6.23;
- core/canonical: the finite-family positive-parameter owner `η`;
- bridge/view: `eta_apply`.

Primitive data:
- a finite index type `ι`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the score vector `u : EuclideanSpace ℝ ι`.

Derived API:
- the finite-maximum expansion `coordinateMaximum_def`;
- the coordinate formula `centeredByCoordinateMaximum_apply`;
- the evaluation formula `eta_apply`;
- the shift and gradient invariance theorems.

This file stays at the source-facing Chapter 6 layer. The positive-parameter log-sum-exp owner
`η` is stated at the intrinsic finite-family level, while the stable max-shift specialization
continues to use the coordinate-owner `coordinateMaximum` on the same finite score vectors.
-/

universe v

variable {ι : Type v} [Fintype ι]

/-- The log-sum-exp smoothing potential
`η_μ(u) = μ log (∑ⱼ exp (uⱼ / μ))` on a finite score family for a positive smoothing parameter
`μ`. -/
def η (μ : {μ : ℝ // 0 < μ}) (u : EuclideanSpace ℝ ι) : ℝ :=
  (μ : ℝ) * Real.log (∑ j : ι, Real.exp (u j / (μ : ℝ)))

/-- Evaluating `η μ` at `u` gives the defining log-sum-exp formula
`μ log (∑ⱼ exp (uⱼ / μ))`. -/
theorem eta_apply (μ : {μ : ℝ // 0 < μ}) (u : EuclideanSpace ℝ ι) :
    η μ u = (μ : ℝ) * Real.log (∑ j : ι, Real.exp (u j / (μ : ℝ))) :=
  rfl

section

variable {m : ℕ} [NeZero m]

local notation "U" => EuclideanSpace ℝ (Fin m)

/-- The maximal coordinate of `u ∈ ℝᵐ`. -/
def coordinateMaximum (u : U) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m ↦ u j)

/-- Expanding `coordinateMaximum u` gives the finite maximum of the coordinates of `u`. -/
-- Proof sketch: unfold `coordinateMaximum`; the right-hand side is the defining `Finset.sup'`.
theorem coordinateMaximum_def (u : U) :
    coordinateMaximum u =
      Finset.univ.sup' Finset.univ_nonempty (fun j : Fin m ↦ u j) := rfl

/-- The vector obtained from `u` by subtracting its maximal coordinate from every component. -/
def centeredByCoordinateMaximum (u : U) : U :=
  WithLp.toLp 2 (fun j : Fin m ↦ u j - coordinateMaximum u)

/-- Each coordinate of `centeredByCoordinateMaximum u` is obtained by subtracting
`coordinateMaximum u` from the corresponding coordinate of `u`. -/
-- Proof sketch: unfold `centeredByCoordinateMaximum`; `WithLp.toLp` preserves the displayed
-- coordinate formula.
theorem centeredByCoordinateMaximum_apply (u : U) (j : Fin m) :
    centeredByCoordinateMaximum u j = u j - coordinateMaximum u := rfl

/-- Proposition 6.23 (1): if `v` is obtained from `u` by subtracting the maximal coordinate
`coordinateMaximum u` from every component, then the log-sum-exp potential satisfies
`η(u) = coordinateMaximum u + η(v)`. -/
-- Proof sketch: factor `exp (coordinateMaximum u / μ)` out of the finite sum
-- `∑ⱼ exp (uⱼ / μ)`, rewrite the remaining summand using
-- `centeredByCoordinateMaximum_apply`, and then apply `Real.log_mul` to pull out the additive
-- term `coordinateMaximum u`.
theorem eta_eq_coordinateMaximum_add_eta_centered
    (μ : {μ : ℝ // 0 < μ}) (u : U) :
    η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u) := sorry

/-- Proposition 6.23 (2): subtracting the same maximal coordinate from every component leaves the
gradient of the log-sum-exp potential unchanged. -/
-- Proof sketch: differentiate the explicit softmax formula for `η`, or differentiate the identity
-- from `eta_eq_coordinateMaximum_add_eta_centered` on regions where the maximizing index is fixed
-- and then use the explicit coordinate formula to remove the local partition.
theorem gradient_eta_eq_gradient_eta_centered
    (μ : {μ : ℝ // 0 < μ}) (u : U) :
    ∇ (η μ) u = ∇ (η μ) (centeredByCoordinateMaximum u) := sorry

end

end
