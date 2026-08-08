import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open scoped Gradient

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Algorithm 12.1 is `source-facing` in the chapter's dual proximal-gradient API.

Domain sampling against the nearby project owners identifies:
- `proximal_gradient_step` and `is_proximal_gradient_trajectory` from Chapter 10 as the
  `core/canonical` owners for the generic proximal-gradient step and trajectory;
- `prox[...]` from Chapter 6 as the canonical owner for the underlying proximal step;
- `PosReal` from Chapter 6 as the positive stepsize owner;
- the operator norm on `ContinuousLinearMap` as the canonical source of the bound
  `L_F = ‖A‖² / σ`.

Since the source algorithm specifies an initialization `y^0`, a constant admissible parameter
`L ≥ L_F`, and a recursive proximal update, the clean public API is a trajectory predicate on the
iterate sequence together with a small subtype for admissible constant stepsizes. The gradient
term is kept explicit as a map `gradF`, representing the textbook `∇ F`; under the stronger
identification `gradF = ∇ F`, the Chapter 12 source-facing layer is bridged back to the Chapter 10
owner. -/

/-- The dual smoothness bound `L_F = ‖A‖² / σ` attached to the dual representation. -/
def dual_based_proximal_gradient_dual_lipschitz_constant
    (A : E →L[ℝ] V) (σ : PosReal) : ℝ :=
  ‖A‖ ^ (2 : ℕ) / (σ : ℝ)

-- Proof sketch: unfold `dual_based_proximal_gradient_dual_lipschitz_constant`; the displayed
-- scalar is exactly the textbook bound `‖A‖² / σ`.
/-- Expanding the dual smoothness bound gives the textbook value `‖A‖² / σ`. -/
theorem dual_based_proximal_gradient_dual_lipschitz_constant_eq
    (A : E →L[ℝ] V) (σ : PosReal) :
    dual_based_proximal_gradient_dual_lipschitz_constant A σ =
      ‖A‖ ^ (2 : ℕ) / (σ : ℝ) :=
  rfl

/-- An admissible constant parameter for the dual proximal-gradient method is a positive real
`L` satisfying the textbook lower bound `L_F = ‖A‖² / σ ≤ L`. -/
abbrev DualBasedProximalGradientDualStepsizeParameter
    (A : E →L[ℝ] V) (σ : PosReal) :=
  { L : PosReal // dual_based_proximal_gradient_dual_lipschitz_constant A σ ≤ (L : ℝ) }

namespace DualBasedProximalGradientDualStepsizeParameter

-- Proof sketch: the subtype condition in
-- `DualBasedProximalGradientDualStepsizeParameter A σ` is exactly the required lower bound.
/-- Every admissible dual proximal-gradient parameter satisfies `‖A‖² / σ ≤ L`. -/
theorem lower_bound
    {A : E →L[ℝ] V} {σ : PosReal}
    (L : DualBasedProximalGradientDualStepsizeParameter A σ) :
    dual_based_proximal_gradient_dual_lipschitz_constant A σ ≤ (L : ℝ) :=
  L.2

end DualBasedProximalGradientDualStepsizeParameter

/-- The admissible next dual iterates from `y^k` are the proximal points of `(1 / L) G` at the
forward-gradient point `y^k - (1 / L) gradF(y^k)`, where `gradF` represents the gradient of the
smooth term `F`. -/
def dual_based_proximal_gradient_dual_step
    (G : V → EReal) (gradF : V → V) (L : PosReal) (yk : V) : Set V :=
  prox[((((1 / L : PosReal) : EReal) • G))] (yk - (1 / L : ℝ) • gradF yk)

-- Proof sketch: unfold `dual_based_proximal_gradient_dual_step`; membership is definitionally
-- proximal-set membership for the scaled nonsmooth term at the forward-gradient point.
/-- A point belongs to the dual proximal-gradient step set exactly when it is a proximal point of
`(1 / L) G` at `y^k - (1 / L) gradF(y^k)`. -/
@[simp] theorem mem_dual_based_proximal_gradient_dual_step_iff
    {G : V → EReal} {gradF : V → V} {L : PosReal} {yk yNext : V} :
    yNext ∈ dual_based_proximal_gradient_dual_step G gradF L yk ↔
      yNext ∈ prox[((((1 / L : PosReal) : EReal) • G))]
        (yk - (1 / L : ℝ) • gradF yk) :=
  Iff.rfl

/-- Algorithm 12.1: given an initial point `y^0 = y0` and a constant admissible parameter
`L ≥ ‖A‖² / σ`, a sequence `y` is a dual proximal-gradient trajectory for the dual representation
when every successor iterate satisfies
`y^(k+1) ∈ prox[(1 / L) G] (y^k - (1 / L) ∇F(y^k))`, with `gradF` representing `∇F`. -/
def is_dual_based_proximal_gradient_dual_trajectory
    (G : V → EReal) (gradF : V → V) {A : E →L[ℝ] V} {σ : PosReal}
    (L : DualBasedProximalGradientDualStepsizeParameter A σ)
    (y : ℕ → V) (y0 : V) : Prop :=
  y 0 = y0 ∧
    ∀ k : ℕ, y (k + 1) ∈ dual_based_proximal_gradient_dual_step G gradF L (y k)

-- Proof sketch: extract the initialization equation from the first conjunct of
-- `is_dual_based_proximal_gradient_dual_trajectory`.
/-- A dual proximal-gradient trajectory starts from the prescribed initial point `y^0 = y0`. -/
theorem is_dual_based_proximal_gradient_dual_trajectory_zero
    {G : V → EReal} {gradF : V → V} {A : E →L[ℝ] V} {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A σ}
    {y : ℕ → V} {y0 : V}
    (h : is_dual_based_proximal_gradient_dual_trajectory G gradF L y y0) :
    y 0 = y0 :=
  h.1

-- Proof sketch: specialize the defining universal clause of
-- `is_dual_based_proximal_gradient_dual_trajectory` at the iteration index `k`.
/-- At every iteration `k`, the next dual iterate is a proximal point of the scaled term
`(1 / L) G` at the forward-gradient point `y^k - (1 / L) gradF(y^k)`. -/
theorem is_dual_based_proximal_gradient_dual_trajectory_step
    {G : V → EReal} {gradF : V → V} {A : E →L[ℝ] V} {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A σ}
    {y : ℕ → V} {y0 : V}
    (h : is_dual_based_proximal_gradient_dual_trajectory G gradF L y y0)
    (k : ℕ) :
    y (k + 1) ∈ dual_based_proximal_gradient_dual_step G gradF L (y k) :=
  h.2 k

end

section

variable {V : Type v}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

-- Proof sketch: unfold both step owners. After replacing `gradF` by the canonical gradient of
-- `F`, the two proximal-point sets are definitionally equal.
/-- Under the identification `gradF = ∇ F`, the Chapter 12 explicit-gradient dual step is exactly
the Chapter 10 proximal-gradient step for the composite objective `F + G`. -/
theorem dual_based_proximal_gradient_dual_step_eq_proximal_gradient_step
    (F G : V → EReal) (gradF : V → V) (L : PosReal)
    (hgradF : ∀ y : V, gradF y = ∇ (fun z : V ↦ (F z).toReal) y)
    (yk : V) :
    dual_based_proximal_gradient_dual_step G gradF L yk =
      proximal_gradient_step F G yk L := by
  ext yNext
  rw [mem_dual_based_proximal_gradient_dual_step_iff, mem_proximal_gradient_step_iff]
  simp [hgradF]

-- Proof sketch: pair the supplied interior-domain hypothesis with the source-facing Chapter 12
-- step relation, then rewrite each step through
-- `dual_based_proximal_gradient_dual_step_eq_proximal_gradient_step`.
/-- A Chapter 12 dual proximal-gradient trajectory becomes a Chapter 10 proximal-gradient
trajectory once the explicit dual gradient is identified with `∇ F` and the iterates are known to
lie in `interior (effective_domain F)`. -/
theorem is_dual_based_proximal_gradient_dual_trajectory.toIsProximalGradientTrajectory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : V → EReal} {gradF : V → V} {A : E →L[ℝ] V} {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A σ}
    {y : ℕ → V} {y0 : V}
    (h : is_dual_based_proximal_gradient_dual_trajectory G gradF L y y0)
    (hgradF : ∀ yk : V, gradF yk = ∇ (fun z : V ↦ (F z).toReal) yk)
    (hdom : ∀ k : ℕ, y k ∈ interior (effective_domain F)) :
    is_proximal_gradient_trajectory F G y (fun _ ↦ (L : PosReal)) := by
  intro k
  refine ⟨hdom k, ?_⟩
  simpa [dual_based_proximal_gradient_dual_step_eq_proximal_gradient_step
    F G gradF (L : PosReal) hgradF (y k)] using
    is_dual_based_proximal_gradient_dual_trajectory_step h k

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The reciprocal parameter `σ⁻¹` is an admissible dual proximal-gradient stepsize for the
identity map. -/
theorem dual_based_proximal_gradient_identity_stepsize_parameter_lower_bound
    (σ : PosReal) :
    dual_based_proximal_gradient_dual_lipschitz_constant
        (ContinuousLinearMap.id ℝ E) σ ≤ ((σ⁻¹ : PosReal) : ℝ) := by
  rw [dual_based_proximal_gradient_dual_lipschitz_constant_eq]
  have hnorm : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hsq : ‖ContinuousLinearMap.id ℝ E‖ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [hnorm, norm_nonneg (ContinuousLinearMap.id ℝ E)]
  have hσ : 0 ≤ (σ : ℝ) := σ.2.le
  have hmain :
      ‖ContinuousLinearMap.id ℝ E‖ ^ (2 : ℕ) / (σ : ℝ) ≤ 1 / (σ : ℝ) := by
    simpa using div_le_div_of_nonneg_right hsq hσ
  simpa using hmain

/-- The canonical admissible dual proximal-gradient stepsize parameter for the identity map is
the reciprocal value `σ⁻¹`. -/
abbrev dual_based_proximal_gradient_identity_stepsize_parameter
    (σ : PosReal) :
    DualBasedProximalGradientDualStepsizeParameter
      (ContinuousLinearMap.id ℝ E) σ :=
  ⟨σ⁻¹, dual_based_proximal_gradient_identity_stepsize_parameter_lower_bound σ⟩

end
