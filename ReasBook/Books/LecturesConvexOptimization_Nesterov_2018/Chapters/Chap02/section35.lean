import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_35_1 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 2.35.1 is source-facing in the projected-gradient / metric-projection domain on a
complete real inner-product space.

Owner declarations sampled for this refinement:
* `IsProjectionPointOn` in `Chap07/Definition_7_3`, the primitive nearest-point predicate;
* `IsProjectionPointOn.isMinOn` in `Definition_2_33`, the canonical minimizing-property API;
* `euclideanProjection` and `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the
  chapter's chosen projection point and its owner bridge.
* `NNRealˣ`, the project-standard owner for primitive positive real parameters.

Best owner abstraction:
* `gradientStep f xBar γ`, with `γ : NNRealˣ`;
* `IsProjectionPointOn Q (gradientStep f xBar γ) p`.

Source/core/bridge triage:
* source-facing: `gradientMapping` and `reducedGradient`;
* core/canonical: `IsProjectionPointOn` and `euclideanProjection`;
* bridge/view: `gradientMapping_isProjectionPointOn`.

Primitive data:
* the feasible set `Q` with nonempty / closed / convex structure;
* the objective `f`, base point `xBar`, and positive inverse-stepsize / regularization
  parameter `γ`.

Derived API:
* the owner projection-point view `gradientMapping_isProjectionPointOn`;
* feasibility and minimizing properties recovered from that owner bridge;
* the residual formula already built into `reducedGradient`.

This file therefore keeps the source-facing projected-step objects and the single owner bridge
needed for downstream projection-point reasoning, while avoiding any heavier wrapper API.
-/

section

variable [CompleteSpace E]

/-- The explicit gradient step from `xBar` with positive inverse-stepsize parameter `γ`. -/
def gradientStep
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    E :=
  xBar - ((γ : ℝ)⁻¹) • ∇ f xBar

/-- Definition 2.35.1 (1): the projected-gradient point is the Euclidean projection of the explicit
gradient step `gradientStep f xBar γ` onto `Q`. -/
def gradientMapping
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ)
    :
    E :=
  euclideanProjection Q hQ_nonempty hQ_closed hQ_convex
    (gradientStep f xBar γ)

private abbrev nonemptyOfFact (Q : Set E) [Fact (Set.Nonempty Q)] : Set.Nonempty Q :=
  Fact.out

namespace ProjectedGradient

scoped notation:max
    "x_Q[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  gradientMapping
    Q hQ_nonempty hQ_closed hQ_convex f xBar γ

scoped notation:max
    "x_f[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  gradientMapping
    Q hQ_nonempty hQ_closed hQ_convex f xBar γ

scoped notation:max
    "x_Q[" Q ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  gradientMapping
    Q (nonemptyOfFact Q) hQ_closed hQ_convex f xBar γ

scoped notation:max
    "x_f[" Q ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  gradientMapping
    Q (nonemptyOfFact Q) hQ_closed hQ_convex f xBar γ

end ProjectedGradient

open scoped ProjectedGradient

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (γ : NNRealˣ)

/-- The projected-gradient point is a projection point of the explicit gradient step
`gradientStep f xBar γ` onto `Q`. -/
theorem gradientMapping_isProjectionPointOn
    (xBar : E)
    :
    IsProjectionPointOn Q (gradientStep f xBar γ)
      x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) :=
  euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex
    (gradientStep f xBar γ)

/-- Definition 2.35.1 (2): the reduced gradient is the scaled residual from `xBar` to the
projected-gradient point. -/
def reducedGradient
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ)
    :
    E :=
  (γ : ℝ) • (xBar - gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ)

namespace ProjectedGradient

scoped notation:max
    "g_Q[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  reducedGradient
    Q hQ_nonempty hQ_closed hQ_convex f xBar γ

scoped notation:max
    "g_f[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  reducedGradient
    Q hQ_nonempty hQ_closed hQ_convex f xBar γ

scoped notation:max
    "g_Q[" Q ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  reducedGradient
    Q (nonemptyOfFact Q) hQ_closed hQ_convex f xBar γ

scoped notation:max
    "g_f[" Q ";" hQ_closed ";" hQ_convex "|" f ";" γ "]" "(" xBar ")" =>
  reducedGradient
    Q (nonemptyOfFact Q) hQ_closed hQ_convex f xBar γ

end ProjectedGradient

end

end

/-! ### Remark_2_35_1 (from Chap02) -/
open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: projected-gradient / Euclidean-projection step formulas on a complete real
inner-product space, with the textbook `ℝⁿ` formulas recovered by specialization.

Owner declarations sampled for this refinement:
* `IsProjectionPointOn` in `Chap07/Definition_7_3`, the primitive nearest-point predicate;
* `euclideanProjection` and `euclideanProjection_univ` in `Theorem_2_33`, the chapter's chosen
  projection map and its owner `Set.univ` specialization;
* `gradientMapping` and `reducedGradient` in `Definition_2_35_1`, the source-facing
  projected-gradient point and residual.

Best owner abstraction:
* source-facing: `gradientMapping` and `reducedGradient`;
* core/canonical: `IsProjectionPointOn` and `euclideanProjection`;
* bridge/view: the solved-form step identity and the `Set.univ` specializations in this remark.

Primitive data:
* the feasible set `Q` with nonempty / closed / convex structure;
* the objective `f`, base point `xBar`, and parameter `γ`.

Derived API:
* the explicit step identity recovered from `reducedGradient`;
* the whole-space formulas recovered from `euclideanProjection_univ`.

This file therefore keeps only the source-facing bridge theorems and reuses the owner projection
theorem for the `Set.univ` specialization instead of reproving projection uniqueness locally. -/

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ)

/-- Remark 2.35.1: the projected-gradient point is obtained from `xBar` by a step of size `1 / γ`
in the direction of the reduced gradient. -/
-- Proof sketch: start from the defining identity
-- `reducedGradient = γ • (xBar - gradientMapping)` and multiply by `γ⁻¹`.
theorem gradientMapping_eq_point_sub_inv_smul_reducedGradient
    :
    x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) =
      xBar - (γ : ℝ)⁻¹ • g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) := by
  have hγ : (γ : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero γ
  simp [reducedGradient, smul_smul, hγ]

end

/-- When the feasible set is all of the ambient space, the projected-gradient point is the ordinary
gradient step with stepsize `1 / γ`. The textbook statement on `ℝⁿ` is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: unfold `gradientMapping` and apply the owner theorem `euclideanProjection_univ`
-- to the explicit gradient step.
@[simp] theorem gradientMapping_univ_eq_gradient_step
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    x_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; γ](xBar) =
      gradientStep f xBar γ := by
  simp [gradientMapping]

/-- For the unconstrained problem on the ambient space, the reduced gradient equals the ordinary
gradient. The textbook statement on `ℝⁿ` is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: substitute `gradientMapping_univ_eq_gradient_step` into the defining identity
-- `reducedGradient = γ • (xBar - gradientMapping)` and simplify the scalar factor
-- `γ * γ⁻¹ = 1`.
@[simp] theorem reducedGradient_univ_eq_gradient
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    g_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; γ](xBar) =
      ∇ f xBar := by
  rw [reducedGradient, gradientMapping_univ_eq_gradient_step]
  have hγ : (γ : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero γ
  simp [gradientStep, hγ]

end

/-! ### Remark_2_35_2 (from Chap02) -/
open scoped Gradient ProjectedGradient

universe u

/- Remark 2.35.2 is a recall-only item in the projected-gradient / Euclidean-projection domain on
nonempty closed convex sets in a complete real inner-product space. The textbook `ℝⁿ` statement is
the specialization `E = EuclideanSpace ℝ (Fin n)`.

Primary domain:
* the ambient projected-gradient point `x_Q(xBar; γ)`, defined by projecting the explicit
  gradient step from an arbitrary ambient base point `xBar : E`.

Owner declarations sampled for this refinement:
* `gradientMapping` in `Definition_2_35_1`, the source-facing projected-gradient point;
* `gradientMapping_isProjectionPointOn` in `Definition_2_35_1`, the chapter's source-facing
  projection-point bridge for that projected-gradient point;
* `euclideanProjection` in `Theorem_2_33`, the lower owner used internally by
  `gradientMapping`;
* `gradientMapping_eq_point_sub_inv_smul_reducedGradient` in `Remark_2_35_1`, the later
  source-facing step identity derived from the same owner.

Best owner abstraction:
* `gradientMapping`.

Primitive data:
* the feasible set `Q` with nonempty / closed / convex structure;
* the objective `f`, the ambient base point `xBar`, and the parameter `γ`;
* the complete real inner-product-space structure on `E`, which is exactly the ambient owner layer
  used by `gradientMapping` and `euclideanProjection`.

Derived API:
* `gradientMapping_isProjectionPointOn`, the direct source-facing projection-point bridge;
* the later step identity `gradientMapping_eq_point_sub_inv_smul_reducedGradient`.

Source/core/bridge triage:
* source-facing: the remark that `x_Q(xBar; γ)` is well-defined for every ambient `xBar : E`,
  with no hypothesis `xBar ∈ Q`;
* core/canonical: `gradientMapping`;
* bridge/view: `gradientMapping_isProjectionPointOn`.

Accordingly, this file stays at the owner level: it recalls `gradientMapping` directly in the
general ambient space where it is defined, and recalls its chapter-local projection-point bridge
instead of dropping back to the lower `euclideanProjection` interface or re-specializing either
declaration to `ℝⁿ`. -/

recall gradientMapping
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    E

recall gradientMapping_isProjectionPointOn
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (γ : NNRealˣ) (xBar : E) :
    IsProjectionPointOn Q (gradientStep f xBar γ)
      x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar)

/-! ### Definition_2_35 (from Chap02) -/
open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: projected-gradient quadratic model subproblems on a nonempty closed convex set
in a complete real inner-product space.

Owner declarations sampled for this item:
* `firstOrderTaylorModelAt` and `quadraticallyRegularizedObjective` in
  `Definition_1_4_17.lean`, which own the affine tangent model and its quadratic regularization;
* `gradient_quadratic_model_eq_completedSquare` in `Chap01/FirstOrderTaylorModel.lean`, the
  owner completed-square bridge for that regularized first-order model;
* `gradientStep`, `gradientMapping`, and `reducedGradient` in `Definition_2_35_1.lean`, which own
  the projected-gradient step, its projected point, and the scaled residual;
* `gradientMapping_isProjectionPointOn` in `Definition_2_35_1.lean`, the canonical projection
  certificate for the projected-gradient point.

Source/core/bridge triage:
* source-facing: Definition 2.35's minimizer formula and reduced-gradient residual formula;
* core/canonical: `gradientMapping` and `reducedGradient`;
* bridge/view: the minimizing-property theorem below, together with the reused owner rewrite
  `gradient_quadratic_model_eq_completedSquare`.

This file therefore keeps the owner declarations themselves as direct recalls and states only the
thin bridge theorem needed to recover the textbook minimizer characterization, reusing the Chapter
1 completed-square identity directly instead of duplicating it locally. -/

/- Definition 2.35: the textbook gradient mapping and reduced gradient are represented by the
canonical owner declarations `gradientMapping` and `reducedGradient`. The point
`gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ` is the unique minimizer of the
quadratically regularized first-order Taylor model over `Q`, and
`reducedGradient Q hQ_nonempty hQ_closed hQ_convex f xBar γ` is the scaled residual
`γ • (xBar - gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ)`. -/
recall gradientMapping
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    E

recall reducedGradient
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    E

/-- The projected-gradient point belongs to `Q` and minimizes the quadratically regularized
first-order Taylor model from Definition 2.35 over `Q`. -/
-- Proof sketch: rewrite the objective using
-- `gradient_quadratic_model_eq_completedSquare`; up to an additive constant it becomes the squared
-- distance to `gradientStep f xBar γ`. Then apply the projection optimality of
-- `gradientMapping_isProjectionPointOn`.
theorem gradientMapping_minimizes_objective
    {Q : Set E} (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {f : E → ℝ} {xBar : E} {γ : NNRealˣ} :
    x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) ∈ Q ∧
      IsMinOn
        (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) γ xBar)
        Q
        x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) := by
  let xQ := x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar)
  let step := gradientStep f xBar γ
  have hproj : IsProjectionPointOn Q step xQ := by
    simpa [xQ, step] using
      gradientMapping_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex f γ xBar
  refine ⟨hproj.1, ?_⟩
  rw [isMinOn_iff]
  intro y hy
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hdist : ‖xQ - step‖ ≤ ‖y - step‖ :=
    isMinOn_iff.mp hproj.isMinOn y hy
  have hsq : ‖xQ - step‖ ^ (2 : ℕ) ≤ ‖y - step‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hxQ_model :
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (γ : ℝ) xBar xQ =
        f xBar + ((γ : ℝ) / 2) * ‖xQ - step‖ ^ (2 : ℕ) -
          (1 / (2 * (γ : ℝ))) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
      simpa [xQ, step, gradientStep] using
        gradient_quadratic_model_eq_completedSquare f xBar xQ hγ.ne'
  have hy_model :
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (γ : ℝ) xBar y =
        f xBar + ((γ : ℝ) / 2) * ‖y - step‖ ^ (2 : ℕ) -
          (1 / (2 * (γ : ℝ))) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
    simpa [step, gradientStep] using
      gradient_quadratic_model_eq_completedSquare f xBar y hγ.ne'
  rw [hxQ_model, hy_model]
  nlinarith [hsq, hγ]

end

/-! ### Proposition_2_35 (from Chap02) -/
/- Proposition 2.35 lies in constrained projected-gradient models on real inner-product spaces.

Owner declarations sampled for this refinement:
* `affineModelAt` in `Chap01/FirstOrderTaylorModel`, the primitive first-order model with an
  explicit gradient field;
* `firstOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the source-facing specialization using
  the totalized gradient;
* `IsProjectionPointOn.iff_isMinOn` in `Definition_2_33`, the owner bridge from distance
  minimizers to projection points;
* `IsProjectionPointOn.eq` in `Theorem_2_33`, the owner uniqueness API for projection points on a
  convex set;
* `HasFDerivAt` together with `InnerProductSpace.toDualMap`, the primitive derivative owner for an
  explicit first-order datum `g` without completeness assumptions;
* `IsLocalMinOn.hasFDerivWithinAt_nonneg` in mathlib, the owner first-order optimality API used to
  recover the projection-point inequality for the objective minimizer.

Best owner abstraction:
* `HasFDerivAt f (InnerProductSpace.toDualMap ℝ E g) tStar` together with
  `IsProjectionPointOn Q (tStar - ((γ : ℝ)⁻¹) • g) p`.

Source/core/bridge triage:
* source-facing: Proposition 2.35 in its textbook `firstOrderTaylorModelAt` form;
* core/canonical: the owner theorem below for `affineModelAt`, `HasFDerivAt`, and
  `IsProjectionPointOn`;
* bridge/view: the specialization from the explicit gradient witness to the source-facing
  `firstOrderTaylorModelAt` statement.

Primitive data:
* the feasible set `Q`, objective `f`, positive inverse-stepsize parameter `γ`, gradient
  witness `g`, and points `t0`,
  `tStar`;
* convexity of `Q`;
* feasibility and minimizing hypotheses for `t0` and `tStar`.

Derived API:
* the model minimizer `t0` is promoted to a projection point by the completed-square rewrite for
  the regularized affine model;
* the primitive derivative witness represented by `g` is fed directly to
  `IsLocalMinOn.hasFDerivWithinAt_nonneg`, and then `tStar` is promoted to the same projection
  point by the first-order optimality inequality and
  `norm_eq_iInf_iff_real_inner_le_zero`;
* convexity then identifies the two projection points.
-/

open scoped Gradient

noncomputable section

universe u

section RegularizedAffineModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : Set E} {f : E → ℝ} {g : E} {γ : NNRealˣ}

/-- Completing the square rewrites the quadratically regularized affine model at `xBar` with
constant gradient witness `g` as a constant plus a squared-distance term from the explicit step
`xBar - γ⁻¹ • g`. -/
theorem quadraticallyRegularizedObjective_affineModelAt_eq_completedSquare
    (f : E → ℝ) (g xBar x : E) (γ : NNRealˣ) :
    quadraticallyRegularizedObjective (affineModelAt f (fun _ ↦ g) xBar) (γ : ℝ) xBar x =
      f xBar + ((γ : ℝ) / 2) * ‖x - (xBar - ((γ : ℝ)⁻¹) • g)‖ ^ (2 : ℕ) -
        (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
  have hγ : (γ : ℝ) ≠ 0 := by
    exact (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))).ne'
  have hsub :
      x - (xBar - ((γ : ℝ)⁻¹) • g) = (x - xBar) + ((γ : ℝ)⁻¹) • g := by
    abel_nf
  have hsq :
      ((γ : ℝ) / 2 : ℝ) * ‖x - (xBar - ((γ : ℝ)⁻¹) • g)‖ ^ (2 : ℕ) =
        ((γ : ℝ) / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
          inner ℝ g (x - xBar) +
          (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
    calc
      ((γ : ℝ) / 2 : ℝ) * ‖x - (xBar - ((γ : ℝ)⁻¹) • g)‖ ^ (2 : ℕ)
          = ((γ : ℝ) / 2 : ℝ) *
              inner ℝ (x - (xBar - ((γ : ℝ)⁻¹) • g)) (x - (xBar - ((γ : ℝ)⁻¹) • g)) := by
                rw [real_inner_self_eq_norm_sq]
      _ = ((γ : ℝ) / 2 : ℝ) *
            inner ℝ ((x - xBar) + ((γ : ℝ)⁻¹) • g) ((x - xBar) + ((γ : ℝ)⁻¹) • g) := by
            rw [hsub]
      _ = ((γ : ℝ) / 2 : ℝ) *
            (inner ℝ (x - xBar) (x - xBar) +
              inner ℝ (x - xBar) (((γ : ℝ)⁻¹) • g) +
              inner ℝ (((γ : ℝ)⁻¹) • g) (x - xBar) +
              inner ℝ (((γ : ℝ)⁻¹) • g) (((γ : ℝ)⁻¹) • g)) := by
                rw [inner_add_add_self]
      _ = ((γ : ℝ) / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
            inner ℝ g (x - xBar) +
            (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
              rw [real_inner_self_eq_norm_sq, inner_smul_right, real_inner_smul_left,
                real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
              have hcomm : inner ℝ (x - xBar) g = inner ℝ g (x - xBar) := by
                simpa using (real_inner_comm (x - xBar) g).symm
              rw [hcomm]
              field_simp [hγ]
              ring
  rw [quadraticallyRegularizedObjective_apply, affineModelAt_apply]
  calc
    f xBar + inner ℝ g (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) =
        f xBar +
          ((((γ : ℝ) / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ)) +
            inner ℝ g (x - xBar) +
            (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ)) -
          (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
      ring
    _ = f xBar + ((γ : ℝ) / 2) * ‖x - (xBar - ((γ : ℝ)⁻¹) • g)‖ ^ (2 : ℕ) -
          (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
      rw [← hsq]

/-- Proposition 2.35 at the owner layer: if `t0 ∈ Q` minimizes the quadratically regularized
affine model determined by an explicit first-order witness `g` at `tStar`, and `tStar ∈ Q`
minimizes `f` on the convex set `Q`, then `t0 = tStar`. -/
-- Proof sketch: the completed-square identity rewrites the regularized affine model as a positive
-- multiple of the squared distance to `tStar - μ⁻¹ • g` plus a constant, so the minimizer `t0`
-- is a projection point of that explicit step onto `Q`. The minimizing property of `tStar`
-- and the primitive Fréchet derivative witness represented by `g` give the same projection-point
-- statement for `tStar` through the first-order optimality step.
-- Convexity of `Q` then gives projection uniqueness.
theorem eq_of_isMinOn_quadraticallyRegularizedObjective_affineModelAt_of_isMinOn
    (hQ_convex : Convex ℝ Q) {t0 tStar : E}
    (htStar_fderiv : HasFDerivAt f (InnerProductSpace.toDualMap ℝ E g) tStar)
    (ht0_mem : t0 ∈ Q) (htStar_mem : tStar ∈ Q)
    (ht0 : IsMinOn
      (quadraticallyRegularizedObjective (affineModelAt f (fun _ ↦ g) tStar) (γ : ℝ) tStar) Q t0)
    (htStar : IsMinOn f Q tStar) :
    t0 = tStar := by
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  let y : E := tStar - ((γ : ℝ)⁻¹) • g
  let model : E → ℝ :=
    quadraticallyRegularizedObjective (affineModelAt f (fun _ ↦ g) tStar) (γ : ℝ) tStar
  have ht0_proj : IsProjectionPointOn Q y t0 := by
    refine (IsProjectionPointOn.iff_isMinOn).2 ?_
    refine ⟨ht0_mem, ?_⟩
    rw [isMinOn_iff]
    intro x hx
    have ht0_model :
        model t0 =
          f tStar + ((γ : ℝ) / 2) * ‖t0 - y‖ ^ (2 : ℕ) -
            (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
      simpa [model, y] using
        quadraticallyRegularizedObjective_affineModelAt_eq_completedSquare f g tStar t0 γ
    have hx_model :
        model x =
          f tStar + ((γ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) -
            (1 / (2 * (γ : ℝ))) * ‖g‖ ^ (2 : ℕ) := by
      simpa [model, y] using
        quadraticallyRegularizedObjective_affineModelAt_eq_completedSquare f g tStar x γ
    have hsq : ‖t0 - y‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
      have hmin : model t0 ≤ model x := (isMinOn_iff.mp ht0) x hx
      nlinarith [hmin, ht0_model, hx_model, hγ]
    exact
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by simpa [pow_two] using hsq)
  have hvariational :
      ∀ x ∈ Q, inner ℝ (y - tStar) (x - tStar) ≤ 0 := by
    intro x hx
    have hdir : x - tStar ∈ posTangentConeAt Q tStar := by
      exact sub_mem_posTangentConeAt_of_segment_subset (hQ_convex.segment_subset htStar_mem hx)
    have hfirstOrder :=
      htStar.localize.hasFDerivWithinAt_nonneg htStar_fderiv.hasFDerivWithinAt hdir
    have hgrad : 0 ≤ inner ℝ g (x - tStar) := by
      simpa [InnerProductSpace.toDualMap_apply_apply] using hfirstOrder
    have hscaled : 0 ≤ ((γ : ℝ)⁻¹) * inner ℝ g (x - tStar) :=
      mul_nonneg (inv_nonneg.mpr hγ.le) hgrad
    simpa [y, sub_eq_add_neg, inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using
      (neg_nonpos.mpr hscaled)
  have htStar_proj : IsProjectionPointOn Q y tStar := by
    refine IsProjectionPointOn.of_norm_eq_iInf htStar_mem ?_
    exact (norm_eq_iInf_iff_real_inner_le_zero hQ_convex htStar_mem).2 hvariational
  exact ht0_proj.eq hQ_convex htStar_proj

end RegularizedAffineModel

section RegularizedTaylorModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : Set E} {f : E → ℝ} {γ : NNRealˣ}

/-- Proposition 2.35: let `tStar ∈ Q` minimize `f` on a closed convex set `Q`, and let `t0 ∈ Q`
minimize the quadratically regularized first-order Taylor model of `f` centered at `tStar`.
Then `t0 = tStar` on any complete real inner-product space; the textbook Euclidean statement is
the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: this is the source-facing specialization of the owner theorem above, taking the
-- gradient witness to be the canonical totalized gradient `∇ f tStar`.
theorem eq_of_isMinOn_quadraticallyRegularizedObjective_firstOrderTaylorModelAt_of_isMinOn
    (hQ_convex : Convex ℝ Q) {t0 tStar : E}
    (htStar_diff : DifferentiableAt ℝ f tStar)
    (ht0_mem : t0 ∈ Q) (htStar_mem : tStar ∈ Q)
    (ht0 : IsMinOn
      (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f tStar) (γ : ℝ) tStar) Q t0)
    (htStar : IsMinOn f Q tStar) :
    t0 = tStar := by
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply, firstOrderTaylorModelAt, affineModelAt]
    using
    eq_of_isMinOn_quadraticallyRegularizedObjective_affineModelAt_of_isMinOn
      hQ_convex htStar_diff.hasGradientAt.hasFDerivAt
      ht0_mem htStar_mem ht0 htStar

end RegularizedTaylorModel

end

/-! ### Theorem_2_35 (from Chap02) -/
open scoped Gradient ProjectedGradient

noncomputable section

universe u

/- Theorem 2.35 lies in constrained projected-gradient fixed points and projection optimality on
real inner-product spaces, with the textbook fixed-point statement specialized back to `ℝⁿ`.

Owner declarations sampled for this refinement:
* `IsProjectionPointOn Q y p` in `Chap07/Definition_7_3`, the owner predicate for nearest-point
  data;
* `gradientMapping` in `Definition_2_35_1`, the source-facing projected-gradient point;
* `HasGradientAt`, the canonical gradient owner predicate on real inner-product spaces;
* `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`, the chapter
  owner theorem for convex first-order optimality;
* `sub_mem_posTangentConeAt_of_segment_subset` and
  `IsLocalMinOn.hasFDerivWithinAt_nonneg`, the owner first-order optimality API for a
  differentiable minimizer on a convex feasible set;
* `norm_eq_iInf_iff_real_inner_le_zero`, the owner characterization of projection points on a
  convex set by the variational inequality.

Best owner abstraction:
* `HasGradientAt f g xStar` together with
  `IsProjectionPointOn Q (xStar - γ⁻¹ • g) xStar`.

Source/core/bridge triage:
* source-facing: Theorem 2.35 as the fixed-point statement for the textbook projected-gradient map
  on `ℝⁿ`;
* core/canonical: `IsProjectionPointOn Q (xStar - γ⁻¹ • g) xStar`;
* bridge/view: the specialization from an explicit gradient witness to the textbook gradient
  step, followed by the chosen Euclidean projection map.

Primitive data:
* the feasible set `Q`, objective `f`, minimizer `xStar`, gradient witness `g`, and positive
  inverse-stepsize parameter `γ`;
* convexity of `Q`;
* feasibility of `xStar`, optimality of `xStar` on `Q`, and a gradient witness for `f` at
  `xStar`.

Derived API:
* the owner projection-point statement for `xStar`;
* the fixed-point equality for `gradientMapping`, obtained from the chosen Euclidean projection.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable
  {Q : Set E}
  {f : E → ℝ}
  {xStar : E}
  {g : E}
  {γ : NNRealˣ}

/-- Helper for Theorem 2.35: a constrained minimizer on a convex set is the projection of the
explicit step determined by any gradient witness `g` at `xStar`. -/
theorem isProjectionPointOn_gradientStep_of_isMinOn
    (hQ_convex : Convex ℝ Q)
    (hxStar : xStar ∈ Q) (hopt : IsMinOn f Q xStar)
    (hf_grad : HasGradientAt f g xStar) :
    IsProjectionPointOn Q (xStar - ((γ : ℝ)⁻¹) • g) xStar := by
  -- Convert first-order optimality at the minimizer into the projection variational inequality
  -- for the explicit gradient step.
  have hvariational :
      ∀ x ∈ Q, inner ℝ ((xStar - ((γ : ℝ)⁻¹) • g) - xStar) (x - xStar) ≤ 0 := by
    intro x hx
    have hγ : 0 < (γ : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
    have hdir : x - xStar ∈ posTangentConeAt Q xStar := by
      exact sub_mem_posTangentConeAt_of_segment_subset (hQ_convex.segment_subset hxStar hx)
    have hfirstOrder :=
      hopt.localize.hasFDerivWithinAt_nonneg hf_grad.hasFDerivAt.hasFDerivWithinAt hdir
    have hgrad :
        0 ≤ inner ℝ g (x - xStar) := by
      simpa [hf_grad.hasFDerivAt.fderiv, innerSL_apply_apply] using hfirstOrder
    have hscaled : 0 ≤ (γ : ℝ)⁻¹ * inner ℝ g (x - xStar) :=
      mul_nonneg (inv_nonneg.mpr hγ.le) hgrad
    simpa [sub_eq_add_neg, inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using
      (neg_nonpos.mpr hscaled)
  -- Package that variational inequality into the canonical projection-point predicate.
  have hmin :
      ‖(xStar - ((γ : ℝ)⁻¹) • g) - xStar‖ =
        ⨅ w : Q, ‖(xStar - ((γ : ℝ)⁻¹) • g) - w‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hxStar).2 hvariational
  exact IsProjectionPointOn.of_norm_eq_iInf hxStar hmin

/-- Theorem 2.35: every optimal solution on a closed convex feasible set is a fixed point of the
projected-gradient mapping for every positive inverse-stepsize parameter on a complete real
inner-product space.
The textbook `ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: let `p = gradientMapping Q ⟨xStar, hxStar⟩ hQ_closed hQ_convex f xStar γ
--`. The minimizing property of `p` gives the projection variational
-- inequality, while the optimality of `xStar` and differentiability of `f` at `xStar` give the
-- first-order necessary optimality inequality at `xStar`. Evaluating these two inequalities at
-- `xStar` and `p` respectively yields `‖p - xStar‖ ^ 2 = 0`, so `p = xStar`.
theorem gradientMapping_eq_of_isMinOn
    (Q : Set E) {f : E → ℝ} {xStar : E} {γ : NNRealˣ}
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (hxStar : xStar ∈ Q) (hopt : IsMinOn f Q xStar)
    (hf_diff : DifferentiableAt ℝ f xStar) :
    x_Q[Q; ⟨xStar, hxStar⟩; hQ_closed; hQ_convex | f; γ](xStar) = xStar := by
  let hQ_nonempty : Q.Nonempty := ⟨xStar, hxStar⟩
  -- First show that the minimizer is itself a projection point of its gradient step.
  have hproj :
      IsProjectionPointOn Q (gradientStep f xStar γ) xStar :=
    by
      simpa [gradientStep] using
        isProjectionPointOn_gradientStep_of_isMinOn hQ_convex hxStar hopt hf_diff.hasGradientAt
  -- Then identify that projection point with the chosen Euclidean projection used by
  -- `gradientMapping`.
  simpa [hQ_nonempty, gradientMapping] using
    (hproj.eq_euclideanProjection hQ_nonempty hQ_closed hQ_convex).symm
end
