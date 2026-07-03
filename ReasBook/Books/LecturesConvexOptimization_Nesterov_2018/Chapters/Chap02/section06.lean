import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_6 (from Chap02) -/
open scoped Gradient SmoothConvex SeminormDualNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {L : NNReal}
variable {Q : Set E} {f : E → ℝ}

/- Definition 2.6 is a source-facing recall in first-order smooth convex analysis on a feasible
set, measured by a norm and its dual norm.

Primary domain:
* the smooth-convex owner `f ∈ 𝓕[L, p]¹¹(Q)` on a set `Q`

Sampled owner-style declarations:
* `ConvexC1On` in `Definition_2_4`, the underlying `C¹` convex owner on `Q`
* `‖g‖[p,*]` in `Definition_2_5`, the source-facing dual-norm notation
* `ConvexC1SeminormSmoothOn` in `Theorem_2_5`, the canonical owner for Definition 2.6
* `ConvexC1SeminormSmoothOn.dualNorm_gradient_sub_le` in `Theorem_2_5`, the derived gradient
  inequality API

Best owner abstraction:
* source-facing: `f ∈ 𝓕[L, p]¹¹(Q)`
* core/canonical: `ConvexC1SeminormSmoothOn p L Q f`
* bridge/view: the owner projection lemmas `.convexC1On`, `.contDiffOn`, `.convexOn`, and
  `.dualNorm_gradient_sub_le`

Primitive data:
* the feasible set `Q`
* the objective `f`
* the seminorm `p`
* the smoothness constant `L`
* the owner predicate `ConvexC1SeminormSmoothOn p L Q f`

Derived API:
* `ConvexC1SeminormSmoothOn.convexC1On`
* `ConvexC1SeminormSmoothOn.contDiffOn`
* `ConvexC1SeminormSmoothOn.convexOn`
* `ConvexC1SeminormSmoothOn.hasGradientAt`
* `ConvexC1SeminormSmoothOn.dualNorm_gradient_sub_le`

Source/core/bridge triage:
* source-facing: the textbook class `f ∈ 𝓕[L, p]¹¹(Q)`
* core/canonical: `ConvexC1SeminormSmoothOn p L Q f`
* bridge/view: the owner projections and the displayed estimate
  `‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y)`

This recall file therefore uses the chapter owner directly instead of re-expanding its defining
conjunction. No parallel local wrapper or duplicate conjunction API is kept here. -/

section

variable (p) (L) (Q) (f)

/- Definition 2.6: a function on `Q` belongs to the smooth-convex class exactly when
`f ∈ 𝓕[L, p]¹¹(Q)`, whose defining gradient clause is
`‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y)` together with the ambient gradient witness
`HasGradientAt f (∇ f x) x` on `Q`. -/
#check f ∈ 𝓕[L, p]¹¹(Q)

/- The owner predicate exposes its `C¹` convexity and smoothness projections canonically. -/
recall ConvexC1SeminormSmoothOn.convexC1On

recall ConvexC1SeminormSmoothOn.contDiffOn

recall ConvexC1SeminormSmoothOn.convexOn

recall ConvexC1SeminormSmoothOn.hasGradientAt

/- The displayed dual-norm gradient estimate is also owned canonically by the chapter predicate.
-/
recall ConvexC1SeminormSmoothOn.dualNorm_gradient_sub_le

end

/-! ### Lemma_2_6 (from Chap02) -/
/- Primary domain: strong convexity on convex subsets of `ℝⁿ` with respect to an explicit
norm-like seminorm.

Sampled owner-style declarations before refining this file:
* mathlib `UniformConvexOn.add`
* mathlib `ConvexOn.smul`
* project `StrongConvexOnWith` in `Definition_2_14`
* project `StrongConvexOnWith.nonneg_combo_inter` in `Definition_2_14`

Best owner abstraction:
* `StrongConvexOnWith p μ Q f`

Primitive data:
* the owner predicate `StrongConvexOnWith p μ Q f`

Derived API:
* `StrongConvexOnWith.nonneg_combo_inter`, which belongs with the rest of the owner API in
  `Definition_2_14`

Source/core/bridge triage:
* source-facing: the weighted-sum closure statement
* core/canonical: `StrongConvexOnWith.nonneg_combo_inter`
* bridge/view: later Euclidean specializations should reuse that owner theorem directly

This numbered item is therefore a direct owner recall, not a second declaration site.
-/

/- Lemma 2.6 is the direct owner recall of nonnegative weighted-sum closure for
`StrongConvexOnWith`. -/
recall StrongConvexOnWith.nonneg_combo_inter

/-! ### Proposition_2_6 (from Chap02) -/
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 2.6 belongs to smooth strongly convex quadratic optimization on a real Hilbert
space.

Relevant owner-style declarations sampled in this domain:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order operator owner;
* `quadraticallyRegularizedObjective` in `Chap01/FirstOrderTaylorModel`, the canonical owner for
  the centered `(\delta / 2) \|x - x_0\|^2` term;
* `IsStrongConvexSmoothObjective` and `𝓢[μ, L]¹¹` in `Chap02/Definition_2_17`, the chapter owner
  predicate and its source-facing notation;
* the finite-dimensional analogue `quadraticObjective_mem_S11` in
  `Chap02/Proposition_2_4`.

Source/core/bridge triage:
* source-facing: the quadratic objective `f_{μ,Q_f}` and its membership in `𝓢[μ, μ Q_f]¹¹`;
* core/canonical: the bounded self-adjoint operator `A : E →L[ℝ] E`, the Hessian operator
  `hessian f x`, and `IsStrongConvexSmoothObjective μ L f`;
* bridge/view: the constant Hessian formula and its Loewner lower and upper bounds.

Primitive data:
* the scalar parameters `μ`, `Q_f`;
* the bounded operator `A : E →L[ℝ] E`.

Derived API:
* the pointwise formula for `f_{μ,Q_f}`, obtained by quadratic regularization of the operator
  quadratic form at the origin;
* twice Fréchet differentiability, the constant Hessian formula, and the Loewner Hessian bounds;
* the source-facing membership statement in `𝓢[μ, μ Q_f]¹¹`.
-/

local notation "I" => ContinuousLinearMap.id ℝ E

/-- The quadratic objective `f_{μ,Q_f}` attached to a bounded operator on a real Hilbert space. -/
def nesterovQuadraticObjective (μ Q_f : ℝ) (A : E →L[ℝ] E) : E → ℝ :=
  quadraticallyRegularizedObjective
    (fun x ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x))
    μ
    (0 : E)

variable {μ Q_f : ℝ} {A : E →L[ℝ] E}

/-- Evaluating the quadratic objective expands to its defining formula. -/
@[simp] theorem nesterovQuadraticObjective_apply (x : E) :
    nesterovQuadraticObjective μ Q_f A x =
      μ * (Q_f - 1) / 8 * inner ℝ x (A x) + μ / 2 * ‖x‖ ^ (2 : ℕ) :=
  by simp [nesterovQuadraticObjective, quadraticallyRegularizedObjective]

variable [CompleteSpace E]

/-- Helper for Proposition 2.6: the gradient of the operator quadratic objective is the affine
map with linear part `((μ (Q_f - 1)) / 8) (A + A†)` and regularizing term `μ I`. -/
theorem nesterovQuadraticObjective_gradient_eq :
    ∇ (nesterovQuadraticObjective μ Q_f A) =
      fun x ↦ ((((μ * (Q_f - 1)) / 8) • (A + A.adjoint)) + μ • I) x := by
  -- Differentiate the quadratic core and the squared-norm regularizer separately.
  have hgradAt :
      ∀ x : E,
        HasGradientAt (nesterovQuadraticObjective μ Q_f A)
          (((μ * (Q_f - 1) / 8) • ((A + A.adjoint) x)) + μ • x) x := by
    intro x
    have htoDual_innerSL (z : E) : (InnerProductSpace.toDual ℝ E).symm ((innerSL ℝ) z) = z := by
      apply ext_inner_right ℝ
      intro y
      simp [InnerProductSpace.toDual_symm_apply]
    have htoDual_toDual (z : E) :
        (InnerProductSpace.toDual ℝ E).symm ((InnerProductSpace.toDual ℝ E) z) = z := by
      apply ext_inner_right ℝ
      intro y
      simp
    have hcore0 :
        HasFDerivAt (fun y : E ↦ inner ℝ y (A y))
          (innerSL ℝ ((A + A.adjoint) x)) x := by
      have hcoreCLM :
          ((fderivInnerCLM ℝ (x, A x)).comp ((1 : E →L[ℝ] E).prod A)) =
            innerSL ℝ ((A + A.adjoint) x) := by
        ext y
        calc
          ((fderivInnerCLM ℝ (x, A x)).comp ((1 : E →L[ℝ] E).prod A)) y
              = inner ℝ x (A y) + inner ℝ y (A x) := by
                  simp [fderivInnerCLM_apply]
          _ = inner ℝ y (A.adjoint x) + inner ℝ y (A x) := by
                have hAdj : inner ℝ x (A y) = inner ℝ y (A.adjoint x) := by
                  calc
                    inner ℝ x (A y) = inner ℝ (A y) x := by rw [real_inner_comm]
                    _ = inner ℝ y (A.adjoint x) := by rw [A.adjoint_inner_right]
                rw [hAdj]
          _ = inner ℝ y (A x + A.adjoint x) := by
                simpa [add_comm] using (inner_add_right y (A x) (A.adjoint x)).symm
          _ = innerSL ℝ ((A + A.adjoint) x) y := by
                simp [innerSL_apply_apply, real_inner_comm, inner_add_right]
      exact hcoreCLM ▸ ((hasFDerivAt_id x).inner ℝ A.hasFDerivAt)
    have hcore :
        HasGradientAt (fun y : E ↦ μ * (Q_f - 1) / 8 * inner ℝ y (A y))
          ((μ * (Q_f - 1) / 8) • ((A + A.adjoint) x)) x := by
      have hsmul :
          HasFDerivAt (fun y : E ↦ μ * (Q_f - 1) / 8 * inner ℝ y (A y))
            (((μ * (Q_f - 1) / 8) • innerSL ℝ ((A + A.adjoint) x)) : E →L[ℝ] ℝ) x := by
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          hcore0.const_smul (μ * (Q_f - 1) / 8)
      simpa [htoDual_innerSL, add_comm, add_left_comm, add_assoc] using hsmul.hasGradientAt
    have hnormSq :
        HasFDerivAt (fun y : E ↦ ‖y‖ ^ (2 : ℕ)) (2 • innerSL ℝ x) x := by
      simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have hreg :
        HasGradientAt (fun y : E ↦ (μ / 2) * ‖y‖ ^ (2 : ℕ)) (μ • x) x := by
      have hsmul :
          HasFDerivAt (fun y : E ↦ (μ / 2) * ‖y‖ ^ (2 : ℕ))
            ((μ / 2) • (2 • innerSL ℝ x)) x := by
        simpa [smul_eq_mul] using hnormSq.const_smul (μ / 2)
      have hlin :
          ((μ / 2) • (2 • innerSL ℝ x)) = InnerProductSpace.toDual ℝ E (μ • x) := by
        ext y
        simp [InnerProductSpace.toDual_apply_apply, two_smul]
        ring
      exact (htoDual_toDual (μ • x)) ▸ (hlin ▸ hsmul).hasGradientAt
    have hsum :
        HasGradientAt
          (fun y : E ↦
            μ * (Q_f - 1) / 8 * inner ℝ y (A y) + (μ / 2) * ‖y‖ ^ (2 : ℕ))
          (((μ * (Q_f - 1) / 8) • ((A + A.adjoint) x)) + μ • x) x := by
      simpa [add_assoc, add_left_comm, add_comm]
        using (hcore.hasFDerivAt.add hreg.hasFDerivAt).hasGradientAt
    convert hsum using 1
    funext y
    rw [nesterovQuadraticObjective_apply]
  calc
    ∇ (nesterovQuadraticObjective μ Q_f A)
        = fun x ↦ ((μ * (Q_f - 1) / 8) • ((A + A.adjoint) x)) + μ • x :=
            gradient_eq hgradAt
    _ = fun x ↦ ((((μ * (Q_f - 1)) / 8) • (A + A.adjoint)) + μ • I) x := by
          funext x
          simp [ContinuousLinearMap.add_apply]

/-- The quadratic objective is twice Fréchet differentiable, equivalently its gradient is
Fréchet differentiable on the whole Hilbert space. -/
-- Proof sketch: differentiate the quadratic form `x ↦ inner ℝ x (A x)` and the norm-square term
-- separately; both contributions are polynomial in `x`, so the gradient is differentiable
-- everywhere.
theorem nesterovQuadraticObjective_twiceDifferentiable :
    Differentiable ℝ (∇ (nesterovQuadraticObjective μ Q_f A)) := by
  -- The explicit gradient formula is a continuous linear map, hence differentiable everywhere.
  rw [nesterovQuadraticObjective_gradient_eq]
  exact ((((μ * (Q_f - 1) / 8) • (A + A.adjoint)) + μ • I) : E →L[ℝ] E).differentiable

/-- When `A` is self-adjoint, the Hessian of the quadratic objective is the constant operator
`((μ (Q_f - 1)) / 4) A + μ I`. -/
-- Proof sketch: differentiate the quadratic form `x ↦ inner ℝ x (A x)` once, use
-- self-adjointness to identify the adjoint contribution with `A`, and differentiate the
-- norm-square term to obtain the `μ I` summand.
theorem nesterovQuadraticObjective_hessian_eq (hA : IsSelfAdjoint A) (x : E) :
    hessian (nesterovQuadraticObjective μ Q_f A) x =
      ((μ * (Q_f - 1) / 4) • A) + μ • I := by
  -- Rewrite the gradient as a linear map and read off its derivative.
  let B : E →L[ℝ] E := (((μ * (Q_f - 1) / 8) • (A + A.adjoint)) + μ • I)
  have hB :
      HasFDerivAt (∇ (nesterovQuadraticObjective μ Q_f A)) B x := by
    simpa [B, nesterovQuadraticObjective_gradient_eq] using B.hasFDerivAt
  have hcollapse : B = ((μ * (Q_f - 1) / 4) • A) + μ • I := by
    have hsum : A + A.adjoint = (2 : ℝ) • A := by
      simp [hA.adjoint_eq, two_smul]
    calc
      B = (((μ * (Q_f - 1) / 8) • ((2 : ℝ) • A)) + μ • I) := by
            unfold B
            rw [hsum]
      _ = ((((μ * (Q_f - 1) / 8) * 2) • A) + μ • I) := by
            rw [smul_smul]
      _ = ((μ * (Q_f - 1) / 4) • A) + μ • I := by
            congr 1
            ring
  simpa [hessian, hcollapse] using hB.fderiv

/-- Under the Loewner assumptions `0 ≤ A` and `1 ≤ Q_f`, the Hessian is bounded below by
`μ I`. -/
-- Proof sketch: combine the constant Hessian formula with `0 ≤ A` and `1 ≤ Q_f` to see that the
-- perturbation term `((μ (Q_f - 1)) / 4) • A` is positive semidefinite, then add `μ I`.
theorem nesterovQuadraticObjective_hessian_lower_bound
    (hμ : 0 ≤ μ) (hQf : 1 ≤ Q_f) (hA_nonneg : 0 ≤ A) (x : E) :
    μ • I ≤ hessian (nesterovQuadraticObjective μ Q_f A) x := by
  -- Positivity of `A` makes the scaled perturbation term positive semidefinite.
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA_nonneg
  have hA_self : IsSelfAdjoint A := by
    rw [ContinuousLinearMap.isPositive_iff'] at hA_pos
    exact hA_pos.1
  have hcoeff : 0 ≤ μ * (Q_f - 1) / 4 := by
    nlinarith
  rw [nesterovQuadraticObjective_hessian_eq hA_self x, ContinuousLinearMap.le_def]
  simpa using hA_pos.smul_of_nonneg hcoeff

/-- Under the Loewner assumption `A ≤ 4 I`, the Hessian is bounded above by `(μ Q_f) I`. -/
-- Proof sketch: rewrite the Hessian by `nesterovQuadraticObjective_hessian_eq`, use
-- `hA_le : A ≤ 4 I` to bound the perturbation term by `μ (Q_f - 1) I`, and simplify the scalar
-- factor to obtain the upper bound `(μ Q_f) I`.
theorem nesterovQuadraticObjective_hessian_upper_bound
    (hμ : 0 ≤ μ) (hQf : 1 ≤ Q_f)
    (hA_le : A ≤ (4 : ℝ) • I) (x : E) :
    hessian (nesterovQuadraticObjective μ Q_f A) x ≤ (μ * Q_f) • I := by
  -- Rewrite the gap to the upper bound as a nonnegative scalar multiple of `4 I - A`.
  have hshift_pos : (((4 : ℝ) • I) - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hA_le
  have hshift_self : IsSelfAdjoint (((4 : ℝ) • I) - A) := by
    rw [ContinuousLinearMap.isPositive_iff'] at hshift_pos
    exact hshift_pos.1
  have hI_self : IsSelfAdjoint ((4 : ℝ) • I : E →L[ℝ] E) := by
    have hpos : (((4 : ℝ) • (I : E →L[ℝ] E)) : E →L[ℝ] E).IsPositive :=
      ContinuousLinearMap.isPositive_one.smul_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num)
    rw [ContinuousLinearMap.isPositive_iff'] at hpos
    exact hpos.1
  have hA_self : IsSelfAdjoint A := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hI_self.sub hshift_self
  have hcoeff : 0 ≤ μ * (Q_f - 1) / 4 := by
    nlinarith
  have hshift_scaled :
      (((μ * Q_f) • I) - (((μ * (Q_f - 1) / 4) • A) + μ • I)).IsPositive := by
    have hbase :
        (((μ * (Q_f - 1) / 4) • (((4 : ℝ) • I) - A)) : E →L[ℝ] E).IsPositive :=
      hshift_pos.smul_of_nonneg hcoeff
    have hrewrite :
        (((μ * Q_f) • I) - (((μ * (Q_f - 1) / 4) • A) + μ • I)) =
          ((μ * (Q_f - 1) / 4) • (((4 : ℝ) • I) - A)) := by
      calc
        (((μ * Q_f) • I) - (((μ * (Q_f - 1) / 4) • A) + μ • I))
            = (((μ * Q_f) • I - μ • I) - ((μ * (Q_f - 1) / 4) • A)) := by
                abel_nf
        _ = ((μ * (Q_f - 1)) • I - ((μ * (Q_f - 1) / 4) • A)) := by
              rw [← sub_smul]
              congr 1
              ring
        _ = (((μ * (Q_f - 1) / 4) • ((4 : ℝ) • I)) - ((μ * (Q_f - 1) / 4) • A)) := by
              congr 1
              rw [smul_smul]
              congr 1
              ring
        _ = ((μ * (Q_f - 1) / 4) • (((4 : ℝ) • I) - A)) := by
              rw [smul_sub]
    exact hrewrite ▸ hbase
  rw [ContinuousLinearMap.le_def]
  rw [nesterovQuadraticObjective_hessian_eq hA_self x]
  simpa using hshift_scaled

/-- Helper for Proposition 2.6: the constant Hessian operator has norm at most `μ Q_f` under the
Loewner bounds `0 ≤ A ≤ 4 I`. -/
lemma nesterovQuadraticObjective_hessian_operator_norm_le
    (hμ : 0 ≤ μ) (hQf : 1 ≤ Q_f) (hA_nonneg : 0 ≤ A) (hA_le : A ≤ (4 : ℝ) • I) :
    ‖((μ * (Q_f - 1) / 4) • A) + μ • I‖ ≤ μ * Q_f := by
  -- The Hessian is self-adjoint and squeezed between `0` and `(μ Q_f) I`, so Rayleigh quotients
  -- control its operator norm exactly as in the finite-dimensional quadratic case.
  let B : E →L[ℝ] E := ((μ * (Q_f - 1) / 4) • A) + μ • I
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA_nonneg
  have hA_self : IsSelfAdjoint A := by
    rw [ContinuousLinearMap.isPositive_iff'] at hA_pos
    exact hA_pos.1
  have hB_eq : hessian (nesterovQuadraticObjective μ Q_f A) (0 : E) = B := by
    simpa [B] using
      nesterovQuadraticObjective_hessian_eq
        (μ := μ) (Q_f := Q_f) (A := A) hA_self (0 : E)
  have hB_lower : μ • I ≤ B := by
    rw [← hB_eq]
    exact nesterovQuadraticObjective_hessian_lower_bound
      (μ := μ) (Q_f := Q_f) (A := A) hμ hQf hA_nonneg (0 : E)
  have hB_nonneg : (0 : E →L[ℝ] E) ≤ B := by
    have hμI_nonneg : (0 : E →L[ℝ] E) ≤ μ • I := by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      simpa using ContinuousLinearMap.isPositive_one.smul_of_nonneg hμ
    exact le_trans hμI_nonneg hB_lower
  have hB_le : B ≤ (μ * Q_f) • I := by
    rw [← hB_eq]
    exact nesterovQuadraticObjective_hessian_upper_bound
      (μ := μ) (Q_f := Q_f) (A := A) hμ hQf hA_le (0 : E)
  have hB_symm : (B : E →ₗ[ℝ] E).IsSymmetric := by
    have hB_pos : B.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive B).mp hB_nonneg
    rw [ContinuousLinearMap.isPositive_iff'] at hB_pos
    simpa using hB_pos.1.isSymmetric
  have hL_nonneg : 0 ≤ μ * Q_f := by
    nlinarith
  have hbound : ∀ z : E, |B.rayleighQuotient z| ≤ μ * Q_f := by
    intro z
    by_cases hz : z = 0
    · simpa [hz] using hL_nonneg
    · have hz_norm_sq_pos : 0 < ‖z‖ ^ (2 : ℕ) := by
        positivity
      have hLI_pos : (((μ * Q_f) • I) - B).IsPositive := by
        simpa [ContinuousLinearMap.le_def] using hB_le
      have hquad : inner ℝ (B z) z ≤ (μ * Q_f) * ‖z‖ ^ (2 : ℕ) := by
        have hnonneg := hLI_pos.inner_nonneg_left z
        simpa [inner_smul_left, inner_sub_left, inner_self_eq_norm_sq_to_K, mul_assoc,
          mul_left_comm, mul_comm] using hnonneg
      have hnonneg : 0 ≤ inner ℝ (B z) z :=
        ((ContinuousLinearMap.nonneg_iff_isPositive _).1 hB_nonneg).inner_nonneg_left z
      rw [ContinuousLinearMap.rayleighQuotient, abs_of_nonneg]
      · exact (div_le_iff₀ hz_norm_sq_pos).2 hquad
      · exact div_nonneg hnonneg hz_norm_sq_pos.le
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient B hB_symm]
  exact ciSup_le hbound

/-- Proposition 2.6: if `μ > 0`, `1 ≤ Q_f`, and `0 ≤ A ≤ 4 I` in the Loewner order, then the
quadratic objective `f_{μ,Q_f}` belongs to the source class `𝓢[μ, μ * Q_f]¹¹`; in particular its
condition number parameter is `Q_f`. -/
-- Proof sketch: use `nesterovQuadraticObjective_twiceDifferentiable` and the two Loewner Hessian
-- bounds to obtain `μ`-strong convexity and `(μ Q_f)`-Lipschitz gradient, then package these
-- data in the chapter owner predicate and rewrite through the source-facing notation `𝓢[μ, L]¹¹`.
theorem nesterovQuadraticObjective_mem_S11
    (hμ : 0 < μ) (hQf : 1 ≤ Q_f)
    (hA_nonneg : 0 ≤ A) (hA_le : A ≤ (4 : ℝ) • I) :
    nesterovQuadraticObjective μ Q_f A ∈ 𝓢[μ, μ * Q_f]¹¹ := by
  -- The positive operator assumption gives both convexity of the quadratic perturbation and
  -- self-adjointness of `A`.
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA_nonneg
  have hA_self : IsSelfAdjoint A := by
    rw [ContinuousLinearMap.isPositive_iff'] at hA_pos
    exact hA_pos.1
  have hcoeff_nonneg : 0 ≤ μ * (Q_f - 1) / 4 := by
    nlinarith
  have hquad_convex0 :
      ConvexOn ℝ Set.univ
        (fun x : E ↦
          (1 / 2 : ℝ) * inner ℝ ((((μ * (Q_f - 1) / 4) : ℝ) • A) x) x) :=
    LinearMap.IsPositive.convexOn_half_inner_map_self (hA_pos.smul_of_nonneg hcoeff_nonneg)
  have hquad_convex :
      ConvexOn ℝ Set.univ (fun x : E ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x)) := by
    refine hquad_convex0.congr ?_
    intro x hx
    calc
      (1 / 2 : ℝ) * inner ℝ ((((μ * (Q_f - 1) / 4) : ℝ) • A) x) x
          = (1 / 2 : ℝ) * ((μ * (Q_f - 1) / 4) * inner ℝ (A x) x) := by
              simp [inner_smul_left]
      _ = μ * (Q_f - 1) / 8 * inner ℝ x (A x) := by
            rw [real_inner_comm]
            ring
  have hstrong0 :
      StrongConvexOn Set.univ μ
        ((fun x : E ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x)) +
          quadraticallyRegularizedObjective (fun _ : E ↦ 0) μ (0 : E)) :=
    StrongConvexOn.add_convexOn
      (quadraticallyRegularizedObjective_zero_strongConvexOn (0 : E) μ)
      hquad_convex
  have hsplit :
      nesterovQuadraticObjective μ Q_f A =
        (fun x : E ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x)) +
          quadraticallyRegularizedObjective (fun _ : E ↦ 0) μ (0 : E) := by
    funext x
    simp [nesterovQuadraticObjective, quadraticallyRegularizedObjective]
  have hstrong : StrongConvexOn Set.univ μ (nesterovQuadraticObjective μ Q_f A) := by
    exact hsplit.symm ▸ hstrong0
  have hcont_quad :
      ContDiff ℝ 1 (fun x : E ↦ μ * (Q_f - 1) / 8 * inner ℝ x (A x)) := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      contDiff_const.mul (contDiff_id.inner ℝ A.contDiff)
  have hcont_reg : ContDiff ℝ 1 (fun x : E ↦ (μ / 2) * ‖x‖ ^ (2 : ℕ)) := by
    simpa [smul_eq_mul] using (contDiff_norm_sq ℝ).const_smul (μ / 2)
  have hcont : ContDiff ℝ 1 (nesterovQuadraticObjective μ Q_f A) := by
    convert hcont_quad.add hcont_reg using 1
    funext x
    rw [nesterovQuadraticObjective_apply]
  let B : E →L[ℝ] E := ((μ * (Q_f - 1) / 4) • A) + μ • I
  have hcollapse :
      ((((μ * (Q_f - 1) / 8) • (A + A.adjoint)) + μ • I) : E →L[ℝ] E) = B := by
    have hsum : A + A.adjoint = (2 : ℝ) • A := by
      simp [hA_self.adjoint_eq, two_smul]
    calc
      ((((μ * (Q_f - 1) / 8) • (A + A.adjoint)) + μ • I) : E →L[ℝ] E)
          = (((μ * (Q_f - 1) / 8) • ((2 : ℝ) • A)) + μ • I) := by
              rw [hsum]
      _ = ((((μ * (Q_f - 1) / 8) * 2) • A) + μ • I) := by
            rw [smul_smul]
      _ = B := by
            unfold B
            congr 1
            ring
  have hgrad_eq : ∇ (nesterovQuadraticObjective μ Q_f A) = fun x ↦ B x := by
    rw [nesterovQuadraticObjective_gradient_eq]
    exact congrArg (fun T : E →L[ℝ] E => fun x : E ↦ T x) hcollapse
  have hBnorm : ‖B‖ ≤ μ * Q_f :=
    nesterovQuadraticObjective_hessian_operator_norm_le
      (μ := μ) (Q_f := Q_f) (A := A) hμ.le hQf hA_nonneg hA_le
  have hnnorm : (‖B‖₊ : ℝ) ≤ μ * Q_f := by
    exact_mod_cast hBnorm
  have hgrad_lip : ∀ x y : E,
      ‖∇ (nesterovQuadraticObjective μ Q_f A) x -
          ∇ (nesterovQuadraticObjective μ Q_f A) y‖ ≤
        (μ * Q_f) * ‖x - y‖ := by
    intro x y
    simpa [hgrad_eq] using
      (B.lipschitz.norm_sub_le x y).trans <|
        mul_le_mul_of_nonneg_right hnnorm (norm_nonneg _)
  exact mem_S11_iff.mpr ⟨hμ, hcont, hstrong, hgrad_lip⟩

/-! ### Theorem_2_6 (from Chap02) -/
open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/- Primary domain: twice continuously differentiable smooth convex analysis on finite-dimensional
real inner-product spaces with seminorm-controlled gradient smoothness.

Relevant owner-style declarations sampled before refining this file:
* `ConvexC1On` in `Definition_2_4`
* `𝓕[L, p]¹¹` in `Theorem_2_5`
* `convexOn_iff_hessian_quadratic_form_nonneg` in `Theorem_2_4`

Source/core/bridge triage:
* source-facing: `f ∈ 𝓕[L, p]¹¹`
* core/canonical: `ConvexOn ℝ Set.univ f` together with the upper Hessian quadratic-form bound
* bridge/view: the owner theorem
  `ConvexC1SeminormSmooth.hessian_quadratic_form_upper_bound` and the explicit lower-and-upper
  Hessian quadratic-form inequalities in
  `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded`

The owner abstraction here is `f ∈ 𝓕[L, p]¹¹`.
Primitive data: the whole-space `C¹` convexity owner `ConvexC1On Set.univ f` and the defining
dual-norm Lipschitz bound for `∇ f`.
Derived API: `hf.contDiff`, `hf.convexOn`, `hf.dualNorm_gradient_sub_le`, and via Theorem 2.4 the
nonnegativity of the Hessian quadratic form. The only genuinely new second-order ingredient here
is the upper bound `inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2`. This matches the textbook
`ℝⁿ` setting through the chapter owner `𝓕[L, p]¹¹`, rather than over-generalizing beyond the
available first-order owner layer. -/

section

variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {L : NNReal} {f : E → ℝ}

open scoped SeminormDualNorm

open InnerProductSpace

/-- Helper for Theorem 2.6: the dual pairing with `x` is controlled in absolute value by the
dual seminorm of `g` times `p x`. -/
private theorem abs_inner_le_dualNorm_mul (x g : E) :
    |inner ℝ g x| ≤ ‖g‖[p,*] * p x := by
  -- Bound the positive and negative parts separately using the dual Cauchy--Schwarz inequality.
  refine abs_le.mpr ?_
  constructor
  · have hneg : -inner ℝ g x ≤ ‖g‖[p,*] * p x := by
      simpa using (Seminorm.inner_le_dualNorm_mul p (-x) g)
    nlinarith
  · exact Seminorm.inner_le_dualNorm_mul p x g

/-- Helper for Theorem 2.6: the affine line `s ↦ x + s • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 2.6: scalarizing the gradient along a line differentiates to the Hessian
pairing. -/
private theorem scalarized_gradient_line_hasDerivAt
    (hf_C2 : ContDiff ℝ 2 f) (x d u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) u)
      (inner ℝ (hessian f (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) (x + t • d) := by
    -- A `C²` function has a differentiable Fréchet derivative field.
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • d) :=
      (hf_C2.contDiffAt (x := x + t • d)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ f) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map to differentiate it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (x + s • d))
        ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the derivative of the gradient with the derivative of the affine line.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (x + s • d)))
        (φ.comp ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional `v ↦ ⟪v, u⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 2.6: a positive operator with a diagonal quadratic-form bound also controls
mixed pairings. -/
private theorem mixed_pairing_le_of_isPositive_and_quadratic_form_bound
    {A : E →L[ℝ] E}
    (hApos : A.IsPositive)
    (hAupper : ∀ v : E, inner ℝ (A v) v ≤ (L : ℝ) * (p v) ^ 2) :
    ∀ d u : E, |inner ℝ (A d) u| ≤ (L : ℝ) * p d * p u := by
  intro d u
  let a : ℝ := inner ℝ (A u) u
  let b : ℝ := 2 * inner ℝ (A d) u
  let c : ℝ := inner ℝ (A d) d
  have hpoly : ∀ α : ℝ, 0 ≤ a * (α * α) + b * α + c := by
    intro α
    have hnonneg := hApos.inner_nonneg_left (d + α • u)
    -- Expand the positive quadratic form on `d + α u` to a scalar quadratic in `α`.
    rw [show inner ℝ (A (d + α • u)) (d + α • u) = a * (α * α) + b * α + c by
      dsimp [a, b, c]
      calc
        inner ℝ (A (d + α • u)) (d + α • u)
            = inner ℝ (A d + α • A u) (d + α • u) := by simp [map_add, map_smul]
        _ = (inner ℝ (A d) d + inner ℝ (A d) (α • u)) +
              (inner ℝ (α • A u) d + inner ℝ (α • A u) (α • u)) := by
              rw [inner_add_right, inner_add_left, inner_add_left]
              ring
        _ = inner ℝ (A d) d + inner ℝ (A d) (α • u) +
              inner ℝ (α • A u) d + inner ℝ (α • A u) (α • u) := by
              ring_nf
        _ = inner ℝ (A d) d + α * inner ℝ (A d) u + α * inner ℝ (A u) d +
              (α * α) * inner ℝ (A u) u := by
              simp [real_inner_smul_right, real_inner_smul_left, mul_assoc]
        _ = inner ℝ (A d) d + α * inner ℝ (A d) u + α * inner ℝ (A d) u +
              (α * α) * inner ℝ (A u) u := by
              rw [show inner ℝ (A u) d = inner ℝ (A d) u by
                calc
                  inner ℝ (A u) d = inner ℝ u (A d) := hApos.inner_left_eq_inner_right _ _
                  _ = inner ℝ (A d) u := by simpa [real_inner_comm]]
        _ = a * (α * α) + b * α + c := by
              dsimp [a, b, c]
              ring] at hnonneg
    exact hnonneg
  have hdiscr : discrim a b c ≤ 0 := discrim_le_zero hpoly
  have hsq : (inner ℝ (A d) u) ^ 2 ≤ a * c := by
    -- Nonpositive discriminant gives the Cauchy--Schwarz bound for the positive form.
    rw [discrim, sq] at hdiscr
    dsimp [b] at hdiscr
    nlinarith
  have hbound_sq : (inner ℝ (A d) u) ^ 2 ≤ ((L : ℝ) * p d * p u) ^ 2 := by
    have hd : c ≤ (L : ℝ) * (p d) ^ 2 := by
      simpa [c] using hAupper d
    have hu : a ≤ (L : ℝ) * (p u) ^ 2 := by
      simpa [a] using hAupper u
    have ha_nonneg : 0 ≤ a := by
      simpa [a] using hApos.inner_nonneg_left u
    have hc_nonneg : 0 ≤ c := by
      simpa [c] using hApos.inner_nonneg_left d
    nlinarith
  have habs_sq : |inner ℝ (A d) u| ^ 2 ≤ ((L : ℝ) * p d * p u) ^ 2 := by
    simpa [sq_abs] using hbound_sq
  have hRnonneg : 0 ≤ (L : ℝ) * p d * p u := by positivity
  -- Take square roots in the ordered-field sense to recover the absolute-value estimate.
  nlinarith [abs_nonneg (inner ℝ (A d) u), hRnonneg, habs_sq]

/-- Helper for Theorem 2.6: a uniform pairing bound on the `p`-unit ball gives the dual-norm
bound. -/
private theorem dualNorm_le_of_unit_ball_pairing_bound {g : E} {C : ℝ}
    (hC : ∀ u : E, p u ≤ 1 → inner ℝ g u ≤ C) :
    ‖g‖[p,*] ≤ C := by
  -- Unfold the dual norm as the support function of the closed `p`-unit ball.
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · refine ⟨(0 : ℝ), ?_⟩
    refine ⟨(0 : E), ?_⟩
    constructor <;> simp
  · rintro y ⟨u, hu, rfl⟩
    exact hC u hu

/- Core/canonical layer: after Theorem 2.4 identifies convexity on the ambient real
finite-dimensional inner-product space with nonnegativity of the Hessian quadratic form, the only
extra second-order content of Theorem 2.6 is the upper quadratic bound. -/
namespace ConvexC1SeminormSmooth

/-- For a twice continuously differentiable smooth-convex objective, every Hessian quadratic form
is bounded above by the smoothness constant times `p(h)^2`. -/
theorem hessian_quadratic_form_upper_bound
    (hf : f ∈ 𝓕[L, p]¹¹) (hf_C2 : ContDiff ℝ 2 f) (x h : E) :
    inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 := by
  have hconvex_iff :
      ConvexOn ℝ Set.univ f ↔
        ∀ z ∈ Set.univ, ∀ v : E, 0 ≤ inner ℝ (hessian f z v) v :=
    convexOn_iff_hessian_quadratic_form_nonneg isOpen_univ convex_univ hf_C2.contDiffOn
  have hnonneg : 0 ≤ inner ℝ (hessian f x h) h := by
    -- The lower bound is exactly the Theorem 2.4 convexity-to-Hessian bridge.
    exact (hconvex_iff.mp hf.convexOn) x (Set.mem_univ x) h
  let φ : ℝ → ℝ := fun s ↦ inner ℝ (∇ f (x + s • h)) h
  have hφ_lip : LipschitzWith ⟨(L : ℝ) * (p h) ^ 2, by positivity⟩ φ := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro s t
    have hpair :=
      abs_inner_le_dualNorm_mul (p := p) h (∇ f (x + s • h) - ∇ f (x + t • h))
    have hgrad := hf.dualNorm_gradient_sub_le (x + s • h) (x + t • h)
    -- The defining gradient-Lipschitz inequality makes the scalarized line restriction Lipschitz.
    calc
      dist (φ s) (φ t)
          = |inner ℝ (∇ f (x + s • h) - ∇ f (x + t • h)) h| := by
              simp [φ, dist_eq_norm, inner_sub_left]
      _ ≤ ‖∇ f (x + s • h) - ∇ f (x + t • h)‖[p,*] * p h := hpair
      _ ≤ ((L : ℝ) * p ((x + s • h) - (x + t • h))) * p h := by
            gcongr
      _ = ((L : ℝ) * (|s - t| * p h)) * p h := by
            rw [show p ((x + s • h) - (x + t • h)) = |s - t| * p h by
              calc
                p ((x + s • h) - (x + t • h)) = p ((s - t) • h) := by
                  congr
                  calc
                    (x + s • h) - (x + t • h) = s • h - t • h := by abel_nf
                    _ = (s - t) • h := by rw [sub_smul]
                _ = |s - t| * p h := by simpa [Real.norm_eq_abs] using (map_smul_eq_mul p (s - t) h)]
      _ = ((L : ℝ) * (p h) ^ 2) * dist s t := by
            rw [Real.dist_eq]
            ring_nf
  have hderiv := scalarized_gradient_line_hasDerivAt (f := f) hf_C2 x h h 0
  have hderiv_bound : |deriv φ 0| ≤ (L : ℝ) * (p h) ^ 2 := by
    -- A Lipschitz scalar function has derivative bounded by the same Lipschitz constant.
    simpa [φ, Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := 0) hφ_lip
  have hderiv_eq : deriv φ 0 = inner ℝ (hessian f x h) h := by
    -- Identify the derivative of the line restriction with the Hessian quadratic form.
    simpa [φ] using hderiv.deriv
  rw [hderiv_eq] at hderiv_bound
  exact (abs_le.mp hderiv_bound).2

/-- Conversely, a twice continuously differentiable convex objective whose Hessian quadratic form
is bounded above by `L * p(h)^2` belongs to `𝓕[L, p]¹¹`. -/
theorem of_convexOn_hessian_quadratic_form_upper_bound
    (hf_C2 : ContDiff ℝ 2 f) (hconvex : ConvexOn ℝ Set.univ f)
    (hupper : ∀ x h : E,
      inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2) :
    f ∈ 𝓕[L, p]¹¹ := by
  have hconvex_iff :
      ConvexOn ℝ Set.univ f ↔
        ∀ z ∈ Set.univ, ∀ v : E, 0 ≤ inner ℝ (hessian f z v) v :=
    convexOn_iff_hessian_quadratic_form_nonneg isOpen_univ convex_univ hf_C2.contDiffOn
  have hnonneg : ∀ z v : E, 0 ≤ inner ℝ (hessian f z v) v := by
    -- Convexity gives pointwise positivity of the Hessian quadratic form.
    intro z v
    exact (hconvex_iff.mp hconvex) z (Set.mem_univ z) v
  have hpos : ∀ z : E, (hessian f z).IsPositive := by
    intro z
    -- Package the quadratic-form nonnegativity as positivity of the Hessian operator.
    exact (ContinuousLinearMap.isPositive_iff _).2
      ⟨fderiv_gradient_isSymmetric_of_contDiffAt (hf_C2.contDiffAt (x := z)), hnonneg z⟩
  let hf_C1 : ContDiff ℝ 1 f := hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  refine ⟨⟨hf_C1.contDiffOn, hconvex⟩, ?_, ?_⟩
  · intro x hx
    -- The `C²` hypothesis supplies the ambient gradient witness required by `𝓕[L, p]¹¹`.
    exact (hf_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) x).hasGradientAt
  · intro x hx y hy
    let d : E := x - y
    have hpair_bound :
        ∀ u : E, p u ≤ 1 → inner ℝ (∇ f x - ∇ f y) u ≤ (L : ℝ) * p d := by
      intro u hu
      let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (y + t • d)) u
      have hψ_deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivWithinAt ψ (inner ℝ (hessian f (y + t • d) d) u) (Set.Icc (0 : ℝ) 1) t := by
        intro t ht
        -- Differentiate the scalarized gradient along the segment from `x` to `y`.
        exact (scalarized_gradient_line_hasDerivAt (f := f) hf_C2 y d u t).hasDerivWithinAt
      have hψ_bound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
          ‖inner ℝ (hessian f (y + t • d) d) u‖ ≤ (L : ℝ) * p d := by
        intro t ht
        have hmixed := mixed_pairing_le_of_isPositive_and_quadratic_form_bound (p := p) (L := L)
          (hpos (y + t • d)) (hupper (y + t • d)) d u
        have hpu_le : (L : ℝ) * p d * p u ≤ (L : ℝ) * p d := by
          have hd_nonneg : 0 ≤ p d := by positivity
          have hL_nonneg : 0 ≤ (L : ℝ) := by positivity
          have hmul : p d * p u ≤ p d := by
            calc
              p d * p u ≤ p d * 1 := by
                gcongr
              _ = p d := by ring
          nlinarith
        exact hmixed.trans hpu_le
      have hsegment := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := ψ) hψ_deriv hψ_bound
      have hrewrite : ψ 1 - ψ 0 = inner ℝ (∇ f x - ∇ f y) u := by
        simp [ψ, d, inner_sub_left]
      have habs : |inner ℝ (∇ f x - ∇ f y) u| ≤ (L : ℝ) * p d := by
        -- Integrate the derivative bound along the segment to control the endpoint pairing.
        simpa [Real.dist_eq, dist_eq_norm, hrewrite] using hsegment
      exact (abs_le.mp habs).2
    -- Convert the unit-ball pairing bound into the dual-norm Lipschitz estimate.
    simpa [d] using dualNorm_le_of_unit_ball_pairing_bound (p := p) hpair_bound

end ConvexC1SeminormSmooth

/-- Theorem 2.6: for a twice continuously differentiable function on a finite-dimensional real
inner-product space,
belonging to `𝓕[L, p]¹¹` is equivalent to the Hessian quadratic form being
nonnegative and bounded above by `L * p(h)^2` in every direction. The textbook `ℝⁿ` statement is
the finite-dimensional specialization. -/
-- Proof sketch: the owner theorem
-- `ConvexC1SeminormSmooth.hessian_quadratic_form_upper_bound` isolates the genuinely new
-- second-order content, namely the upper Hessian quadratic-form bound. The lower bound is
-- exactly the Theorem 2.4 bridge from convexity of `f` on `Set.univ` to nonnegativity of the
-- Hessian quadratic form.
theorem convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded
    (hf_C2 : ContDiff ℝ 2 f) :
    f ∈ 𝓕[L, p]¹¹ ↔
      ∀ x h : E,
        0 ≤ inner ℝ (hessian f x h) h ∧
          inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 := by
  have hconvex_iff :
      ConvexOn ℝ Set.univ f ↔
        ∀ x ∈ Set.univ, ∀ h : E, 0 ≤ inner ℝ (hessian f x h) h :=
    convexOn_iff_hessian_quadratic_form_nonneg isOpen_univ convex_univ hf_C2.contDiffOn
  constructor
  · intro hf x h
    exact
      ⟨(hconvex_iff.mp hf.convexOn) x (Set.mem_univ x) h,
        ConvexC1SeminormSmooth.hessian_quadratic_form_upper_bound hf hf_C2 x h⟩
  · intro hquad
    have hconvex : ConvexOn ℝ Set.univ f := by
      refine hconvex_iff.mpr ?_
      intro x hx h'
      simpa using (hquad x h').1
    exact
      ConvexC1SeminormSmooth.of_convexOn_hessian_quadratic_form_upper_bound
        hf_C2 hconvex (fun x h ↦ (hquad x h).2)

end

end
