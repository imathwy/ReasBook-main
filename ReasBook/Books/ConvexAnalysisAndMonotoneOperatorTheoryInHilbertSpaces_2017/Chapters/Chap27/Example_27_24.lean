import Mathlib
import BauschkeLean.Chap03.Proposition_3_30
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap11.Proposition_11_12
import BauschkeLean.Chap10.Example_10_9
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap17.Proposition_17_6
import BauschkeLean.Chap24.Example_24_2
import BauschkeLean.Chap27.Theorem_27_23

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open ContinuousLinearMap
open scoped ContinuousLinearMap InnerProductSpace Pointwise Topology

universe u v

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

/-- Helper for Example 27.24: the Chapter 24 quadratic owner for the least-squares objective
`x ↦ ‖L x - y‖² / 2`. -/
noncomputable abbrev leastSquaresQuadraticOwner (L : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) :
    𝓗 → Set.Ioi (⊥ : EReal) :=
  ERealFunction.example_24_2_function (L.adjoint.comp L) (-(L.adjoint y)) (‖y‖ ^ 2 / 2)

/-- Helper for Example 27.24: the Chapter 24 quadratic owner evaluates to the least-squares
functional `x ↦ ‖L x - y‖² / 2`. -/
lemma least_squares_quadratic_owner_apply
    (L : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) (x : 𝓗) :
    ((leastSquaresQuadraticOwner L y) x : EReal) =
      ((((‖L x - y‖ ^ 2) / 2 : ℝ) : EReal)) := by
  -- Rewrite the quadratic owner through the Gram term and the adjoint pairing.
  rw [leastSquaresQuadraticOwner, ERealFunction.example_24_2_function_apply]
  rw [ContinuousLinearMap.comp_apply]
  have hgram : ⟪(L.adjoint) (L x), x⟫_ℝ = ‖L x‖ ^ 2 := by
    simpa using (L.apply_norm_sq_eq_inner_adjoint_left x).symm
  have hadj : ⟪x, -(L.adjoint y)⟫_ℝ = -⟪L x, y⟫_ℝ := by
    simpa using congrArg Neg.neg (ContinuousLinearMap.adjoint_inner_right (A := L) x y)
  -- Expand the residual square and normalize the scalar coefficients.
  have hsq : ‖L x - y‖ ^ 2 = ‖L x‖ ^ 2 - 2 * ⟪L x, y⟫_ℝ + ‖y‖ ^ 2 := by
    simpa using norm_sub_sq_real (L x) y
  rw [hgram, hadj, hsq]
  ring_nf

/-- Helper for Example 27.24: the least-squares minimizers are exactly the Moore-Penrose
solution set of the normal equation. -/
lemma argmin_least_squares_quadratic_owner_eq_moore_penrose_solution_set
    (L : 𝓗 →L[ℝ] 𝓚) (hL_closed : IsClosed (L.range : Set 𝓚)) (y : 𝓚) :
    Argmin (leastSquaresQuadraticOwner L y).asEReal = moorePenroseSolutionSet L y := by
  ext x
  constructor
  · intro hx
    rw [mem_moorePenroseSolutionSet_iff]
    have hleast : IsLeastSquaresSolution L y x := by
      -- Convert global minimality of the quadratic owner into least-squares optimality.
      rw [ERealFunction.mem_argmin_iff, isMinOn_univ_iff] at hx
      rw [isLeastSquaresSolution_iff]
      intro z
      have hxz := hx z
      have hquad :
          ((((‖L x - y‖ ^ 2) / 2 : ℝ) : EReal)) ≤
            ((((‖L z - y‖ ^ 2) / 2 : ℝ) : EReal)) := by
        rw [Function.asEReal_apply, least_squares_quadratic_owner_apply L y x,
          Function.asEReal_apply, least_squares_quadratic_owner_apply L y z] at hxz
        exact hxz
      have hsq : (‖L x - y‖ ^ 2) / 2 ≤ (‖L z - y‖ ^ 2) / 2 := by
        exact_mod_cast hquad
      nlinarith [norm_nonneg (L x - y), norm_nonneg (L z - y)]
    have htfae := (leastSquares_tfae_and_exists_of_closed_range L hL_closed y).2 x
    exact (List.TFAE.out htfae 0 2).mp hleast
  · intro hx
    have htfae := (leastSquares_tfae_and_exists_of_closed_range L hL_closed y).2 x
    have hleast : IsLeastSquaresSolution L y x := by
      -- The normal equation is the third clause of Proposition 3.27.
      exact (List.TFAE.out htfae 2 0).mp ((mem_moorePenroseSolutionSet_iff L y x).mp hx)
    rw [ERealFunction.mem_argmin_iff, isMinOn_univ_iff]
    intro z
    have hnorm : ‖L x - y‖ ≤ ‖L z - y‖ := hleast z
    have hsq : (‖L x - y‖ ^ 2) / 2 ≤ (‖L z - y‖ ^ 2) / 2 := by
      nlinarith [hnorm, norm_nonneg (L x - y), norm_nonneg (L z - y)]
    have hquad :
        ((((‖L x - y‖ ^ 2) / 2 : ℝ) : EReal)) ≤
          ((((‖L z - y‖ ^ 2) / 2 : ℝ) : EReal)) := by
      exact_mod_cast hsq
    rw [Function.asEReal_apply, least_squares_quadratic_owner_apply L y x,
      Function.asEReal_apply, least_squares_quadratic_owner_apply L y z]
    exact hquad

omit [CompleteSpace 𝓗] in
/-- Helper for Example 27.24: `halfSquaredNorm` is uniformly convex on every nonempty
closed-ball slice of its effective domain. -/
lemma halfSquaredNorm_uniformlyConvexOn_closedBall_slice
    (c : 𝓗) {r : ℝ} (hr : 0 ≤ r)
    (hC_nonempty :
      (Metric.closedBall c r ∩
        ERealFunction.effectiveDomain
          (ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal))).Nonempty) :
    ∃ φ : NNReal → EReal,
      ERealFunction.UniformlyConvexOn ERealFunction.halfSquaredNorm
        (Metric.closedBall c r ∩
          ERealFunction.effectiveDomain (ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)))
        φ := by
  let g : 𝓗 → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
  have hr_nonneg : 0 ≤ r := hr
  have hstrong : StrongConvexOn (Set.univ : Set 𝓗) (1 : ℝ) g := by
    -- The half-squared norm is exactly the `β = 1` strong-convexity normal form.
    rw [strongConvexOn_iff_convex]
    simpa [g, sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (convexOn_const (c := (0 : ℝ)) convex_univ :
        _root_.ConvexOn ℝ (Set.univ : Set 𝓗) (fun _ : 𝓗 ↦ (0 : ℝ)))
  have huniform :
      ERealFunction.UniformlyConvex g.toEReal
        (ERealFunction.strongConvexityModulus (1 : ℝ)) := by
    have hstrongly :
        ERealFunction.StronglyConvex g.toEReal (1 : ℝ) :=
      ERealFunction.StrongConvexOn.toStronglyConvex (g := g) (by norm_num) hstrong
    exact hstrongly.uniformlyConvex
  have hhalf :
      g.toEReal = (ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)) := by
    ext x
    change (((‖x‖ ^ 2 / 2 : ℝ) : EReal)) = (ERealFunction.halfSquaredNorm x : EReal)
    rw [ERealFunction.halfSquaredNorm_apply]
  have hslice :
      ERealFunction.UniformlyConvexOn g.toEReal
        (Metric.closedBall c r ∩
          ERealFunction.effectiveDomain
            (ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)))
        (ERealFunction.strongConvexityModulus (1 : ℝ)) := by
    refine ⟨hC_nonempty, ?_, huniform.uniformlyConvexOn.monotone,
      huniform.uniformlyConvexOn.modulus_eq_zero_iff, ?_⟩
    · intro x hx
      simp [Function.effectiveDomain_toEReal]
    · intro x hx y hy α hα0 hα1
      simpa [Function.effectiveDomain_toEReal] using
        huniform.uniformlyConvexOn.gap_le (by simp [Function.effectiveDomain_toEReal])
          (by simp [Function.effectiveDomain_toEReal]) hα0 hα1
  -- Restrict the global uniform convexity of `halfSquaredNorm` to the requested closed-ball slice.
  refine ⟨ERealFunction.strongConvexityModulus (1 : ℝ), ?_⟩
  simpa [hhalf] using hslice

omit [CompleteSpace 𝓗] in
/-- Helper for Example 27.24: `halfSquaredNorm` belongs to `Γ₀(𝓗)`. -/
lemma halfSquaredNorm_mem_gammaZero_local :
    (ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)) ∈ Γ₀(𝓗) := by
  let q : 𝓗 → ℝ := fun x ↦ ‖x‖ ^ 2 / 2
  have hq_eq :
      q.toEReal = (ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)) := by
    ext x
    simp [q, ERealFunction.halfSquaredNorm, ERealFunction.moreauQuadraticKernel, div_eq_mul_inv,
      mul_comm]
  have hcont : Continuous q := by
    simpa [q, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (continuous_norm.pow 2).const_mul (1 / 2 : ℝ)
  have hconv :
      _root_.ConvexOn ℝ (Set.univ : Set 𝓗) q := by
    have hnorm_sq :
        _root_.ConvexOn ℝ (Set.univ : Set 𝓗) (fun z : 𝓗 ↦ ‖z‖ ^ 2) :=
      (convexOn_univ_norm :
          _root_.ConvexOn ℝ (Set.univ : Set 𝓗) (fun z : 𝓗 ↦ ‖z‖)).pow
        (fun z _ ↦ norm_nonneg z) 2
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hquad :
        ‖a • x + b • y‖ ^ 2 / 2 ≤ a * (‖x‖ ^ 2 / 2) + b * (‖y‖ ^ 2 / 2) := by
      have hquad' :
          ‖a • x + b • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
        simpa [smul_eq_mul] using hnorm_sq.2 (by simp) (by simp) ha hb hab
      nlinarith
    simpa [q] using hquad
  rw [← hq_eq]
  exact ERealFunction.real_toEReal_mem_gammaZero_of_continuous_convexOn_univ q hcont hconv

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Example 27.24: `halfSquaredNorm` is coercive, so its lower level sets are bounded.
-/
lemma halfSquaredNorm_coercive_local :
    ERealFunction.Coercive
      ((ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)).asEReal) := by
  refine
    (ERealFunction.coercive_iff_bounded_lowerLevelSet
      (f := (ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)).asEReal)).2 ?_
  intro ξ
  refine (Metric.isBounded_iff_subset_closedBall (0 : 𝓗)).2 ?_
  let R : ℝ := max 1 (2 * |ξ| + 1)
  refine ⟨R, ?_⟩
  intro x hx
  rw [ERealFunction.mem_lowerLevelSet_iff] at hx
  have hxreal : ‖x‖ ^ 2 / 2 ≤ ξ := by
    have hcast :
        ((ERealFunction.halfSquaredNorm x : Set.Ioi (⊥ : EReal)) : EReal) ≤ ((ξ : ℝ) : EReal) := by
      simpa [Function.asEReal_apply] using hx
    have hcast' :
        ((((1 / 2 : ℝ) * ‖x‖ ^ 2 : ℝ) : EReal)) ≤ ((ξ : ℝ) : EReal) := by
      simpa [ERealFunction.halfSquaredNorm_apply] using hcast
    have hreal' : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ ξ := by
      exact_mod_cast hcast'
    nlinarith
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hnorm
  have hnorm' : ¬ ‖x‖ ≤ R := by
    simpa using hnorm
  have hRlt : R < ‖x‖ := lt_of_not_ge hnorm'
  have hnorm_ge_one : 1 ≤ ‖x‖ := le_trans (le_max_left 1 (2 * |ξ| + 1)) hRlt.le
  have habs_lt : 2 * |ξ| + 1 < ‖x‖ := lt_of_le_of_lt (le_max_right 1 (2 * |ξ| + 1)) hRlt
  have hξ_twice : 2 * ξ < ‖x‖ := by
    nlinarith [le_abs_self ξ, habs_lt]
  have hnorm_sq_ge : ‖x‖ ≤ ‖x‖ ^ 2 := by
    nlinarith [hnorm_ge_one, sq_nonneg ‖x‖]
  have hξ_lt : ξ < ‖x‖ ^ 2 / 2 := by
    nlinarith [hξ_twice, hnorm_sq_ge]
  exact (not_lt_of_ge hxreal) hξ_lt

/-- Helper for Example 27.24: the Tikhonov-regularized least-squares objective is exactly the
Chapter 24 quadratic-affine owner with linear part `L†L + ε Id`. -/
lemma regularized_example_24_2_function_eq_leastSquares_plus_posReal_halfSquaredNorm
    (L : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ERealFunction.example_24_2_function
      ((L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)) (-(L.adjoint y)) (‖y‖ ^ 2 / 2) =
      leastSquaresQuadraticOwner L y +
        (⟨ε, hε.1⟩ : ERealFunction.PosReal) • ERealFunction.halfSquaredNorm := by
  ext x
  change
    (ERealFunction.example_24_2_function
      ((L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)) (-(L.adjoint y)) (‖y‖ ^ 2 / 2) x : EReal) =
      ((((leastSquaresQuadraticOwner L y x : Set.Ioi (⊥ : EReal)) +
          (((⟨ε, hε.1⟩ : ERealFunction.PosReal) • ERealFunction.halfSquaredNorm) x)) : EReal))
  rw [ERealFunction.posReal_smul_apply, ERealFunction.example_24_2_function_apply,
    least_squares_quadratic_owner_apply, ERealFunction.halfSquaredNorm_apply, ← EReal.coe_mul]
  -- Split the regularized quadratic form into the least-squares owner and the penalization term.
  have hsplit :
      (1 / 2 : ℝ) *
          ⟪(((L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)) x), x⟫_ℝ +
        ⟪x, -(L.adjoint y)⟫_ℝ + ‖y‖ ^ 2 / 2 =
      ((1 / 2 : ℝ) * ⟪((L.adjoint.comp L) x), x⟫_ℝ +
          ⟪x, -(L.adjoint y)⟫_ℝ + ‖y‖ ^ 2 / 2) +
        ε * (‖x‖ ^ 2 / 2) := by
    calc
      (1 / 2 : ℝ) *
            ⟪(((L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)) x), x⟫_ℝ +
          ⟪x, -(L.adjoint y)⟫_ℝ + ‖y‖ ^ 2 / 2
          =
            (1 / 2 : ℝ) *
                (⟪((L.adjoint.comp L) x), x⟫_ℝ +
                  ⟪(ε • (1 : 𝓗 →L[ℝ] 𝓗) x), x⟫_ℝ) +
              ⟪x, -(L.adjoint y)⟫_ℝ + ‖y‖ ^ 2 / 2 := by
              simp [inner_add_left]
      _ =
            (1 / 2 : ℝ) * ⟪((L.adjoint.comp L) x), x⟫_ℝ +
              ⟪x, -(L.adjoint y)⟫_ℝ + ‖y‖ ^ 2 / 2 +
              ε * (‖x‖ ^ 2 / 2) := by
              simp [one_apply, real_inner_smul_left, inner_self_eq_norm_sq_to_K]
              ring
      _ =
            ((1 / 2 : ℝ) * ⟪((L.adjoint.comp L) x), x⟫_ℝ +
                ⟪x, -(L.adjoint y)⟫_ℝ + ‖y‖ ^ 2 / 2) +
              ε * (‖x‖ ^ 2 / 2) := by
              ring
  have howner_real :
      (1 / 2 : ℝ) * ⟪((L.adjoint.comp L) x), x⟫_ℝ + ⟪x, -(L.adjoint y)⟫_ℝ + ‖y‖ ^ 2 / 2 =
        ‖L x - y‖ ^ 2 / 2 := by
    have howner_ereal :
        (((1 / 2 : ℝ) * ⟪((L.adjoint.comp L) x), x⟫_ℝ + ⟪x, -(L.adjoint y)⟫_ℝ +
            ‖y‖ ^ 2 / 2 : ℝ) : EReal) =
          ((((‖L x - y‖ ^ 2) / 2 : ℝ) : EReal)) := by
      simpa [leastSquaresQuadraticOwner, ERealFunction.example_24_2_function_apply] using
        (least_squares_quadratic_owner_apply L y x)
    exact_mod_cast howner_ereal
  rw [hsplit, howner_real, ← EReal.coe_add]

/-- Helper for Example 27.24: a zero gradient makes the Chapter 24 quadratic-affine owner attain
its global minimum. -/
lemma mem_argmin_example_24_2_function_of_gradient_zero
    (A : 𝓗 →L[ℝ] 𝓗) (hA_self : IsSelfAdjoint A) (hA_mono : A.toLinearMap.IsMonotone)
    (u p : 𝓗) (α : ℝ) (hp : A p + u = 0) :
    p ∈ Argmin (ERealFunction.example_24_2_function A u α).asEReal := by
  have hf :
      ERealFunction.example_24_2_function A u α ∈ Γ₀(𝓗) :=
    ERealFunction.example_24_2_function_mem_gammaZero A hA_self hA_mono u α
  have hgrad :
      HasGateauxDerivativeAt
        (fun x ↦
          (ERealFunction.example_24_2_function A u α x : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ 𝓗 (A p + u)) p := by
    -- The Chapter 24 owner has the textbook gradient `x ↦ A x + u`.
    simpa using
      ERealFunction.hasGateauxDerivativeAt_example_24_2_function_toReal_of_isSelfAdjoint
        A hA_self u p α
  have hsub :
      A p + u ∈
        ERealFunction.subdifferential (ERealFunction.example_24_2_function A u α) p :=
    ERealFunction.gateauxGradient_mem_subdifferential
      (ERealFunction.example_24_2_function A u α) hf.2
      (by
        rw [ERealFunction.effectiveDomain_example_24_2_function_eq_univ]
        simp)
      (A p + u) hgrad
  -- Route correction: use Fermat's rule directly instead of re-packaging a singleton
  -- subdifferential description.
  rw [ERealFunction.argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff]
  simpa [hp] using hsub

/-- Helper for Example 27.24: the inverse point of the regularized normal operator solves the
Euler-Lagrange equation for the Tikhonov objective. -/
lemma regularized_normal_operator_inverse_solves_equation
    (L : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    (((L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)) :
        𝓗 →L[ℝ] 𝓗)
        ((((L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)).inverse) (L.adjoint y)) +
      (-(L.adjoint y)) = 0 := by
  let Aε : 𝓗 →L[ℝ] 𝓗 := (L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)
  have hAε_self : IsSelfAdjoint Aε := by
    -- The Gram operator is self-adjoint, and so is the scalar identity perturbation.
    refine LinearMap.IsSymmetric.isSelfAdjoint ?_
    intro x z
    have hgram :
        ⟪((L.adjoint.comp L) x), z⟫_ℝ = ⟪x, (L.adjoint.comp L) z⟫_ℝ :=
      (isPositive_adjoint_comp_self L).isSelfAdjoint.isSymmetric x z
    calc
      ⟪Aε x, z⟫_ℝ
          = ⟪((L.adjoint.comp L) x), z⟫_ℝ + ⟪(ε • (1 : 𝓗 →L[ℝ] 𝓗) x), z⟫_ℝ := by
              simp [Aε, inner_add_left]
      _ = ⟪x, (L.adjoint.comp L) z⟫_ℝ + ε * ⟪x, z⟫_ℝ := by
              rw [hgram]
              simp [one_apply, real_inner_smul_left]
      _ = ⟪x, ((L.adjoint.comp L) z)⟫_ℝ + ⟪x, (ε • (1 : 𝓗 →L[ℝ] 𝓗) z)⟫_ℝ := by
              simp [one_apply, real_inner_smul_right]
      _ = ⟪x, Aε z⟫_ℝ := by
              simp [Aε, inner_add_right]
  have hAε_strong : Aε.toLinearMap.IsStronglyMonotone ε := by
    refine ⟨hε.1, ?_⟩
    intro x
    -- The identity contributes the `ε ‖x‖²` lower bound, while `L†L` adds a nonnegative term.
    have hgram_nonneg : 0 ≤ ‖L x‖ ^ 2 := sq_nonneg ‖L x‖
    have hgram :
        ⟪((L.adjoint.comp L) x), x⟫_ℝ = ‖L x‖ ^ 2 := by
      simpa [ContinuousLinearMap.comp_apply] using
        (L.apply_norm_sq_eq_inner_adjoint_left x).symm
    calc
      ε * ‖x‖ ^ 2 ≤ ε * ‖x‖ ^ 2 + ‖L x‖ ^ 2 := by linarith
      _ = ε * ‖x‖ ^ 2 + ⟪((L.adjoint.comp L) x), x⟫_ℝ := by rw [hgram]
      _ = ⟪Aε x, x⟫_ℝ := by
            simp [Aε, inner_add_left, one_apply, real_inner_smul_left,
              inner_self_eq_norm_sq_to_K, add_comm]
  have hAε_inv : Aε.IsInvertible :=
    ContinuousLinearMap.isInvertible_of_isSelfAdjoint_of_isStronglyMonotone
      Aε hAε_self hAε_strong
  -- Cancel the inverse through the strongly monotone normal operator.
  calc
    Aε (Aε.inverse (L.adjoint y)) + (-(L.adjoint y))
        = L.adjoint y + (-(L.adjoint y)) := by
            rw [hAε_inv.self_apply_inverse]
    _ = 0 := by abel_nf

/-- Helper for Example 27.24: the Moore-Penrose inverse is the minimum-norm minimizer of the
least-squares objective. -/
lemma moore_penrose_inverse_mem_argminOn_halfSquaredNorm
    (L : 𝓗 →L[ℝ] 𝓚) (hL_closed : IsClosed (L.range : Set 𝓚)) (y : 𝓚) :
    (L⁺[hL_closed]) y ∈
      Argmin[Argmin (leastSquaresQuadraticOwner L y).asEReal]
        ERealFunction.halfSquaredNorm.asEReal := by
  rw [ERealFunction.mem_argminOn_iff]
  refine ⟨?_, ?_⟩
  · -- The generalized inverse solves the normal equation, hence lies in the least-squares argmin.
    rw [argmin_least_squares_quadratic_owner_eq_moore_penrose_solution_set L hL_closed y]
    exact moorePenroseInverse_mem_moorePenroseSolutionSet L hL_closed y
  · rw [isMinOn_iff]
    intro z hz
    have hzsol : z ∈ moorePenroseSolutionSet L y := by
      rw [← argmin_least_squares_quadratic_owner_eq_moore_penrose_solution_set L hL_closed y]
      exact hz
    have hdist :
        Metric.infDist (0 : 𝓗) (moorePenroseSolutionSet L y) = ‖(L⁺[hL_closed]) y‖ := by
      -- The generalized inverse is the metric projection of `0` onto the solution set.
      simpa [dist_eq_norm, moorePenroseInverse_eq_projectionPoint_moorePenroseSolutionSet] using
        (projectionPoint_isBestApproximation (moorePenroseSolutionSet L y)
          (isChebyshev_moorePenroseSolutionSet L hL_closed y) 0).2.symm
    have hdist_le : Metric.infDist (0 : 𝓗) (moorePenroseSolutionSet L y) ≤ ‖z‖ := by
      simpa [dist_eq_norm] using
        (Metric.infDist_le_dist_of_mem (x := (0 : 𝓗)) hzsol)
    have hnorm : ‖(L⁺[hL_closed]) y‖ ≤ ‖z‖ := by
      simpa [hdist] using hdist_le
    have hsq : ‖(L⁺[hL_closed]) y‖ ^ 2 / 2 ≤ ‖z‖ ^ 2 / 2 := by
      nlinarith [hnorm, norm_nonneg ((L⁺[hL_closed]) y), norm_nonneg z]
    have hquad :
        (((‖(L⁺[hL_closed]) y‖ ^ 2 / 2 : ℝ) : EReal)) ≤
          (((‖z‖ ^ 2 / 2 : ℝ) : EReal)) := by
      exact_mod_cast hsq
    rw [Function.asEReal_apply, ERealFunction.halfSquaredNorm_apply,
      Function.asEReal_apply, ERealFunction.halfSquaredNorm_apply]
    exact hquad

/-- Helper for Example 27.24: for `ε > 0`, the regularized normal-equation solution is the unique
minimizer of the Tikhonov-regularized least-squares functional. -/
lemma regularized_quadratic_owner_inverse_apply_mem_argmin
    (L : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    (((L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)).inverse) (L.adjoint y) ∈
      Argmin
        (leastSquaresQuadraticOwner L y +
          (⟨ε, hε.1⟩ : ERealFunction.PosReal) • ERealFunction.halfSquaredNorm).asEReal := by
  let Aε : 𝓗 →L[ℝ] 𝓗 := (L.adjoint.comp L) + ε • (1 : 𝓗 →L[ℝ] 𝓗)
  have hAε_self : IsSelfAdjoint Aε := by
    -- Reuse the same self-adjointness computation as in the inverse-equation lemma.
    refine LinearMap.IsSymmetric.isSelfAdjoint ?_
    intro x z
    have hgram :
        ⟪((L.adjoint.comp L) x), z⟫_ℝ = ⟪x, (L.adjoint.comp L) z⟫_ℝ :=
      (isPositive_adjoint_comp_self L).isSelfAdjoint.isSymmetric x z
    calc
      ⟪Aε x, z⟫_ℝ
          = ⟪((L.adjoint.comp L) x), z⟫_ℝ + ⟪(ε • (1 : 𝓗 →L[ℝ] 𝓗) x), z⟫_ℝ := by
              simp [Aε, inner_add_left]
      _ = ⟪x, (L.adjoint.comp L) z⟫_ℝ + ε * ⟪x, z⟫_ℝ := by
              rw [hgram]
              simp [one_apply, real_inner_smul_left]
      _ = ⟪x, ((L.adjoint.comp L) z)⟫_ℝ + ⟪x, (ε • (1 : 𝓗 →L[ℝ] 𝓗) z)⟫_ℝ := by
              simp [one_apply, real_inner_smul_right]
      _ = ⟪x, Aε z⟫_ℝ := by
              simp [Aε, inner_add_right]
  have hAε_strong : Aε.toLinearMap.IsStronglyMonotone ε := by
    refine ⟨hε.1, ?_⟩
    intro x
    have hgram_nonneg : 0 ≤ ‖L x‖ ^ 2 := sq_nonneg ‖L x‖
    have hgram :
        ⟪((L.adjoint.comp L) x), x⟫_ℝ = ‖L x‖ ^ 2 := by
      simpa [ContinuousLinearMap.comp_apply] using
        (L.apply_norm_sq_eq_inner_adjoint_left x).symm
    calc
      ε * ‖x‖ ^ 2 ≤ ε * ‖x‖ ^ 2 + ‖L x‖ ^ 2 := by linarith
      _ = ε * ‖x‖ ^ 2 + ⟪((L.adjoint.comp L) x), x⟫_ℝ := by rw [hgram]
      _ = ⟪Aε x, x⟫_ℝ := by
            simp [Aε, inner_add_left, one_apply, real_inner_smul_left,
              inner_self_eq_norm_sq_to_K, add_comm]
  have hargmin :
      Aε.inverse (L.adjoint y) ∈
        Argmin (ERealFunction.example_24_2_function Aε (-(L.adjoint y)) (‖y‖ ^ 2 / 2)).asEReal := by
    have hzero :
        Aε (Aε.inverse (L.adjoint y)) + (-(L.adjoint y)) = 0 := by
      simpa [Aε] using regularized_normal_operator_inverse_solves_equation L y hε
    -- The zero-gradient criterion now gives the regularized minimizer directly.
    exact mem_argmin_example_24_2_function_of_gradient_zero
      Aε hAε_self hAε_strong.isMonotone (-(L.adjoint y)) (Aε.inverse (L.adjoint y))
      (‖y‖ ^ 2 / 2) hzero
  -- Rewrite the owner back to the source-facing least-squares-plus-penalty functional.
  rw [← regularized_example_24_2_function_eq_leastSquares_plus_posReal_halfSquaredNorm
    L y hε]
  simpa [Aε] using hargmin

-- Semantic recall: Chapter 3 exposes the generalized inverse as `L⁺[hL_closed]`, and the
-- Chapter 27 convergence statements model `ε ↓ 0` with `nhdsWithin (0 : ℝ)` on a positive set.
/-- Example 27.24: if `L : 𝓗 →L[ℝ] 𝓚` has closed range, then the Tikhonov-regularized
normal-equation solutions `(L*L + ε Id)⁻¹ L* y` converge to the generalized inverse `L† y`
as `ε ↓ 0`. -/
theorem tendsto_regularized_normalEquation_inverse_apply_adjoint_to_moorePenroseInverse
    (L : 𝓗 →L[ℝ] 𝓚) (hL_closed : IsClosed (L.range : Set 𝓚)) (y : 𝓚) :
    Tendsto
      (fun ε : ℝ ↦ ((((L.adjoint ∘L L) + ε • 1).inverse) ∘L L.adjoint) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((L⁺[hL_closed]) y)) := by
  let xε : ℝ → 𝓗 := fun ε ↦ ((((L.adjoint ∘L L) + ε • 1).inverse) ∘L L.adjoint) y
  have hf : leastSquaresQuadraticOwner L y ∈ Γ₀(𝓗) := by
    -- The least-squares owner is Example 24.2 with the positive Gram operator.
    simpa [leastSquaresQuadraticOwner] using
      ERealFunction.example_24_2_function_mem_gammaZero
        (L.adjoint.comp L)
        (isPositive_adjoint_comp_self L).isSelfAdjoint
        ((isPositive_adjoint_comp_self L).toLinearMap.isMonotone)
        (-(L.adjoint y)) (‖y‖ ^ 2 / 2)
  have hg :
      (ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)) ∈ Γ₀(𝓗) :=
    halfSquaredNorm_mem_gammaZero_local
  have hfeas :
      (Argmin (leastSquaresQuadraticOwner L y).asEReal ∩
        ERealFunction.effectiveDomain ERealFunction.halfSquaredNorm).Nonempty := by
    refine ⟨(L⁺[hL_closed]) y, ?_, ?_⟩
    · rw [argmin_least_squares_quadratic_owner_eq_moore_penrose_solution_set L hL_closed y]
      exact moorePenroseInverse_mem_moorePenroseSolutionSet L hL_closed y
    · rw [ERealFunction.mem_effectiveDomain_iff, ERealFunction.halfSquaredNorm_apply]
      exact EReal.coe_lt_top _
  have hg_coe :
      ERealFunction.Coercive
        ((ERealFunction.halfSquaredNorm : 𝓗 → Set.Ioi (⊥ : EReal)).asEReal) :=
    halfSquaredNorm_coercive_local
  have hxε :
      ∀ {ε : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1),
        xε ε ∈
          Argmin
            (leastSquaresQuadraticOwner L y +
              (⟨ε, hε.1⟩ : ERealFunction.PosReal) • ERealFunction.halfSquaredNorm).asEReal := by
    intro ε hε
    simpa [xε, ContinuousLinearMap.comp_apply] using
      regularized_quadratic_owner_inverse_apply_mem_argmin L y hε
  have hmain :
      Tendsto xε (nhdsWithin (0 : ℝ) (Set.Ioo (0 : ℝ) 1)) (𝓝 ((L⁺[hL_closed]) y)) := by
    -- This is exactly the source-faithful Theorem 27.23 route from the textbook proof.
    refine ERealFunction.tendsto_argmin_add_posReal_smul_of_closedBall_uniformlyConvex
      hf hg hfeas hg_coe
      (fun {c} {r} hr hnonempty ↦
        halfSquaredNorm_uniformlyConvexOn_closedBall_slice (c := c) hr hnonempty)
      (moore_penrose_inverse_mem_argminOn_halfSquaredNorm L hL_closed y)
      hxε
  simpa [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one, xε] using hmain
