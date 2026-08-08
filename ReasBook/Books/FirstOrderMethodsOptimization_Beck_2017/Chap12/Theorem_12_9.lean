import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_12
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_33
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_5
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Gradient

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)

local notation "q" => dual_based_proximal_gradient_lagrange_dual_objective_primal f g A
local notation "qOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value f g A
local notation "Hdual" =>
  composite_model_objective
    (fun z : V ↦ (((EReal.toReal ((f∗) (A.adjoint z)) : ℝ)) : EReal))
    (fun z : V ↦ (g∗) (-z))

/-- Helper for Theorem 12.9: the source acceleration sequence coincides with the canonical Chapter
10 FISTA momentum sequence. -/
lemma fast_dual_primal_acceleration_eq_fista_momentum
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {u : ℕ → E} {y w : ℕ → V} {t : ℕ → ℝ}
    (htraj : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t) :
    ∀ k : ℕ, t k = fista_momentum_sequence k := by
  intro k
  induction k with
  | zero =>
      -- Both momentum sequences start from the textbook value `t₀ = 1`.
      simpa using htraj.t_zero
  | succ k hk =>
      -- The source acceleration recursion is the same Chapter 10 update as the canonical owner.
      rw [htraj.acceleration_step k, hk, fista_momentum_sequence_succ]

/-- Helper for Theorem 12.9: the canonical Chapter 10 momentum sequence satisfies the scalar
identity `t_(k+1)^2 - t_(k+1) = t_k^2`. -/
lemma fast_dual_momentum_quadratic_identity (k : ℕ) :
    fista_momentum_sequence (k + 1) ^ (2 : ℕ) - fista_momentum_sequence (k + 1) =
      fista_momentum_sequence k ^ (2 : ℕ) := by
  -- Rewrite the successor momentum through the explicit Chapter 10 update formula.
  rw [fista_momentum_sequence_succ, fista_momentum_update_eq]
  have hsqrt_sq :
      Real.sqrt (1 + 4 * fista_momentum_sequence k ^ (2 : ℕ)) *
          Real.sqrt (1 + 4 * fista_momentum_sequence k ^ (2 : ℕ)) =
        1 + 4 * fista_momentum_sequence k ^ (2 : ℕ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + 4 * fista_momentum_sequence k ^ (2 : ℕ) by positivity)]
  -- The remaining step is a scalar simplification of the displayed formula.
  nlinarith

/-- Helper for Theorem 12.9: the native Algorithm 12.3 extrapolation is tracked by the shifted
residual built from `w^k`, the iterate `y^k`, and the comparison point `yStar`. -/
def native_dual_residual_to_optimum
    (y0 : V) (y : ℕ → V) (yStar : V) : ℕ → V
  | 0 => y0 - yStar
  | 1 => y 1 - yStar
  | k + 2 =>
      (1 + fista_momentum_sequence k) • y (k + 2) -
        (yStar + fista_momentum_sequence k • y (k + 1))

/-- Helper for Theorem 12.9: the prox-gradient comparison term at step `k` is the scaled
displacement from `y (k + 1)` to the source convex-combination point. -/
def native_dual_step_residual_to_optimum
    (y : ℕ → V) (yStar : V) (k : ℕ) : V :=
  (fista_momentum_sequence (k + 1) : ℝ) • y (k + 1) -
    (yStar + (fista_momentum_sequence (k + 1) - 1) • y k)

/-- Helper for Theorem 12.9: multiplying the native extrapolated point `w^k` by `t_(k+1)`
produces the shifted residual dictated by Algorithm 12.3's momentum field. -/
lemma chapter12_scaled_extrapolation_residual
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ
      (fun z : V ↦ (g∗) (-z))
      (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
      L y0 y w)
    (yStar : V) (k : ℕ) :
    (fista_momentum_sequence k : ℝ) • w k -
      (yStar + (fista_momentum_sequence k - 1) • y k) =
        native_dual_residual_to_optimum y0 y yStar k := by
  cases k with
  | zero =>
      -- At the base index, `w⁰ = y⁰ = y0`, so the scalar coefficient cancels completely.
      simp only [native_dual_residual_to_optimum, htraj.w_zero, htraj.y_zero, sub_eq_add_neg]
      module
  | succ k =>
      cases k with
      | zero =>
          -- The first extrapolated point is stored separately as `w¹ = y¹`.
          simp only [native_dual_residual_to_optimum, htraj.first_momentum_step, sub_eq_add_neg]
          module
      | succ n =>
          have ht_lb :
              (((n + 2 : ℕ) : ℝ) + 2) / 2 ≤ fista_momentum_sequence (n + 2) :=
            fista_momentum_sequence_lower_bound
              fista_momentum_sequence_zero
              fista_momentum_sequence_succ
              (n + 2)
          have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by
            positivity
          have haux_real : (1 : ℝ) ≤ ((n : ℝ) + 4) / 2 := by
            have htwo : (2 : ℝ) ≤ (n : ℝ) + 4 := by
              nlinarith
            linarith
          have haux : (1 : ℝ) ≤ (((n + 2 : ℕ) : ℝ) + 2) / 2 := by
            norm_num [Nat.cast_add] at haux_real ⊢
            linarith
          have ht_ge_one : (1 : ℝ) ≤ fista_momentum_sequence (n + 2) :=
            le_trans haux ht_lb
          have ht_pos : 0 < fista_momentum_sequence (n + 2) :=
            lt_of_lt_of_le zero_lt_one ht_ge_one
          have hinv :
              (fista_momentum_sequence (n + 2) : ℝ) *
                  (fista_momentum_sequence (n + 2))⁻¹ =
                1 := by
            field_simp [ht_pos.ne']
          have hprod :
              (fista_momentum_sequence (n + 2) : ℝ) *
                  (fista_momentum_sequence n *
                    (fista_momentum_sequence (n + 2))⁻¹) =
                fista_momentum_sequence n := by
            calc
              (fista_momentum_sequence (n + 2) : ℝ) *
                  (fista_momentum_sequence n *
                    (fista_momentum_sequence (n + 2))⁻¹) =
                  fista_momentum_sequence n *
                    ((fista_momentum_sequence (n + 2) : ℝ) *
                      (fista_momentum_sequence (n + 2))⁻¹) := by
                    ring
              _ = fista_momentum_sequence n := by simp [hinv]
          -- Route correction: the native owner stores the shifted coefficient
          -- `t_n / t_(n+2)`, so the residual must follow that exact recurrence rather than
          -- the Chapter 10 FISTA one.
          rw [htraj.momentum_step n, div_eq_mul_inv]
          simp_rw [smul_add, smul_sub, smul_smul]
          rw [hprod]
          simp only [native_dual_residual_to_optimum, sub_eq_add_neg, add_assoc]
          module

/-- Helper for Theorem 12.9: the prox-gradient quadratic term at step `k` is the squared norm of
the source comparison residual based at `y (k + 1)`. -/
lemma chapter12_native_step_residual_norm_rewrite
    (y : ℕ → V) (yStar : V) (k : ℕ) :
    let θ : ℝ := (fista_momentum_sequence (k + 1))⁻¹
    let z : V := θ • yStar + (1 - θ) • y k
    (fista_momentum_sequence (k + 1) : ℝ) ^ (2 : ℕ) * ‖y (k + 1) - z‖ ^ (2 : ℕ) =
      ‖native_dual_step_residual_to_optimum y yStar k‖ ^ (2 : ℕ) := by
  let θ : ℝ := (fista_momentum_sequence (k + 1))⁻¹
  let z : V := θ • yStar + (1 - θ) • y k
  have ht_lb :
      (((k + 1 : ℕ) : ℝ) + 2) / 2 ≤ fista_momentum_sequence (k + 1) :=
    fista_momentum_sequence_lower_bound
      fista_momentum_sequence_zero
      fista_momentum_sequence_succ
      (k + 1)
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by
    positivity
  have haux_real : (1 : ℝ) ≤ ((k : ℝ) + 3) / 2 := by
    have htwo : (2 : ℝ) ≤ (k : ℝ) + 3 := by
      nlinarith
    linarith
  have haux : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + 2) / 2 := by
    norm_num [Nat.cast_add] at haux_real ⊢
    linarith
  have ht_ge_one : (1 : ℝ) ≤ fista_momentum_sequence (k + 1) :=
    le_trans haux ht_lb
  have ht_pos : 0 < fista_momentum_sequence (k + 1) :=
    lt_of_lt_of_le zero_lt_one ht_ge_one
  have hmul_inv :
      (fista_momentum_sequence (k + 1) : ℝ) *
          (fista_momentum_sequence (k + 1))⁻¹ =
        1 := by
    field_simp [ht_pos.ne']
  have hcoef :
      (fista_momentum_sequence (k + 1) : ℝ) *
          (1 - (fista_momentum_sequence (k + 1))⁻¹) =
        fista_momentum_sequence (k + 1) - 1 := by
    nlinarith [hmul_inv]
  have hscaled :
      (fista_momentum_sequence (k + 1) : ℝ) • (y (k + 1) - z) =
        native_dual_step_residual_to_optimum y yStar k := by
    -- Multiply the displacement by `t_(k+1)` and cancel the coefficient `1 / t_(k+1)`.
    dsimp [z, θ, native_dual_step_residual_to_optimum]
    rw [smul_sub, smul_add]
    simp_rw [smul_smul]
    rw [hmul_inv, hcoef]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  dsimp [θ, z]
  calc
    (fista_momentum_sequence (k + 1) : ℝ) ^ (2 : ℕ) * ‖y (k + 1) - z‖ ^ (2 : ℕ) =
        ‖(fista_momentum_sequence (k + 1) : ℝ) • (y (k + 1) - z)‖ ^ (2 : ℕ) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
          ring
    _ = ‖native_dual_step_residual_to_optimum y yStar k‖ ^ (2 : ℕ) := by
          rw [hscaled]

/-- Helper for Theorem 12.9: the native pre-step quadratic term based at `w^k` is exactly the
squared norm of the shifted Algorithm 12.3 residual. -/
lemma chapter12_native_extrapolated_residual_norm_rewrite
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ
      (fun z : V ↦ (g∗) (-z))
      (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
      L y0 y w)
    (yStar : V) (k : ℕ) :
    let θ : ℝ := (fista_momentum_sequence k)⁻¹
    let z : V := θ • yStar + (1 - θ) • y k
    (fista_momentum_sequence k : ℝ) ^ (2 : ℕ) * ‖w k - z‖ ^ (2 : ℕ) =
      ‖native_dual_residual_to_optimum y0 y yStar k‖ ^ (2 : ℕ) := by
  let θ : ℝ := (fista_momentum_sequence k)⁻¹
  let z : V := θ • yStar + (1 - θ) • y k
  have ht_lb :
      (((k : ℕ) : ℝ) + 2) / 2 ≤ fista_momentum_sequence k :=
    fista_momentum_sequence_lower_bound
      fista_momentum_sequence_zero
      fista_momentum_sequence_succ
      k
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by
    positivity
  have haux_real : (1 : ℝ) ≤ ((k : ℝ) + 2) / 2 := by
    have htwo : (2 : ℝ) ≤ (k : ℝ) + 2 := by
      nlinarith
    linarith
  have haux : (1 : ℝ) ≤ (((k : ℕ) : ℝ) + 2) / 2 := by
    simpa using haux_real
  have ht_ge_one : (1 : ℝ) ≤ fista_momentum_sequence k :=
    le_trans haux ht_lb
  have ht_pos : 0 < fista_momentum_sequence k :=
    lt_of_lt_of_le zero_lt_one ht_ge_one
  have hmul_inv :
      (fista_momentum_sequence k : ℝ) *
          (fista_momentum_sequence k)⁻¹ =
        1 := by
    field_simp [ht_pos.ne']
  have hcoef :
      (fista_momentum_sequence k : ℝ) *
          (1 - (fista_momentum_sequence k)⁻¹) =
        fista_momentum_sequence k - 1 := by
    nlinarith [hmul_inv]
  have hscaled :
      (fista_momentum_sequence k : ℝ) • (w k - z) =
        native_dual_residual_to_optimum y0 y yStar k := by
    -- The native extrapolated term rewrites to the shifted residual once the scalar factor is
    -- pushed through the convex-combination point.
    dsimp [z, θ]
    rw [smul_sub, smul_add]
    simp_rw [smul_smul]
    rw [hmul_inv, hcoef]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      chapter12_scaled_extrapolation_residual
        (f := f) (g := g) (A := A) htraj yStar k
  dsimp [θ, z]
  calc
    (fista_momentum_sequence k : ℝ) ^ (2 : ℕ) * ‖w k - z‖ ^ (2 : ℕ) =
        ‖(fista_momentum_sequence k : ℝ) • (w k - z)‖ ^ (2 : ℕ) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
          ring
    _ = ‖native_dual_residual_to_optimum y0 y yStar k‖ ^ (2 : ℕ) := by
          rw [hscaled]

/-- Helper for Theorem 12.9: a point is an argmax of `x' ↦ ⟪x', y⟫ - f x'` exactly when its
canonical double-dual image is a subgradient of `conjugate_function f` at `y`. -/
lemma eval_mem_conjugate_subdifferential_iff_isMaxOn_affine_minus
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f)
    (yDual : Module.Dual ℝ E) (x : E) :
    Module.Dual.eval ℝ E x ∈ extendedRealSubdifferential (conjugate_function f) yDual ↔
      IsMaxOn (fun x' : E ↦ (yDual x' : EReal) - f x') Set.univ x := by
  constructor
  · intro hx
    rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
      f hf_proper hf_closed hf_convex yDual] at hx
    rcases hx with ⟨x', hx', hEval⟩
    have hxEq : x' = x :=
      Module.eval_apply_injective (K := ℝ) (V := E) hEval
    simpa using hxEq ▸ hx'
  · intro hx
    rw [subdifferential_conjugate_eq_eval_image_argmax_affine_minus
      f hf_proper hf_closed hf_convex yDual]
    exact ⟨x, hx, rfl⟩

/-- Helper for Theorem 12.9: an Algorithm 12.4 primal argmax point determines a conjugate-side
subgradient at `Aᵀ v`. -/
lemma eval_mem_conjugate_subdifferential_of_mem_dual_primal_x_argmax
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {v : V} {x : E}
    (hx : x ∈ dual_proximal_gradient_primal_x_argmax f A v) :
    Module.Dual.eval ℝ E x ∈
      extendedRealSubdifferential (conjugate_function f)
        (InnerProductSpace.toDualMap ℝ E (A.adjoint v)) := by
  have hf_convex_toReal :
      ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) := by
    exact (h_problem.f_strongly_convex.strictConvexOn σ.2).convexOn
  have hf_convex : is_convex_function f := by
    rw [is_convex_function_iff_convexOn_toReal (fun z _ ↦ h_problem.ne_bot z)]
    exact hf_convex_toReal
  have hmax :
      IsMaxOn
        (fun x' : E ↦
          (((InnerProductSpace.toDualMap ℝ E (A.adjoint v)) x' : EReal) - f x'))
        Set.univ x := by
    simpa [mem_dual_proximal_gradient_primal_x_argmax_iff,
      InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hx
  -- Theorem 4.12 already packages the conjugate-side argmax bridge.
  exact
    (eval_mem_conjugate_subdifferential_iff_isMaxOn_affine_minus
      (f := f) h_problem.toIsProperExtendedRealFunction h_problem.f_closed hf_convex
      (InnerProductSpace.toDualMap ℝ E (A.adjoint v)) x).2 hmax

/-- Helper for Theorem 12.9: a conjugate-side subgradient at `y` is the canonical gradient point
of the primal conjugate `f∗` at `y`. -/
lemma conjugate_subgradient_eval_eq_gradient_point
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {y x : E}
    (hx : Module.Dual.eval ℝ E x ∈
      extendedRealSubdifferential (conjugate_function f) (InnerProductSpace.toDualMap ℝ E y)) :
    x = ∇ (fun z : E ↦ ((f∗) z).toReal) y := by
  let φ : E →ₗ[ℝ] Module.Dual ℝ E :=
    ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).symm).toLinearMap.comp
      ((InnerProductSpace.toDual ℝ E).toLinearEquiv.toLinearMap)
  let xDual : Module.Dual ℝ E :=
    (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).symm
      (InnerProductSpace.toDual ℝ E x)
  have hconj_finite :
      ∀ z : E, (f∗) z ≠ ⊥ ∧ (f∗) z < ⊤ := by
    intro z
    simpa using
      dual_based_proximal_gradient_dual_F_primal_finite_valued
        (σ := σ) (f := f) (A := LinearMap.id)
        h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex z
  have hconj_convex : is_convex_function (f∗) := by
    simpa using dual_based_proximal_gradient_dual_F_primal_convex
      (f := f) (A := (LinearMap.id : E →ₗ[ℝ] E))
  have hconj_diff :
      DifferentiableAt ℝ (fun z : E ↦ ((f∗) z).toReal) y := by
    exact
      (conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
        (σ := σ) (f := f)
        h_problem.toIsProperExtendedRealFunction h_problem.f_closed
        h_problem.f_strongly_convex).1 y (by simp)
  have hy_interior : y ∈ interior (finite_domain (f∗)) := by
    have hfinite_domain_univ : finite_domain (f∗) = Set.univ := by
      ext z
      constructor
      · intro hz
        simp
      · intro hz
        rcases hconj_finite z with ⟨hz_ne_bot, hz_lt_top⟩
        exact ⟨hz_lt_top, hz_ne_bot⟩
    simpa [hfinite_domain_univ]
  have hx_primal : xDual ∈ extendedRealSubdifferential (f∗) y := by
    have hφ_apply (z : E) : φ z = (InnerProductSpace.toDualMap ℝ E z : Module.Dual ℝ E) := by
      ext w
      simp [φ, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
    have hφdual :
        φ.dualMap (Module.Dual.eval ℝ E x) = xDual := by
      ext z
      simp [xDual, φ, InnerProductSpace.toDual_apply_eq_toDualMap_apply, real_inner_comm]
    have hpullback :
        φ.dualMap (Module.Dual.eval ℝ E x) ∈
          extendedRealSubdifferential (fun z : E ↦ conjugate_function f (φ z)) y := by
      exact
        (subdifferential_precompose_affineMap_subset
          (f := conjugate_function f) (φ := φ.toAffineMap) (x := y))
          ⟨Module.Dual.eval ℝ E x, hx, rfl⟩
    have hsubset :=
      show (fun z : E ↦ conjugate_function f (φ z)) = (f∗) by
        funext z
        simpa [hφ_apply z] using (conjugate_function_primal_apply f z).symm
    simpa [hsubset, hφdual] using hpullback
  have hx_strong :
      InnerProductSpace.toDual ℝ E x ∈ strongDualSubdifferential (f∗) y := by
    have hx_image :
        InnerProductSpace.toDual ℝ E x ∈
          (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
            extendedRealSubdifferential (f∗) y := by
      refine ⟨xDual, hx_primal, ?_⟩
      ext z
      simp [xDual, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
    simpa [strongDualSubdifferential_eq_image_subdifferential] using hx_image
  have hsingleton :=
    subdifferential_eq_singleton_gradient_of_differentiableAt
      (f := (f∗)) y hconj_convex ⟨hy_interior, hconj_diff⟩
  have hx_eq_dual :
      InnerProductSpace.toDual ℝ E x =
        InnerProductSpace.toDual ℝ E
          (∇ (fun z : E ↦ ((f∗) z).toReal) y) := by
    have :
        InnerProductSpace.toDual ℝ E x ∈
          ({InnerProductSpace.toDual ℝ E
              (∇ (fun z : E ↦ ((f∗) z).toReal) y)} : Set (StrongDual ℝ E)) := by
      simpa [hsingleton] using hx_strong
    simpa using this
  exact (InnerProductSpace.toDual ℝ E).injective hx_eq_dual

/-- A primal argmax point is the conjugate gradient at the corresponding adjoint dual point. -/
lemma dual_primal_x_argmax_eq_conjugate_gradient
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {v : V} {x : E}
    (hx : x ∈ dual_proximal_gradient_primal_x_argmax f A v) :
    x = ∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint v) := by
  apply conjugate_subgradient_eval_eq_gradient_point
    (f := f) (g := g) (A := A) (σ := σ) h_problem
  exact
    eval_mem_conjugate_subdifferential_of_mem_dual_primal_x_argmax
      (f := f) (g := g) (A := A) (σ := σ) h_problem hx

/-- Helper for Theorem 12.9: the Chapter 12 split minimization objective is pointwise `-q`. -/
lemma dual_terms_objective_eq_neg_q
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y : V) :
    composite_model_objective
        (fun z : V ↦ ((((f∗) (A.adjoint z)).toReal : ℝ) : EReal))
        (fun z : V ↦ (g∗) (-z))
        y =
      -q y := by
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex y
  have hG_ne_bot : (g∗) (-y) ≠ ⊥ := by
    exact
      (dual_based_proximal_gradient_dual_G_primal_proper
        (g := g) h_problem.g_proper h_problem.g_convex).ne_bot y
  have hF_toReal :
      ((((f∗) (A.adjoint y)).toReal : ℝ) : EReal) = (f∗) (A.adjoint y) := by
    exact EReal.coe_toReal hF_finite.2.ne hF_finite.1
  rw [composite_model_objective_apply, hF_toReal,
    dual_based_proximal_gradient_lagrange_dual_objective_primal_apply]
  have hneg_top : -(f∗) (A.adjoint y) ≠ ⊤ := by
    intro htop
    apply hF_finite.1
    simpa using congrArg Neg.neg htop
  have hneg :
      -(-(f∗) (A.adjoint y) - (g∗) (-y)) =
        -(-(f∗) (A.adjoint y)) + (g∗) (-y) :=
    EReal.neg_sub (Or.inr (by simpa using hG_ne_bot)) (Or.inl hneg_top)
  simpa using hneg.symm

/-- Helper for Theorem 12.9: every primal-space dual value is bounded above by the source dual
optimal value `qOpt`. -/
lemma dual_objective_le_problem_value
    (y : V) :
    q y ≤ qOpt := by
  -- Unfold the optimal-value owner once and use the ambient `sSup` upper bound.
  exact le_sSup ⟨InnerProductSpace.toDualMap ℝ V y, rfl⟩

/-- Helper for Theorem 12.9: on the effective domain of the dual nonsmooth term `G(y) = g*(-y)`,
the split Chapter 12 objective is a finite real sum. -/
lemma dual_terms_objective_eq_real_of_mem_effective_domain
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {y : V}
    (hy : y ∈ effective_domain (fun z : V ↦ (g∗) (-z))) :
    Hdual y =
      (((((f∗) (A.adjoint y)).toReal + ((g∗) (-y)).toReal : ℝ)) : EReal) := by
  let hG_proper : IsProperExtendedRealFunction (fun z : V ↦ (g∗) (-z)) :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g) h_problem.g_proper h_problem.g_convex
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex y
  have hF_val :
      ((((f∗) (A.adjoint y)).toReal : ℝ) : EReal) =
        (f∗) (A.adjoint y) := by
    exact EReal.coe_toReal hF_finite.2.ne hF_finite.1
  have hG_val :
      ((((g∗) (-y)).toReal : ℝ) : EReal) =
        (g∗) (-y) := by
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hy).ne
        ((hG_proper.ne_bot _))
  -- Once both dual summands are finite, the split objective is just the corresponding real sum.
  rw [composite_model_objective_apply, ← hF_val, ← hG_val]
  simp

/-- Helper for Theorem 12.9: at an attaining optimal dual point, the split minimization objective
has value `-qOpt`. -/
lemma dual_terms_objective_eq_neg_qOpt_of_dual_optimum
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {yStar : V}
    (hyStar : q yStar = qOpt) :
    composite_model_objective
        (fun z : V ↦ ((((f∗) (A.adjoint z)).toReal : ℝ) : EReal))
        (fun z : V ↦ (g∗) (-z))
        yStar =
      -qOpt := by
  -- First rewrite the Chapter 12 split objective to `-q`, then substitute the attaining value.
  rw [dual_terms_objective_eq_neg_q (f := f) (g := g) (A := A) σ h_problem yStar, hyStar]

/-- Helper for Theorem 12.9: the split minimization gap `Hdual(y) - (-qOpt)` is exactly the
source dual gap `qOpt - q(y)`. -/
lemma dual_terms_objective_gap_eq_dual_gap
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y : V) :
    composite_model_objective
        (fun z : V ↦ ((((f∗) (A.adjoint z)).toReal : ℝ) : EReal))
        (fun z : V ↦ (g∗) (-z))
        y -
        (-qOpt) =
      qOpt - q y := by
  -- Normalize the split objective to `-q` and then rearrange the two negations.
  rw [dual_terms_objective_eq_neg_q (f := f) (g := g) (A := A) σ h_problem y]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using rfl

/-- Helper for Theorem 12.9: an attaining dual optimum minimizes the split Chapter 12 objective
`Fdual + Gdual = -q` on the whole dual space. -/
lemma dual_terms_minimizer_of_dual_optimum
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {yStar : V}
    (hyStar : q yStar = qOpt) :
    yStar ∈
      unconstrained_problem_solutions
        (composite_model_objective
          (fun z : V ↦ ((((f∗) (A.adjoint z)).toReal : ℝ) : EReal))
          (fun z : V ↦ (g∗) (-z))) := by
  -- Rewrite the minimization surface to `-q` and use the defining upper bound `q y ≤ qOpt`.
  rw [mem_unconstrained_problem_solutions_iff_forall_le]
  intro y
  rw [dual_terms_objective_eq_neg_qOpt_of_dual_optimum
      (f := f) (g := g) (A := A) σ h_problem hyStar,
    dual_terms_objective_eq_neg_q (f := f) (g := g) (A := A) σ h_problem y]
  exact EReal.neg_le_neg_iff.2 (dual_objective_le_problem_value (f := f) (g := g) (A := A) y)

/-- Helper for Theorem 12.9: the canonical FISTA coefficient `1 / t_(k+1)` is a valid
convex-combination weight. -/
lemma chapter12_one_div_momentum_mem_Icc
    (k : ℕ) :
    ((fista_momentum_sequence (k + 1))⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have ht_ge_one : (1 : ℝ) ≤ fista_momentum_sequence (k + 1) := by
    have hbound :=
      fista_momentum_sequence_lower_bound
        fista_momentum_sequence_zero
        fista_momentum_sequence_succ
        (k + 1)
    have hk_one : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have haux : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + 2) / 2 := by
      nlinarith
    exact le_trans haux hbound
  have ht_pos : 0 < fista_momentum_sequence (k + 1) :=
    lt_of_lt_of_le zero_lt_one ht_ge_one
  refine ⟨inv_nonneg.mpr (le_of_lt ht_pos), ?_⟩
  have hrecip : 1 / fista_momentum_sequence (k + 1) ≤ 1 / (1 : ℝ) :=
    one_div_le_one_div_of_le zero_lt_one ht_ge_one
  simpa [one_div] using hrecip

/- Theorem 12.9 is split across the usual three layers.

Domain sampling in the surrounding project identifies:
- `IsFastDualProximalGradientDualTrajectory` from Algorithm 12.3 as the `core/canonical` owner of
  the accelerated dual iteration acting on the dual objective `F + G`;
- `IsFastDualProximalGradientPrimalTrajectory` from Algorithm 12.4 as the `source-facing`
  trajectory owner that additionally records the primal argmax sequence `u^k`;
- `dual_based_proximal_gradient_lagrange_dual_objective_primal` from Definition 12.4 together with
  `dual_based_proximal_gradient_lagrange_dual_problem_value` as the canonical Chapter 12 owners
  for `q` and `q_opt`.

Primitive data for the rate statement are therefore the standing problem assumptions, the
admissible constant parameter, the accelerated dual trajectory data `(y, w)`, and the chosen
optimal dual point `yStar`. The primal argmax sequence `u` and the source-facing scalar sequence
`t` belong only to the Algorithm 12.4 presentation, so the core rate theorem below is stated at
the dual-trajectory owner level and the textbook formulation is recovered by a thin bridge theorem.
-/

/-- A fast dual proximal-gradient primal trajectory canonically determines the corresponding fast
dual proximal-gradient dual trajectory for the Chapter 12 dual composite `F + G`. -/
theorem IsFastDualProximalGradientPrimalTrajectory.toDualTrajectory
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {u : ℕ → E} {y w : ℕ → V} {t : ℕ → ℝ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (htraj : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t) :
    IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ
      (fun z : V ↦ (g∗) (-z))
      (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
      L y0 y w := by
  -- The initialization and momentum fields are already stored verbatim in the source owner.
  refine
    { y_zero := htraj.y_zero
      w_zero := htraj.w_zero
      dual_step := ?_
      first_momentum_step := htraj.first_momentum_step
      momentum_step := ?_ }
  · intro k
    -- First identify the source argmax point `u^k` with the gradient of `f∗` at `Aᵀ w^k`.
    have hu_eq :
        u k = ∇ (fun x : E ↦ ((f∗) x).toReal) (A.adjoint (w k)) := by
      apply conjugate_subgradient_eval_eq_gradient_point
        (f := f) (g := g) (A := A) (σ := σ) h_problem
      exact
        eval_mem_conjugate_subdifferential_of_mem_dual_primal_x_argmax
          (f := f) (g := g) (A := A) (σ := σ) h_problem (htraj.primal_step k)
    -- Then Lemma 12.5 converts the primal `y`-step owner into the canonical dual-step owner.
    have hdual_step :
        y (k + 1) ∈
          dual_proximal_gradient_primal_y_step
            g A
            (∇ (fun x : E ↦ ((f∗) x).toReal) (A.adjoint (w k) + 0))
            (w k) L := by
      simpa [hu_eq] using htraj.dual_step k
    simpa using
      (dual_based_proximal_gradient_dual_step_iff_mem_dual_proximal_gradient_primal_y_step
        (σ := σ) (f := f) (g := g) (A := A) (b := 0)
        h_problem.toIsProperExtendedRealFunction h_problem.f_closed
        h_problem.f_strongly_convex h_problem.g_proper h_problem.g_closed
        h_problem.g_convex (y := y (k + 1)) (v := w k) (L := L)).2 hdual_step
  · intro k
    -- The source-facing momentum field is already the canonical shifted recursion.
    simpa [fast_dual_primal_acceleration_eq_fista_momentum (f := f) (g := g) (A := A) htraj k,
      fast_dual_primal_acceleration_eq_fista_momentum (f := f) (g := g) (A := A) htraj (k + 2)]
      using htraj.momentum_step k

/-- Helper for Theorem 12.9: each native Algorithm 12.3 dual step lies in the Chapter 10
prox-gradient step set for the split objective `Fdual + Gdual`. -/
lemma dual_trajectory_step_mem_proximal_gradient_step
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ
      (fun z : V ↦ (g∗) (-z))
      (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
      L y0 y w)
    (k : ℕ) :
    y (k + 1) ∈
      proximal_gradient_step
        (Function.toExtendedReal (fun z : V ↦ ((f∗) (A.adjoint z)).toReal))
        (fun z : V ↦ (g∗) (-z))
        (w k)
        (L : PosReal) := by
  -- Rewrite the native Chapter 12 step owner to the Chapter 10 prox-gradient step owner.
  have hstep :
      y (k + 1) ∈
        dual_based_proximal_gradient_dual_step
          (fun z : V ↦ (g∗) (-z))
          (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
          (L : PosReal)
          (w k) :=
    htraj.dual_step k
  rw [dual_based_proximal_gradient_dual_step_eq_proximal_gradient_step
    (F := Function.toExtendedReal (fun z : V ↦ ((f∗) (A.adjoint z)).toReal))
    (G := fun z : V ↦ (g∗) (-z))
    (gradF := fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
    (L := (L : PosReal))
    (hgradF := fun z ↦ rfl)
    (yk := w k)] at hstep
  simpa using hstep

set_option maxHeartbeats 800000 in
/-- Helper for Theorem 12.9: every positive-index dual iterate lies in the effective domain of
`G(y) = g*(-y)` because it is a prox-gradient step. -/
lemma dual_trajectory_iterate_succ_mem_effective_domain
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ
      (fun z : V ↦ (g∗) (-z))
      (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
      L y0 y w)
    (k : ℕ) :
    y (k + 1) ∈ effective_domain (fun z : V ↦ (g∗) (-z)) := by
  letI : IsProperExtendedRealFunction (fun z : V ↦ (g∗) (-z)) :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g) h_problem.g_proper h_problem.g_convex
  letI : Fact (LowerSemicontinuous (fun z : V ↦ (g∗) (-z))) :=
    ⟨(dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).1⟩
  letI : Fact (is_convex_function (fun z : V ↦ (g∗) (-z))) :=
    ⟨(dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).2⟩
  have hstep_mem :=
    dual_trajectory_step_mem_proximal_gradient_step
      (f := f) (g := g) (A := A) h_problem htraj k
  rw [mem_proximal_gradient_step_iff] at hstep_mem
  exact
    mem_effective_domain_of_mem_scaled_prox_of_pos
      (f := fun z : V ↦ (g∗) (-z))
      (hf_proper := inferInstance)
      (x := _)
      (lam := (1 / (L : PosReal)))
      hstep_mem

set_option maxHeartbeats 800000 in
/-- Helper for Theorem 12.9: the global dual smoothness bound and the admissible parameter `L`
make the Chapter 10 upper-model test hold at every dual base point `w`. -/
lemma dual_upper_model_accepts_at_w
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (wPoint : V)
    [IsProperExtendedRealFunction (fun z : V ↦ (g∗) (-z))]
    [Fact (LowerSemicontinuous (fun z : V ↦ (g∗) (-z)))]
    [Fact (is_convex_function (fun z : V ↦ (g∗) (-z)))] :
    proximal_gradient_backtracking_B2_accepts
      (Function.toExtendedReal (fun z : V ↦ ((f∗) (A.adjoint z)).toReal))
      (fun z : V ↦ (g∗) (-z))
      (L : PosReal)
      (interior_effective_domain_point_of_real
        (fun z : V ↦ ((f∗) (A.adjoint z)).toReal)
        wPoint) := by
  let Fdual : V → ℝ := fun z ↦ ((f∗) (A.adjoint z)).toReal
  let xNext : V := T[(L : PosReal); Fdual, (fun z : V ↦ (g∗) (-z))] wPoint
  have hsmooth :
      is_l_smooth_on Fdual Set.univ
        (Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ)) := by
    -- Lemma 12.3 supplies the global smoothness of `Fdual = f*(Aᵀ ·)`.
    simpa [Fdual] using
      dual_based_proximal_gradient_dual_F_primal_is_l_smooth
        (σ := σ) (f := f) (A := A)
        h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex
  have hLf_le :
      ((Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ) : NNReal) : ℝ) ≤
        (L : ℝ) := by
    -- Rewrite the Chapter 12 smoothness constant to the admissible lower bound `‖A‖² / σ ≤ L`.
    calc
      ((Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ) : NNReal) : ℝ)
          =
          dual_based_proximal_gradient_dual_lipschitz_constant A.toContinuousLinearMap σ := by
            rw [dual_based_proximal_gradient_dual_lipschitz_constant_eq]
            have hσ_nonneg : 0 ≤ 1 / (σ : ℝ) := div_nonneg zero_le_one σ.2.le
            simp only [NNReal.coe_mul, Real.coe_toNNReal _ hσ_nonneg, NNReal.coe_pow,
              coe_nnnorm]
            ring
      _ ≤ (L : ℝ) := DualBasedProximalGradientDualStepsizeParameter.lower_bound L
  have hdescentLf :
      Fdual xNext ≤
        Fdual wPoint +
          inner ℝ (∇ Fdual wPoint) (xNext - wPoint) +
            (((Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ) : NNReal) : ℝ) /
              2) * ‖xNext - wPoint‖ ^ (2 : ℕ) := by
    -- Apply the descent lemma to the split smooth term at the concrete base point `wPoint`.
    have hraw :=
      is_l_smooth_on_descent_lemma
        (L := Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ))
        (D := Set.univ)
        (f := Fdual)
        convex_univ
        hsmooth
        (x := wPoint)
        (y := xNext)
        (by simp)
        (by simp)
    rw [norm_sub_rev] at hraw
    exact hraw
  have hnorm_nonneg : 0 ≤ ‖xNext - wPoint‖ ^ (2 : ℕ) := by
    positivity
  have hdescentL :
      Fdual xNext ≤
        Fdual wPoint +
          inner ℝ (∇ Fdual wPoint) (xNext - wPoint) +
            ((L : ℝ) / 2) * ‖xNext - wPoint‖ ^ (2 : ℕ) := by
    -- Enlarging the curvature from the true smoothness constant to `L` preserves the inequality.
    nlinarith
  -- Repackage the real-valued upper model as the Chapter 10 B2 acceptance predicate.
  refine
    (proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model
      (f := Fdual)
      (g := fun z : V ↦ (g∗) (-z))
      (L := (L : PosReal))
      (y := wPoint)).2 ?_
  simpa [Fdual, xNext]
    using hdescentL

/-- Helper for Theorem 12.9: any attaining dual optimum has finite `G(y) = g*(-y)`-value because
it minimizes `Hdual = Fdual + Gdual` and can be compared to the finite first iterate. -/
lemma dual_optimum_mem_effective_domain
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ
      (fun z : V ↦ (g∗) (-z))
      (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
      L y0 y w)
    {yStar : V}
    (hyStar : q yStar = qOpt) :
    yStar ∈ effective_domain (fun z : V ↦ (g∗) (-z)) := by
  let hG_proper : IsProperExtendedRealFunction (fun z : V ↦ (g∗) (-z)) :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g) h_problem.g_proper h_problem.g_convex
  have hy1_eff :
      y 1 ∈ effective_domain (fun z : V ↦ (g∗) (-z)) :=
    by simpa using
      dual_trajectory_iterate_succ_mem_effective_domain
        (f := f) (g := g) (A := A) h_problem htraj 0
  have hyStar_min :
      yStar ∈ unconstrained_problem_solutions Hdual :=
    dual_terms_minimizer_of_dual_optimum
      (f := f) (g := g) (A := A) σ h_problem hyStar
  have hle : Hdual yStar ≤ Hdual (y 1) :=
    (mem_unconstrained_problem_solutions_iff_forall_le.mp hyStar_min) (y 1)
  have hy1_obj :
      Hdual (y 1) =
        (((((f∗) (A.adjoint (y 1))).toReal + ((g∗) (-y 1)).toReal : ℝ)) : EReal) :=
    dual_terms_objective_eq_real_of_mem_effective_domain
      (f := f) (g := g) (A := A) σ h_problem hy1_eff
  have hHy1_ne_top : Hdual (y 1) ≠ ⊤ := by
    rw [hy1_obj]
    exact EReal.coe_ne_top _
  have hHyStar_ne_top : Hdual yStar ≠ ⊤ := by
    intro htop
    have htop_le : (⊤ : EReal) ≤ Hdual (y 1) := by
      simpa [htop] using hle
    exact hHy1_ne_top (top_unique htop_le)
  have hF_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex yStar
  have hF_val :
      ((((f∗) (A.adjoint yStar)).toReal : ℝ) : EReal) =
        (f∗) (A.adjoint yStar) := by
    exact EReal.coe_toReal hF_finite.2.ne hF_finite.1
  have hG_ne_top : (g∗) (-yStar) ≠ ⊤ := by
    intro hG_top
    have hHyStar_top : Hdual yStar = ⊤ := by
      rw [composite_model_objective_apply, ← hF_val, hG_top]
      simp
    exact hHyStar_ne_top hHyStar_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hG_ne_top)

/-- Helper for Theorem 12.9: the source comparison point
`z_k = (1 / t_(k+1)) y* + (1 - 1 / t_(k+1)) y^k` satisfies the convex objective upper bound used
in the accelerated Lyapunov proof. -/
lemma chapter12_dual_combination_objective_upper_bound
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {yStar yk : V}
    (hyStar_eff : yStar ∈ effective_domain (fun z : V ↦ (g∗) (-z)))
    (hyk_eff : yk ∈ effective_domain (fun z : V ↦ (g∗) (-z)))
    (k : ℕ) :
    let θ : ℝ := (fista_momentum_sequence (k + 1))⁻¹
    let z : V := θ • yStar + (1 - θ) • yk
    Hdual z ≤
      ((((1 - θ) * ((Hdual yk).toReal - (Hdual yStar).toReal) +
          (Hdual yStar).toReal : ℝ)) : EReal) := by
  let hG_proper : IsProperExtendedRealFunction (fun z : V ↦ (g∗) (-z)) :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g) h_problem.g_proper h_problem.g_convex
  let θ : ℝ := (fista_momentum_sequence (k + 1))⁻¹
  let z : V := θ • yStar + (1 - θ) • yk
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using chapter12_one_div_momentum_mem_Icc k
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hθ_le_one : θ ≤ 1 := hθ_mem.2
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_le_one
  have hF_convex_toReal :
      ConvexOn ℝ
        (effective_domain (fun y : V ↦ (f∗) (A.adjoint y)))
        (fun y : V ↦ ((f∗) (A.adjoint y)).toReal) := by
    exact
      convexOn_toReal_of_is_convex_function
        (dual_based_proximal_gradient_dual_F_primal_convex
          (f := f) (A := A))
        (fun y _ ↦
          (dual_based_proximal_gradient_dual_F_primal_finite_valued
            (σ := σ) (f := f) (A := A)
            h_problem.toIsProperExtendedRealFunction h_problem.f_closed
            h_problem.f_strongly_convex y).1)
  have hFstar_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex yStar
  have hFk_finite :=
    dual_based_proximal_gradient_dual_F_primal_finite_valued
      (σ := σ) (f := f) (A := A)
      h_problem.toIsProperExtendedRealFunction h_problem.f_closed h_problem.f_strongly_convex yk
  have hyStar_Feff :
      yStar ∈ effective_domain (fun y : V ↦ (f∗) (A.adjoint y)) :=
    mem_effective_domain.mpr hFstar_finite.2
  have hyk_Feff :
      yk ∈ effective_domain (fun y : V ↦ (f∗) (A.adjoint y)) :=
    mem_effective_domain.mpr hFk_finite.2
  have hz_eff :
      z ∈ effective_domain (fun z : V ↦ (g∗) (-z)) := by
    -- Convexity of the nonsmooth dual term keeps the combination point finite-valued.
    exact
      combo_mem_effective_domain_of_is_convex_function
        (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).2
        hyStar_eff hyk_eff hθ_mem
  have hz_obj :
      Hdual z =
        (((((f∗) (A.adjoint z)).toReal + ((g∗) (-z)).toReal : ℝ)) : EReal) :=
    dual_terms_objective_eq_real_of_mem_effective_domain
      (f := f) (g := g) (A := A) σ h_problem hz_eff
  have hyk_obj :
      Hdual yk =
        (((((f∗) (A.adjoint yk)).toReal + ((g∗) (-yk)).toReal : ℝ)) : EReal) :=
    dual_terms_objective_eq_real_of_mem_effective_domain
      (f := f) (g := g) (A := A) σ h_problem hyk_eff
  have hyStar_obj :
      Hdual yStar =
        (((((f∗) (A.adjoint yStar)).toReal + ((g∗) (-yStar)).toReal : ℝ)) : EReal) :=
    dual_terms_objective_eq_real_of_mem_effective_domain
      (f := f) (g := g) (A := A) σ h_problem hyStar_eff
  have hg_convexE :
      (g∗) (-z) ≤
        (θ : EReal) * (g∗) (-yStar) + ((1 - θ : ℝ) : EReal) * (g∗) (-yk) := by
    -- This is Jensen's inequality for the dual nonsmooth term `G(y) = g*(-y)`.
    simpa [z, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (is_convex_function_iff_segment_ineq.mp
        (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).2)
        yStar hyStar_eff yk hyk_eff hθ_mem
  have hg_convex :
      ((g∗) (-z)).toReal ≤
        θ * ((g∗) (-yStar)).toReal + (1 - θ) * ((g∗) (-yk)).toReal := by
    have hgz_val :
        (((((g∗) (-z)).toReal : ℝ)) : EReal) = (g∗) (-z) := by
      exact EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hG_proper.ne_bot _)
    have hgStar_val :
        (((((g∗) (-yStar)).toReal : ℝ)) : EReal) = (g∗) (-yStar) := by
      exact EReal.coe_toReal (mem_effective_domain.mp hyStar_eff).ne (hG_proper.ne_bot _)
    have hgk_val :
        (((((g∗) (-yk)).toReal : ℝ)) : EReal) = (g∗) (-yk) := by
      exact EReal.coe_toReal (mem_effective_domain.mp hyk_eff).ne (hG_proper.ne_bot _)
    have hg_convex' :
        (((((g∗) (-z)).toReal : ℝ)) : EReal) ≤
          (((((θ * ((g∗) (-yStar)).toReal + (1 - θ) * ((g∗) (-yk)).toReal : ℝ))) : EReal)) := by
      rw [← hgz_val, ← hgStar_val, ← hgk_val] at hg_convexE
      simpa [EReal.coe_add, EReal.coe_mul] using hg_convexE
    exact EReal.coe_le_coe_iff.mp hg_convex'
  have hf_convex :
      ((f∗) (A.adjoint z)).toReal ≤
        θ * ((f∗) (A.adjoint yStar)).toReal + (1 - θ) * ((f∗) (A.adjoint yk)).toReal := by
    have hseg :=
      hF_convex_toReal.2
        hyStar_Feff hyk_Feff hθ_nonneg hone_sub_nonneg (by ring)
    -- The smooth dual term is real-valued everywhere, so its convexity is a direct real inequality.
    simpa [z, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      hseg
  have hz_toReal :
      (Hdual z).toReal =
        ((f∗) (A.adjoint z)).toReal + ((g∗) (-z)).toReal := by
    rw [hz_obj, EReal.toReal_coe]
  have hyk_toReal :
      (Hdual yk).toReal =
        ((f∗) (A.adjoint yk)).toReal + ((g∗) (-yk)).toReal := by
    rw [hyk_obj, EReal.toReal_coe]
  have hyStar_toReal :
      (Hdual yStar).toReal =
        ((f∗) (A.adjoint yStar)).toReal + ((g∗) (-yStar)).toReal := by
    rw [hyStar_obj, EReal.toReal_coe]
  have hupper_real :
      (Hdual z).toReal ≤
        (1 - θ) * ((Hdual yk).toReal - (Hdual yStar).toReal) + (Hdual yStar).toReal := by
    -- Add the real convexity bounds and regroup the `yStar` contribution into the displayed gap.
    rw [hz_toReal, hyk_toReal, hyStar_toReal]
    nlinarith [hf_convex, hg_convex]
  -- Return from the real-valued normalization to the displayed `EReal` inequality.
  simpa [θ, z, hz_obj] using (EReal.coe_le_coe_iff.mpr hupper_real)

-- Proof sketch: identify the displayed FDPG recursion with the constant-stepsize accelerated
-- proximal-gradient method applied to the convex objective `F + G`, where
-- `F(y) = f*(Aᵀ y)` and `G(y) = g*(-y)` are the Chapter 12 primal-space dual terms, so
-- `q(y) = -(F(y) + G(y))`, equivalently
-- `q = dual_based_proximal_gradient_lagrange_dual_objective_primal f g A`.
-- Then apply the standard `O(1 / k^2)` accelerated objective-gap bound to the iterate `y k`, and
-- rewrite the minimum of `F + G` as `-q_opt` using the optimality hypothesis `hyStar`.
/-- The `core/canonical` accelerated dual-gap estimate for the Chapter 12 dual trajectory owner.
-/
theorem fast_dual_proximal_gradient_dual_objective_gap_le_of_dual_trajectory
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (y0 : V) (y w : ℕ → V)
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ
      (fun z : V ↦ (g∗) (-z))
      (fun z : V ↦ ∇ (fun z' : V ↦ ((f∗) (A.adjoint z')).toReal) z)
      L y0 y w)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    qOpt - q (y k) ≤
      ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Route correction: the intended source-faithful proof is to identify the Chapter 12 dual
  -- recursion with constant-stepsize FISTA on `F(y) = ((f∗) (Aᵀ y)).toReal` and
  -- `G(y) = g*(-y)`, then rewrite the Chapter 10 objective gap as `qOpt - q(y^k)`.
  letI : IsProperExtendedRealFunction (fun z : V ↦ (g∗) (-z)) :=
    dual_based_proximal_gradient_dual_G_primal_proper
      (g := g) h_problem.g_proper h_problem.g_convex
  letI : Fact (LowerSemicontinuous (fun z : V ↦ (g∗) (-z))) :=
    ⟨(dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).1⟩
  letI : Fact (is_convex_function (fun z : V ↦ (g∗) (-z))) :=
    ⟨(dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).2⟩
  have hyStar_min :
      yStar ∈
        unconstrained_problem_solutions
          (composite_model_objective
            (fun z : V ↦ ((((f∗) (A.adjoint z)).toReal : ℝ) : EReal))
            (fun z : V ↦ (g∗) (-z))) :=
    dual_terms_minimizer_of_dual_optimum
      (f := f) (g := g) (A := A) σ h_problem hyStar
  have hobjective_eq :
      composite_model_objective
          (fun z : V ↦ ((((f∗) (A.adjoint z)).toReal : ℝ) : EReal))
          (fun z : V ↦ (g∗) (-z))
          (y k) =
        -q (y k) :=
    dual_terms_objective_eq_neg_q (f := f) (g := g) (A := A) σ h_problem (y k)
  have hgap_eq :
      composite_model_objective
          (fun z : V ↦ ((((f∗) (A.adjoint z)).toReal : ℝ) : EReal))
          (fun z : V ↦ (g∗) (-z))
          (y k) -
          (-qOpt) =
        qOpt - q (y k) :=
    dual_terms_objective_gap_eq_dual_gap
      (f := f) (g := g) (A := A) σ h_problem (y k)
  have hstep_mem :
      y (k + 1) ∈
        proximal_gradient_step
          (Function.toExtendedReal (fun z : V ↦ ((f∗) (A.adjoint z)).toReal))
          (fun z : V ↦ (g∗) (-z))
          (w k)
          (L : PosReal) :=
    dual_trajectory_step_mem_proximal_gradient_step
      (f := f) (g := g) (A := A) h_problem htraj k
  have hmodel_accepts :
      proximal_gradient_backtracking_B2_accepts
        (Function.toExtendedReal (fun z : V ↦ ((f∗) (A.adjoint z)).toReal))
        (fun z : V ↦ (g∗) (-z))
        (L : PosReal)
        (interior_effective_domain_point_of_real
          (fun z : V ↦ ((f∗) (A.adjoint z)).toReal)
          (w k)) :=
    dual_upper_model_accepts_at_w
      (f := f) (g := g) (A := A) h_problem L (w k)
  have hstep_norm :
      let θ : ℝ := (fista_momentum_sequence (k + 1))⁻¹
      let z : V := θ • yStar + (1 - θ) • y k
      (fista_momentum_sequence (k + 1) : ℝ) ^ (2 : ℕ) * ‖y (k + 1) - z‖ ^ (2 : ℕ) =
        ‖native_dual_step_residual_to_optimum y yStar k‖ ^ (2 : ℕ) :=
    chapter12_native_step_residual_norm_rewrite
      (y := y) yStar k
  have hbase_norm :
      let θ : ℝ := (fista_momentum_sequence k)⁻¹
      let z : V := θ • yStar + (1 - θ) • y k
    (fista_momentum_sequence k : ℝ) ^ (2 : ℕ) * ‖w k - z‖ ^ (2 : ℕ) =
      ‖native_dual_residual_to_optimum y0 y yStar k‖ ^ (2 : ℕ) :=
    chapter12_native_extrapolated_residual_norm_rewrite
      (f := f) (g := g) (A := A) htraj yStar k
  have hyStar_eff :
      yStar ∈ effective_domain (fun z : V ↦ (g∗) (-z)) :=
    dual_optimum_mem_effective_domain
      (f := f) (g := g) (A := A) h_problem htraj hyStar
  have hyk_eff :
      y k ∈ effective_domain (fun z : V ↦ (g∗) (-z)) := by
    rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
    simpa [Nat.add_comm] using
      dual_trajectory_iterate_succ_mem_effective_domain
        (f := f) (g := g) (A := A) h_problem htraj m
  have hcomparison_upper :
      let θ : ℝ := (fista_momentum_sequence (k + 1))⁻¹
      let z : V := θ • yStar + (1 - θ) • y k
      Hdual z ≤
        ((((1 - θ) * ((Hdual (y k)).toReal - (Hdual yStar).toReal) +
            (Hdual yStar).toReal : ℝ)) : EReal) :=
    chapter12_dual_combination_objective_upper_bound
      (f := f) (g := g) (A := A) σ h_problem hyStar_eff hyk_eff k
  -- TODO: the remaining blocker is now purely the native accelerated-owner rate step. The dual
  -- objective has been normalized to the split minimization surface, the finite-domain transfer
  -- for both `yStar` and `y^k` has been isolated, and the source comparison-point upper bound is
  -- now available as `hcomparison_upper`. The transport-heavy quadratic rewrites are isolated in
  -- `hstep_norm` and `hbase_norm`, with the native extrapolation encoded by
  -- `native_dual_residual_to_optimum`. The first remaining blocker is therefore the one-step
  -- Lyapunov descent obtained by specializing `fundamental_prox_grad_inequality` at the
  -- comparison point and then combining it with `hcomparison_upper`, `hstep_mem`, and
  -- `hmodel_accepts`.
  sorry

-- Proof sketch: pass from the source-facing Algorithm 12.4 trajectory owner to the canonical
-- dual-trajectory owner via
-- `IsFastDualProximalGradientPrimalTrajectory.toDualTrajectory`, then apply the core rate theorem
-- `fast_dual_proximal_gradient_dual_objective_gap_le_of_dual_trajectory`.
/-- Theorem 12.9: under Assumption 12.1, if `(u^k, y^k, w^k, t_k)` is generated by the fast dual
proximal-gradient method with a constant parameter `L ≥ ‖A‖^2 / σ`, then every positive iterate
`y^k` satisfies the accelerated dual-gap estimate
`q_opt - q(y^k) ≤ 2 L ‖y^0 - y^*‖^2 / (k + 1)^2` for any optimal dual solution `y^*`, written
directly with `dual_based_proximal_gradient_lagrange_dual_objective_primal` and the canonical dual
optimal-value owner. -/
theorem fast_dual_proximal_gradient_dual_objective_gap_le
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (y0 : V) (u : ℕ → E) (y w : ℕ → V) (t : ℕ → ℝ)
    (htraj : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    qOpt - q (y k) ≤
      ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
  simpa using
    fast_dual_proximal_gradient_dual_objective_gap_le_of_dual_trajectory
      f g A σ h_problem L y0 y w
      (IsFastDualProximalGradientPrimalTrajectory.toDualTrajectory
        (f := f) (g := g) (A := A) h_problem htraj)
      yStar hyStar k hk

end
