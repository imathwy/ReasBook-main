import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Lemma_10_33
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Theorem_10_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable {x0 xStar : E} {L : ℕ → PosReal} {α : ℝ}
variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]

section

local notation "F" => composite_model_objective f.toExtendedReal g

set_option quotPrecheck false in
local notation "x" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  fista_x f g x0 L

set_option quotPrecheck false in
local notation "y" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  fista_y f g x0 L

set_option quotPrecheck false in
local notation "t" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  fista_t f g x0 L

set_option quotPrecheck false in
local notation "B2Accepts" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  proximal_gradient_backtracking_B2_accepts f.toExtendedReal g

set_option quotPrecheck false in
local notation "UsesB3" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  uses_backtracking_procedure_B3_rule f g y L

/-- Helper for Theorem 10.34: the shifted Lyapunov residual attached to the owner-level FISTA
iterate `x^k` and the optimizer `xStar`. -/
def fista_residual_to_optimum (xStar : E) : ℕ → E
  | 0 => x0 - xStar
  | k + 1 => (t (k + 1) : ℝ) • x (k + 1) - (xStar + (t (k + 1) - 1) • x k)

/-- Helper for Theorem 10.34: the source-indexed Lyapunov residual
`u^k = t_(k-1) x^k - (xStar + (t_(k-1) - 1) x^(k-1))`, with the boundary convention
`u^0 = x0 - xStar`. -/
def fista_lyapunov_residual (xStar : E) : ℕ → E
  | 0 => x0 - xStar
  | k + 1 => (t k : ℝ) • x (k + 1) - (xStar + (t k - 1) • x k)

/-- Helper for Theorem 10.34: at index `1`, the source Lyapunov residual collapses to the plain
distance vector `x^1 - xStar` because `t_0 = 1`. -/
lemma fista_lyapunov_residual_one
    (xStar : E) :
    @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar 1 =
      x 1 - xStar := by
  -- Reduce the residual definition at `k = 1` and cancel the vanishing momentum correction.
  simp [fista_lyapunov_residual, sub_eq_add_neg]

/-- Helper for Theorem 10.34: scaling the post-step displacement from the source combination point
produces the source Lyapunov residual `u^(k+1)`. -/
lemma fista_lyapunov_residual_poststep_rewrite
    (xStar : E) (k : ℕ) :
    let θ : ℝ := (t k)⁻¹
    let z : E := θ • xStar + (1 - θ) • x k
    (t k : ℝ) • (x (k + 1) - z) =
      @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1) := by
  let θ : ℝ := (t k)⁻¹
  let z : E := θ • xStar + (1 - θ) • x k
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.zero_le k
  have haux : (1 : ℝ) ≤ ((k : ℝ) + 2) / 2 := by
    nlinarith
  have ht_ge_one : (1 : ℝ) ≤ t k := by
    exact le_trans haux (fista_t_lower_bound (f := f) (g := g) x0 L k)
  have ht_pos : 0 < t k := lt_of_lt_of_le zero_lt_one ht_ge_one
  have hmul_inv : (t k : ℝ) * (t k)⁻¹ = 1 := by
    field_simp [ht_pos.ne']
  have hcoef :
      (t k : ℝ) * (1 - (t k)⁻¹) = t k - 1 := by
    nlinarith [hmul_inv]
  -- Multiply the source combination-point displacement by `t_k` and cancel the coefficient
  -- `1 / t_k` exactly as in equation `(10.40)`.
  dsimp [z, θ]
  rw [smul_sub, smul_add]
  simp_rw [smul_smul]
  rw [hmul_inv, hcoef]
  simpa [fista_lyapunov_residual, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 10.34: the post-step quadratic term in equation `(10.40)` is the squared
norm of the source Lyapunov residual `u^(k+1)` after the standard `t_k` rescaling. -/
lemma fista_lyapunov_residual_poststep_norm_rewrite
    (xStar : E) (k : ℕ) :
    let θ : ℝ := (t k)⁻¹
    let z : E := θ • xStar + (1 - θ) • x k
    (t k : ℝ) ^ (2 : ℕ) * ‖x (k + 1) - z‖ ^ (2 : ℕ) =
      ‖@fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
        (2 : ℕ) := by
  let θ : ℝ := (t k)⁻¹
  let z : E := θ • xStar + (1 - θ) • x k
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.zero_le k
  have haux : (1 : ℝ) ≤ ((k : ℝ) + 2) / 2 := by
    nlinarith
  have ht_ge_one : (1 : ℝ) ≤ t k := by
    exact le_trans haux (fista_t_lower_bound (f := f) (g := g) x0 L k)
  have ht_pos : 0 < t k := lt_of_lt_of_le zero_lt_one ht_ge_one
  have hscaled :
      (t k : ℝ) • (x (k + 1) - z) =
        @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1) := by
    simpa [θ, z] using
      fista_lyapunov_residual_poststep_rewrite
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
        (Lf := Lf) (x0 := x0) (L := L) (hproblem := hproblem) (xStar := xStar) (k := k)
  -- After the vector identity is fixed, the quadratic term is just `norm_smul`.
  dsimp [θ, z]
  calc
    (t k : ℝ) ^ (2 : ℕ) * ‖x (k + 1) - z‖ ^ (2 : ℕ)
        = ‖(t k : ℝ) • (x (k + 1) - z)‖ ^ (2 : ℕ) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
            ring
    _ = ‖@fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar
          (k + 1)‖ ^ (2 : ℕ) := by
          rw [hscaled]

/-- Helper for Theorem 10.34: at a positive index, the owner-level residual differs from the
source Lyapunov residual only by the explicit momentum-shift correction term. -/
lemma fista_owner_source_residual_decomposition
    (xStar : E) {k : ℕ} (hk : 1 ≤ k) :
    @fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k =
      @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k +
        (t k - t (k - 1)) • (x k - x (k - 1)) := by
  cases k with
  | zero =>
      cases hk
  | succ n =>
      -- Expand both residuals at the same positive index and isolate the one-step shift in the
      -- momentum coefficient.
      simp only [fista_residual_to_optimum, fista_lyapunov_residual, Nat.succ_sub_one,
        sub_eq_add_neg, add_left_comm, add_comm]
      module

/-- Helper for Theorem 10.34: the owner-compatible post-step vector splits into the next source
Lyapunov residual plus the explicit index-shift correction term. -/
lemma fista_poststep_owner_source_decomposition
    (xStar : E) (k : ℕ) :
    let θ : ℝ := (t (k + 1))⁻¹
    let z : E := θ • xStar + (1 - θ) • x k
    (t (k + 1) : ℝ) • (x (k + 1) - z) =
      @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1) +
        (t (k + 1) - t k) • (x (k + 1) - x k) := by
  let θ : ℝ := (t (k + 1))⁻¹
  let z : E := θ • xStar + (1 - θ) • x k
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hk_one : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have haux : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + 2) / 2 := by
    nlinarith
  have ht_ge_one : (1 : ℝ) ≤ t (k + 1) := by
    exact le_trans haux (fista_t_lower_bound (f := f) (g := g) x0 L (k + 1))
  have ht_pos : 0 < t (k + 1) := lt_of_lt_of_le zero_lt_one ht_ge_one
  have hmul_inv : (t (k + 1) : ℝ) * (t (k + 1))⁻¹ = 1 := by
    field_simp [ht_pos.ne']
  have hcoef :
      (t (k + 1) : ℝ) * (1 - (t (k + 1))⁻¹) = t (k + 1) - 1 := by
    nlinarith [hmul_inv]
  -- Expand the owner-compatible post-step displacement and keep the one-step shift as a separate
  -- correction term instead of forcing a false exact residual rewrite.
  dsimp [z, θ]
  rw [smul_sub, smul_add]
  simp_rw [smul_smul]
  rw [hmul_inv, hcoef]
  simp only [fista_lyapunov_residual, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  module

/-- Helper for Theorem 10.34: after normalizing the owner/source index shift at step `k + 1`,
the squared owner residual differs from the squared source residual by the exact scalar correction
from the textbook post-step algebra. -/
lemma fista_owner_source_residual_sqdiff
    (xStar : E) (k : ℕ) :
    ‖@fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
        (2 : ℕ) =
      ‖@fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
          (2 : ℕ) +
        (t (k + 1) - t k) *
          (‖x (k + 1) - xStar‖ ^ (2 : ℕ) - ‖x k - xStar‖ ^ (2 : ℕ)) +
        (t k) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
  let b : E := x k - xStar
  let d : E := x (k + 1) - x k
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have ht_nonneg : 0 ≤ t k := by
    have haux : (0 : ℝ) ≤ (((k : ℕ) : ℝ) + 2) / 2 := by
      positivity
    exact le_trans haux (fista_t_lower_bound (f := f) (g := g) x0 L k)
  have htsucc_nonneg : 0 ≤ t (k + 1) := by
    have haux : (0 : ℝ) ≤ ((((k + 1 : ℕ) : ℝ) + 2) / 2) := by
      positivity
    exact le_trans haux (fista_t_lower_bound (f := f) (g := g) x0 L (k + 1))
  have hu :
      @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1) =
        b + (t k : ℝ) • d := by
    -- Expand the source residual into the current error plus the weighted step displacement.
    dsimp [b, d]
    simp only [fista_lyapunov_residual, sub_eq_add_neg, add_assoc]
    module
  have hw :
      @fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1) =
        b + (t (k + 1) : ℝ) • d := by
    -- The owner-level residual has the same affine form, but with the successor momentum weight.
    dsimp [b, d]
    simp only [fista_residual_to_optimum, sub_eq_add_neg, add_assoc]
    module
  have hnext :
      x (k + 1) - xStar = b + d := by
    -- The next-point error is the current error plus the one-step displacement.
    dsimp [b, d]
    simp only [sub_eq_add_neg, add_assoc]
    module
  have hsource_sq :
      ‖@fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
          (2 : ℕ) =
        ‖b‖ ^ (2 : ℕ) + 2 * (t k) * inner ℝ b d + (t k) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
    -- Expand the source norm square after rewriting it as `b + t_k d`.
    calc
      ‖@fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
          (2 : ℕ)
          = ‖b + (t k : ℝ) • d‖ ^ (2 : ℕ) := by rw [hu]
      _ = ‖b‖ ^ (2 : ℕ) + 2 * inner ℝ b ((t k : ℝ) • d) + ‖(t k : ℝ) • d‖ ^ (2 : ℕ) := by
            simpa using norm_add_sq_real b ((t k : ℝ) • d)
      _ = ‖b‖ ^ (2 : ℕ) + 2 * (t k) * inner ℝ b d + (t k) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
            ring
  have howner_sq :
      ‖@fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
          (2 : ℕ) =
        ‖b‖ ^ (2 : ℕ) + 2 * (t (k + 1)) * inner ℝ b d +
          (t (k + 1)) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
    -- Expand the owner norm square in the same coordinates.
    calc
      ‖@fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
          (2 : ℕ)
          = ‖b + (t (k + 1) : ℝ) • d‖ ^ (2 : ℕ) := by rw [hw]
      _ = ‖b‖ ^ (2 : ℕ) + 2 * inner ℝ b ((t (k + 1) : ℝ) • d) +
            ‖(t (k + 1) : ℝ) • d‖ ^ (2 : ℕ) := by
            simpa using norm_add_sq_real b ((t (k + 1) : ℝ) • d)
      _ = ‖b‖ ^ (2 : ℕ) + 2 * (t (k + 1)) * inner ℝ b d +
            (t (k + 1)) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg htsucc_nonneg]
            ring
  have hnext_sq :
      ‖x (k + 1) - xStar‖ ^ (2 : ℕ) =
        ‖b‖ ^ (2 : ℕ) + 2 * inner ℝ b d + ‖d‖ ^ (2 : ℕ) := by
    -- The displacement identity `x^(k+1) - x* = b + d` gives the usual quadratic expansion.
    calc
      ‖x (k + 1) - xStar‖ ^ (2 : ℕ) = ‖b + d‖ ^ (2 : ℕ) := by rw [hnext]
      _ = ‖b‖ ^ (2 : ℕ) + 2 * inner ℝ b d + ‖d‖ ^ (2 : ℕ) := by
            simpa using norm_add_sq_real b d
  have hmomentum_shift :
      (t (k + 1)) ^ (2 : ℕ) = (t k) ^ (2 : ℕ) + t (k + 1) := by
    -- Convert the standard FISTA momentum identity into the coefficient form needed below.
    rw [fista_t_succ, fista_momentum_update_eq]
    have hsqrt_sq :
        Real.sqrt (1 + 4 * t k ^ (2 : ℕ)) * Real.sqrt (1 + 4 * t k ^ (2 : ℕ)) =
          1 + 4 * t k ^ (2 : ℕ) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 1 + 4 * t k ^ (2 : ℕ) by positivity)]
    nlinarith
  -- After expanding all three norm squares, the remaining statement is a scalar identity.
  rw [howner_sq, hsource_sq, hnext_sq]
  dsimp [b]
  nlinarith [hmomentum_shift]

/-- Helper for Theorem 10.34: the FISTA momentum recursion implies the quadratic identity
`t_(k+1)^2 - t_(k+1) = t_k^2`. -/
lemma fista_momentum_quadratic_identity (k : ℕ) :
    t (k + 1) ^ (2 : ℕ) - t (k + 1) = t k ^ (2 : ℕ) := by
  -- Rewrite the successor momentum through the canonical FISTA update.
  rw [fista_t_succ, fista_momentum_update_eq]
  have hsqrt_sq :
      Real.sqrt (1 + 4 * t k ^ (2 : ℕ)) * Real.sqrt (1 + 4 * t k ^ (2 : ℕ)) =
        1 + 4 * t k ^ (2 : ℕ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + 4 * t k ^ (2 : ℕ) by positivity)]
  -- The scalar identity is then a direct simplification.
  nlinarith

/-- Helper for Theorem 10.34: any trial curvature at least `L_f` satisfies the B3 upper-model
acceptance predicate at the extrapolated point `y^k`. -/
lemma fista_upper_model_accepts_of_stepsize_ge_Lf
    (k : ℕ) (Lbar : PosReal) (hLbar : (Lf : ℝ) ≤ (Lbar : ℝ)) :
    B2Accepts Lbar (interior_effective_domain_point_of_real f (y k)) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- Rewrite B2 acceptance into the displayed upper-model inequality at `y^k`.
  refine
    (proximal_gradient_backtracking_B2_accepts_iff_fista_upper_model f g Lbar (y k)).2 ?_
  let xNext := T[Lbar; f, g] (y k)
  have hy_mem : y k ∈ Set.univ := by
    simp
  have hxNext_mem : xNext ∈ Set.univ := by
    simp [xNext]
  have hdescentLf :
      f xNext ≤
        f (y k) +
          inner ℝ (∇ f (y k)) (xNext - y k) +
            ((Lf : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
    -- The global `L_f`-smoothness field gives the source upper model on `Set.univ`.
    simpa [xNext, norm_sub_rev] using
      (is_l_smooth_on_descent_lemma
        (L := Lf)
        (D := Set.univ)
        (f := f)
        convex_univ
        hproblem.f_smooth
        hy_mem
        hxNext_mem)
  have hnorm_nonneg : 0 ≤ ‖xNext - y k‖ ^ (2 : ℕ) := by
    positivity
  have hdescentLbar :
      f xNext ≤
        f (y k) +
          inner ℝ (∇ f (y k)) (xNext - y k) +
            ((Lbar : ℝ) / 2) * ‖xNext - y k‖ ^ (2 : ℕ) := by
    -- Enlarging the curvature coefficient from `L_f` to `Lbar` preserves the inequality.
    nlinarith
  simpa [xNext] using hdescentLbar

/-- Helper for Theorem 10.34: the accepted B3 curvature is bounded below by the previous trial
curvature and above by `max {η L_f, L_prev}`. -/
lemma fista_b3_local_stepsize_bounds
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hB3 : UsesB3 s η) (k : ℕ) :
    let LPrev := proximal_gradient_backtracking_B2_previous_stepsize s L k
    (LPrev : ℝ) ≤ (L k : ℝ) ∧
      (L k : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (LPrev : ℝ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  rcases hB3 k with ⟨i, hi, hLk⟩
  dsimp
  constructor
  · -- Every accepted B3 trial is `L_prev * η^i`, hence it is at least `L_prev`.
    rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
    have hηge1 : (1 : ℝ) ≤ (η : ℝ) := le_of_lt η.2
    have hLPrev_nonneg :
        0 ≤ (proximal_gradient_backtracking_B2_previous_stepsize s L k : ℝ) := by
      exact le_of_lt (proximal_gradient_backtracking_B2_previous_stepsize s L k).2
    exact le_mul_of_one_le_right hLPrev_nonneg (one_le_pow₀ hηge1)
  · cases i with
    | zero =>
        -- If the first trial is accepted, then `L_k = L_prev`.
        rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
        simp
    | succ m =>
        let LPrev : PosReal := proximal_gradient_backtracking_B2_previous_stepsize s L k
        let Ltrial : PosReal := proximal_gradient_backtracking_trial_stepsize LPrev η m
        have hreject :
            ¬ B2Accepts Ltrial (interior_effective_domain_point_of_real f (y k)) := by
          exact is_backtracking_procedure_B2_index_minimal hi (Nat.lt_succ_self m)
        have htrial_lt_lf : (Ltrial : ℝ) < (Lf : ℝ) := by
          refine lt_of_not_ge fun hnot ↦ ?_
          exact hreject <|
            fista_upper_model_accepts_of_stepsize_ge_Lf (k := k) (Lbar := Ltrial) hnot
        have haccepted_eq :
            (L k : ℝ) = (Ltrial : ℝ) * (η : ℝ) := by
          simp [hLk, Ltrial, LPrev, proximal_gradient_backtracking_trial_stepsize_coe,
            pow_succ, mul_assoc]
        have haccepted_lt :
            (L k : ℝ) < (η : ℝ) * (Lf : ℝ) := by
          have hη_pos : 0 < (η : ℝ) := lt_trans zero_lt_one η.2
          rw [haccepted_eq]
          nlinarith
        exact le_trans (le_of_lt haccepted_lt) (le_max_left _ _)

/-- Helper for Theorem 10.34: if `α = max {η, s / L_f}` with `L_f > 0`, then
`α L_f = max {η L_f, s}`. -/
lemma fista_alpha_mul_lf_eq_max_stepsize
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hLf : 0 < (Lf : ℝ))
    (hα : α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ))) :
    max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) = α * (Lf : ℝ) := by
  -- Split on which branch of the textbook `max` defines `α`.
  rw [hα]
  by_cases hη : (η : ℝ) ≤ (s : ℝ) / (Lf : ℝ)
  · have hs : (s : ℝ) = ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) := by
      field_simp [hLf.ne']
    have hηLf : (η : ℝ) * (Lf : ℝ) ≤ (s : ℝ) := by
      nlinarith
    rw [max_eq_right hηLf, max_eq_right hη]
    exact hs
  · have hηlt : (s : ℝ) / (Lf : ℝ) < (η : ℝ) := lt_of_not_ge hη
    have hsLf : (s : ℝ) < (η : ℝ) * (Lf : ℝ) := by
      have hmul :
          ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) < (η : ℝ) * (Lf : ℝ) := by
        exact mul_lt_mul_of_pos_right hηlt hLf
      have hs :
          ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) = (s : ℝ) := by
        field_simp [hLf.ne']
      rw [hs] at hmul
      exact hmul
    rw [max_eq_left (le_of_lt hsLf), max_eq_left (le_of_lt hηlt)]

/-- Helper for Theorem 10.34: the admissible constant/B3 stepsize rule always yields the uniform
bound `L_k ≤ α L_f`. -/
lemma fista_stepsize_control
    (hrule : hproblem.SublinearRateStepsizeRule y L α) (k : ℕ) :
    (L k : ℝ) ≤ α * (Lf : ℝ) := by
  rcases hrule with ⟨rfl, hconst⟩ | ⟨hLf, s, η, hα, hB3⟩
  · -- In the constant branch, `α = 1` and all curvatures equal `L_f`.
    simpa [hconst k]
  · have hmax :
        max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) = α * (Lf : ℝ) := by
      exact fista_alpha_mul_lf_eq_max_stepsize (Lf := Lf) hLf hα
    induction k with
    | zero =>
        -- The initial accepted curvature is controlled by the first local B3 comparison.
        have hlocal := fista_b3_local_stepsize_bounds (Lf := Lf) (hB3 := hB3) 0
        simpa [proximal_gradient_backtracking_B2_previous_stepsize_zero, hmax] using hlocal.2
    | succ k ih =>
        have hη_le : (η : ℝ) * (Lf : ℝ) ≤ α * (Lf : ℝ) := by
          have hηα : (η : ℝ) ≤ α := by
            rw [hα]
            exact le_max_left _ _
          nlinarith
        have hstep :
            (L (k + 1) : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (L k : ℝ) := by
          have hlocal :=
            fista_b3_local_stepsize_bounds (Lf := Lf) (hB3 := hB3) (k + 1)
          simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using hlocal.2
        have hmax_le : max ((η : ℝ) * (Lf : ℝ)) (L k : ℝ) ≤ α * (Lf : ℝ) := by
          exact max_le hη_le ih
        exact le_trans hstep hmax_le

/-- Helper for Theorem 10.34: every admissible FISTA stepsize is at least the previous accepted
curvature estimate. -/
lemma fista_stepsize_mono
    (hrule : hproblem.SublinearRateStepsizeRule y L α) {k : ℕ} (hk : 1 ≤ k) :
    (L (k - 1) : ℝ) ≤ (L k : ℝ) := by
  rcases hrule with ⟨rfl, hconst⟩ | ⟨_, s, η, _, hB3⟩
  · cases k with
    | zero =>
        cases hk
    | succ n =>
        -- Under the constant rule all curvatures equal `L_f`.
        simpa [hconst n, hconst (n + 1)]
  · cases k with
    | zero =>
        cases hk
    | succ n =>
        -- In the B3 branch, the accepted trial at step `n + 1` is at least the previous value `L_n`.
        simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using
          (fista_b3_local_stepsize_bounds (hB3 := hB3) (n + 1)).1

/-- Helper for Theorem 10.34: multiplying the FISTA extrapolation formula by `t_(k+1)` rewrites
the affine term into the previous Lyapunov residual. -/
lemma fista_scaled_extrapolation_residual
    (xStar : E) (k : ℕ) :
    (t (k + 1) : ℝ) • y k - (xStar + (t (k + 1) - 1) • x k) =
      @fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k := by
  cases k with
  | zero =>
      -- At the base index, `y^0 = x^0 = x0`, so the displayed residual is pure affine
      -- cancellation and matches the `0`-branch of `fista_residual_to_optimum`.
      simp only [fista_residual_to_optimum, fista_y_zero, fista_x_zero, sub_eq_add_neg]
      module
  | succ k =>
      letI : IsProperExtendedRealFunction g := hproblem.g_proper
      letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
      letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
      have ht_lb := fista_t_lower_bound (f := f) (g := g) x0 L (k + 2)
      have ht_pos : 0 < t (k + 2) := by
        -- The standard momentum lower bound keeps every denominator in the extrapolation formula
        -- strictly positive.
        have hk_two_nat : 2 ≤ k + 2 := Nat.le_add_left 2 k
        have hk_two : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
          exact_mod_cast hk_two_nat
        have htwo_lhs : (2 : ℝ) ≤ ((((k + 2 : ℕ) : ℝ) + 2) / 2) := by
          nlinarith [hk_two]
        have htwo : (2 : ℝ) ≤ t (k + 2) := by
          linarith
        linarith
      have ht_pos' : 0 < t (k + 1 + 1) := by
        simpa [Nat.add_assoc] using ht_pos
      have hinv : (t (k + 1 + 1) : ℝ) * (t (k + 1 + 1))⁻¹ = 1 := by
        field_simp [ht_pos'.ne']
      have hprod :
          (t (k + 1 + 1) : ℝ) * ((t (k + 1) - 1) * (t (k + 1 + 1))⁻¹) = t (k + 1) - 1 := by
        calc
          (t (k + 1 + 1) : ℝ) * ((t (k + 1) - 1) * (t (k + 1 + 1))⁻¹) =
            (t (k + 1) - 1) * ((t (k + 1 + 1) : ℝ) * (t (k + 1 + 1))⁻¹) := by
              rw [mul_left_comm (t (k + 1 + 1)) (t (k + 1) - 1) ((t (k + 1 + 1))⁻¹)]
          _ = t (k + 1) - 1 := by simp [hinv]
      -- Expand `y^(k+1)`, cancel the extrapolation denominator at the scalar level, and then
      -- collect the remaining affine terms into the shifted residual.
      rw [fista_y_succ, div_eq_mul_inv]
      simp_rw [smul_add, smul_sub, smul_smul]
      rw [hprod]
      simp only [fista_residual_to_optimum, sub_eq_add_neg, add_assoc]
      module

/-- Helper for Theorem 10.34: the quadratic terms in equation `(10.40)` are exactly the squared
norms of the owner-level residuals once the source combination point is rescaled by `t_(k+1)`. -/
lemma fista_residual_norm_rewrite
    (xStar : E) (k : ℕ) :
    let θ : ℝ := (t (k + 1))⁻¹
    let z : E := θ • xStar + (1 - θ) • x k
    (t (k + 1) : ℝ) ^ (2 : ℕ) * ‖x (k + 1) - z‖ ^ (2 : ℕ) =
        ‖@fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
            (2 : ℕ) ∧
      (t (k + 1) : ℝ) ^ (2 : ℕ) * ‖y k - z‖ ^ (2 : ℕ) =
        ‖@fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k‖ ^
            (2 : ℕ) := by
  let θ : ℝ := (t (k + 1))⁻¹
  let z : E := θ • xStar + (1 - θ) • x k
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hk_one : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have haux : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + 2) / 2 := by
    nlinarith
  have ht_ge_one : (1 : ℝ) ≤ t (k + 1) := by
    exact le_trans haux (fista_t_lower_bound (f := f) (g := g) x0 L (k + 1))
  have ht_pos : 0 < t (k + 1) := lt_of_lt_of_le zero_lt_one ht_ge_one
  have hmul_inv : (t (k + 1) : ℝ) * (t (k + 1))⁻¹ = 1 := by
    field_simp [ht_pos.ne']
  have hcoef :
      (t (k + 1) : ℝ) * (1 - (t (k + 1))⁻¹) = t (k + 1) - 1 := by
    nlinarith [hmul_inv]
  have hx_scaled :
      (t (k + 1) : ℝ) • (x (k + 1) - z) =
        @fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1) := by
    -- Multiply the combination-point displacement by `t_(k+1)` and cancel the coefficient
    -- `1 / t_(k+1)` exactly as in equation `(10.40)`.
    dsimp [z, θ]
    rw [smul_sub, smul_add]
    simp_rw [smul_smul]
    rw [hmul_inv, hcoef]
    simpa [fista_residual_to_optimum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hy_scaled :
      (t (k + 1) : ℝ) • (y k - z) =
        @fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k := by
    -- The same rescaling turns the pre-step term into the previous owner-level residual.
    dsimp [z, θ]
    rw [smul_sub, smul_add]
    simp_rw [smul_smul]
    rw [hmul_inv, hcoef]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      fista_scaled_extrapolation_residual
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
        (x0 := x0) (L := L) (hproblem := hproblem) (xStar := xStar) (k := k)
  dsimp [θ, z]
  constructor
  · -- After the vector identity is fixed, the norm term is just `norm_smul`.
    calc
      (t (k + 1) : ℝ) ^ (2 : ℕ) * ‖x (k + 1) - z‖ ^ (2 : ℕ)
          = ‖(t (k + 1) : ℝ) • (x (k + 1) - z)‖ ^ (2 : ℕ) := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
              ring
      _ =
          ‖@fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar
              (k + 1)‖ ^ (2 : ℕ) := by
            rw [hx_scaled]
  · -- The pre-step quadratic term rewrites in the same way.
    calc
      (t (k + 1) : ℝ) ^ (2 : ℕ) * ‖y k - z‖ ^ (2 : ℕ)
          = ‖(t (k + 1) : ℝ) • (y k - z)‖ ^ (2 : ℕ) := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
              ring
      _ = ‖@fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k‖ ^
            (2 : ℕ) := by
            rw [hy_scaled]

/-- Helper for Theorem 10.34: any optimizer in `XStar` attains the composite objective value
`FOpt`. -/
lemma fista_objective_eq_optimal_value_of_mem_optimal_set
    (hfast : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (hxStar : xStar ∈ XStar) :
    F xStar = (FOpt : EReal) := by
  -- Unpack the optimal-set field directly so the helper stays on the owner-level API.
  apply le_antisymm
  · exact hfast.optimal_value_isGLB.2 <| by
      rintro a ⟨zPoint, rfl⟩
      have hxStar_opt : xStar ∈ unconstrained_problem_solutions F := by
        simpa [hfast.optimal_set_eq] using hxStar
      exact (mem_unconstrained_problem_solutions_iff_forall_le.mp hxStar_opt) zPoint
  · simpa using hfast.optimal_value_isGLB.1 ⟨xStar, rfl⟩

/-- Helper for Theorem 10.34: every optimizer has finite `g`-value, hence belongs to
`effective_domain g`. -/
lemma fista_optimal_point_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    fista_objective_eq_optimal_value_of_mem_optimal_set
      (xStar := xStar) (hfast := hproblem) hxStar
  have hg_top : g xStar ≠ ⊤ := by
    intro hg_top
    have hFx_top : F xStar = ⊤ := by
      simp [composite_model_objective_apply, Function.toExtendedReal, hg_top]
    rw [hFx_top] at hxStar_value
    simpa using hxStar_value
  -- Finite `g`-value is exactly membership in the effective domain.
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_top)

/-- Helper for Theorem 10.34: every positive-index FISTA iterate lies in `effective_domain g`
because each iterate is a prox-gradient step. -/
lemma fista_iterate_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {k : ℕ} (hk : 1 ≤ k) :
    x k ∈ effective_domain g := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  cases k with
  | zero =>
      cases hk
  | succ n =>
      -- Rewrite the successor iterate to the prox-gradient point and use Theorem 10.16.
      rw [fista_x_succ (f := f) (g := g) (x0 := x0) (L := L) n]
      simpa using
        (prox_grad_step_mem_effective_domain_g
          (f := f.toExtendedReal) (g := g)
          (interior_effective_domain_point_of_real f (y n))
          (L n))

/-- Helper for Theorem 10.34: on `effective_domain g`, the composite objective is the real sum
`f x + g(x).toReal`. -/
lemma fista_objective_eq_real_of_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    F xPoint = ((((f xPoint + (g xPoint).toReal : ℝ))) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hgx_val :
      g xPoint = ((((g xPoint).toReal : ℝ)) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne (hg_proper.ne_bot xPoint)).symm
  -- Once `g x` is finite, the objective is just a sum of real casts.
  rw [composite_model_objective_apply, Function.toExtendedReal, hgx_val]
  simp

/-- Helper for Theorem 10.34: the source weight `1 / t_(k+1)` is a genuine convex-combination
coefficient. -/
lemma fista_one_div_t_mem_Icc
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (k : ℕ) :
    ((t (k + 1))⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have ht_ge_one : (1 : ℝ) ≤ t (k + 1) := by
    have hbound := fista_t_lower_bound (f := f) (g := g) x0 L (k + 1)
    have hk_one : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have haux : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) + 2) / 2 := by
      nlinarith
    exact le_trans haux hbound
  have ht_pos : 0 < t (k + 1) := lt_of_lt_of_le zero_lt_one ht_ge_one
  refine ⟨inv_nonneg.mpr (le_of_lt ht_pos), ?_⟩
  have hrecip : 1 / t (k + 1) ≤ 1 / (1 : ℝ) :=
    one_div_le_one_div_of_le zero_lt_one ht_ge_one
  simpa [one_div] using hrecip

/-- Helper for Theorem 10.34: at any iterate with finite `g`-value, the convex-combination point
`(1 / t_(k+1)) x* + (1 - 1 / t_(k+1)) x^k` satisfies the source objective upper bound coming from
convexity of `f` and `g`. -/
lemma fista_combination_objective_upper_bound
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (hxStar : xStar ∈ XStar)
    {k : ℕ} (hxk : x k ∈ effective_domain g) :
    let θ : ℝ := (t (k + 1))⁻¹
    let z : E := θ • xStar + (1 - θ) • x k
    F z ≤
      ((((1 - θ) * ((F (x k)).toReal - FOpt) + FOpt : ℝ)) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  let θ : ℝ := (t (k + 1))⁻¹
  let z : E := θ • xStar + (1 - θ) • x k
  have hxStar_eff : xStar ∈ effective_domain g :=
    fista_optimal_point_mem_effective_domain (xStar := xStar) hproblem hxStar
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using
      fista_one_div_t_mem_Icc
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
        (Lf := Lf) (x0 := x0) (L := L) hproblem k
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hθ_le_one : θ ≤ 1 := hθ_mem.2
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_le_one
  have hθ_sum : θ + (1 - θ) = 1 := by ring
  have hz_eff : z ∈ effective_domain g := by
    -- Convexity of `g` keeps the source combination point in the effective domain.
    exact combo_mem_effective_domain_of_is_convex_function hproblem.g_convex
      hxStar_eff hxk hθ_mem
  have hz_obj :
      F z = ((((f z + (g z).toReal : ℝ))) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain
      (xPoint := z) hproblem hz_eff
  have hxk_obj :
      F (x k) = ((((f (x k) + (g (x k)).toReal : ℝ))) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain
      (xPoint := x k) hproblem hxk
  have hxStar_obj :
      F xStar = ((((f xStar + (g xStar).toReal : ℝ))) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain
      (xPoint := xStar) hproblem hxStar_eff
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    fista_objective_eq_optimal_value_of_mem_optimal_set
      (xStar := xStar) (hfast := hproblem) hxStar
  have hxStar_toReal :
      f xStar + (g xStar).toReal = FOpt := by
    have hxStar_value' :
        ((((f xStar + (g xStar).toReal : ℝ))) : EReal) = (FOpt : EReal) := by
      simpa [hxStar_obj] using hxStar_value
    exact EReal.coe_eq_coe_iff.mp hxStar_value'
  have hxk_toReal :
      (F (x k)).toReal = f (x k) + (g (x k)).toReal := by
    rw [hxk_obj, EReal.toReal_coe]
  have hg_convexE :
      g z ≤
        (θ : EReal) * g xStar + ((1 - θ : ℝ) : EReal) * g (x k) := by
    -- This is the source Jensen inequality for the nonsmooth term.
    simpa [z, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (is_convex_function_iff_segment_ineq.mp hproblem.g_convex)
        xStar hxStar_eff (x k) hxk hθ_mem
  have hg_convex :
      (g z).toReal ≤ θ * (g xStar).toReal + (1 - θ) * (g (x k)).toReal := by
    have hgxStar_val :
        g xStar = ((((g xStar).toReal : ℝ)) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxStar_eff).ne
        (hproblem.g_proper.ne_bot xStar)).symm
    have hgxk_val :
        g (x k) = ((((g (x k)).toReal : ℝ)) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxk).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hgz_val :
        g z = ((((g z).toReal : ℝ)) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hg_convex' :
        ((((g z).toReal : ℝ)) : EReal) ≤
          (((((θ * (g xStar).toReal + (1 - θ) * (g (x k)).toReal : ℝ))) : EReal)) := by
      rw [hgz_val, hgxStar_val, hgxk_val] at hg_convexE
      simpa [EReal.coe_add, EReal.coe_mul] using hg_convexE
    exact EReal.coe_le_coe_iff.mp hg_convex'
  have hf_convex :
      f z ≤ θ * f xStar + (1 - θ) * f (x k) := by
    have hseg :=
      hproblem.f_convex.2
        (show xStar ∈ Set.univ by simp)
        (show x k ∈ Set.univ by simp)
        hθ_nonneg hone_sub_nonneg hθ_sum
    -- Specialize convexity of `f` to the same source combination point.
    simpa [z, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      hseg
  have hz_toReal :
      (F z).toReal = f z + (g z).toReal := by
    rw [hz_obj, EReal.toReal_coe]
  have hupper_real :
      (F z).toReal ≤
        (1 - θ) * ((F (x k)).toReal - FOpt) + FOpt := by
    -- Add the smooth and nonsmooth convexity bounds, then replace `F x*` by `FOpt`.
    rw [hz_toReal, hxk_toReal]
    nlinarith [hf_convex, hg_convex, hxStar_toReal]
  -- Return to `EReal` after the real inequality has been normalized.
  simpa [θ, z, hz_obj] using (EReal.coe_le_coe_iff.mpr hupper_real)

/-- Helper for Theorem 10.34: convexity of the smooth term gives the supporting hyperplane
inequality at any base point. -/
lemma fista_convex_support_at_basepoint
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (xPoint yPoint : E) :
    f xPoint ≥ f yPoint + inner ℝ (∇ f yPoint) (xPoint - yPoint) := by
  have hconv : ConvexOn ℝ Set.univ f := hproblem.f_convex
  let line : ℝ → E := AffineMap.lineMap yPoint xPoint
  let φ : ℝ → ℝ := fun s ↦ f (line s)
  have hφ_convex : ConvexOn ℝ Set.univ φ := by
    -- Restrict the global convexity of `f` to the segment from `y` to `x`.
    simpa [φ, line] using
      hconv.comp_affineMap (AffineMap.lineMap (k := ℝ) yPoint xPoint)
  have hy_diff : DifferentiableAt ℝ f yPoint := hproblem.f_smooth.1 yPoint (by simp)
  have hline : HasDerivAt line (xPoint - yPoint) 0 := by
    simpa [line] using
      (show HasDerivAt (AffineMap.lineMap yPoint xPoint) (xPoint - yPoint) (0 : ℝ) from
        AffineMap.hasDerivAt_lineMap)
  have hφ_deriv : HasDerivAt φ (inner ℝ (∇ f yPoint) (xPoint - yPoint)) 0 := by
    -- Differentiate the segment restriction at the left endpoint and identify the derivative with
    -- the ambient gradient paired against the segment direction.
    have hcomp : HasDerivAt φ (fderiv ℝ f yPoint (xPoint - yPoint)) 0 := by
      have hbase : HasFDerivAt f (fderiv ℝ f yPoint) (line 0) := by
        simpa [line] using hy_diff.hasFDerivAt
      simpa [φ, line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
    have hgrad :
        fderiv ℝ f yPoint (xPoint - yPoint) =
          inner ℝ (∇ f yPoint) (xPoint - yPoint) := by
      simpa using
        (show
            fderiv ℝ f yPoint (xPoint - yPoint) =
              inner ℝ (∇ f yPoint) (xPoint - yPoint) from
          HasGradientAt.fderiv_apply hy_diff.hasGradientAt)
    simpa [hgrad] using hcomp
  have hsecant : inner ℝ (∇ f yPoint) (xPoint - yPoint) ≤ slope φ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hφ_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hφ_deriv
  have hsecant' : inner ℝ (∇ f yPoint) (xPoint - yPoint) ≤ f xPoint - f yPoint := by
    simpa [φ, line, slope] using hsecant
  linarith

/-- Helper for Theorem 10.34: the optimal value is a lower bound for every FISTA objective value,
which is the order-theoretic form of nonnegativity of the objective gap. -/
lemma fista_objective_gap_nonneg
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (n : ℕ) :
    (FOpt : EReal) ≤ F (x n) := by
  -- This is exactly the greatest-lower-bound clause from the standing fast problem.
  exact hproblem.optimal_value_isGLB.1 ⟨x n, rfl⟩

/-- Helper for Theorem 10.34: every positive-index FISTA objective gap is finite, so its real
value casts back to the displayed `EReal` gap `F(x^n) - F_opt`. -/
lemma fista_positive_iterate_gap_coe
    {n : ℕ} (hn : 1 ≤ n) :
    ((((F (x n)).toReal - FOpt : ℝ)) : EReal) = F (x n) - (FOpt : EReal) := by
  have hxn_eff : x n ∈ effective_domain g :=
    fista_iterate_mem_effective_domain
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) hproblem hn
  have hxn_obj :
      F (x n) = ((((f (x n) + (g (x n)).toReal : ℝ))) : EReal) :=
    fista_objective_eq_real_of_mem_effective_domain
      (xPoint := x n) hproblem hxn_eff
  -- Rewrite the iterate value through its finite real representative, then simplify the
  -- `EReal` subtraction as an ordinary real subtraction.
  rw [hxn_obj]
  rw [EReal.toReal_coe]
  simp [EReal.coe_sub]

/-- Helper for Theorem 10.34: every positive-index FISTA objective gap is nonnegative as a real
number, once the finite-value transport from `EReal` has been isolated. -/
lemma fista_positive_iterate_gap_nonneg
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (F (x n)).toReal - FOpt := by
  have hgapE :
      (0 : EReal) ≤ F (x n) - (FOpt : EReal) := by
    -- Convert the global lower bound `F_opt ≤ F(x^n)` into nonnegativity of the shifted gap.
    exact (EReal.sub_nonneg (Or.inr (by simp)) (Or.inr (by simp))).2 <|
      fista_objective_gap_nonneg
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
        (Lf := Lf) (x0 := x0) (L := L) hproblem n
  have hgapE' :
      (0 : EReal) ≤ ((((F (x n)).toReal - FOpt : ℝ)) : EReal) := by
    rw [fista_positive_iterate_gap_coe
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) (n := n) hn]
    exact hgapE
  -- Strip the final `EReal` cast to recover the real nonnegativity statement.
  exact EReal.coe_nonneg.mp hgapE'

/- Theorem 10.34 is `source-facing` in the fast proximal-gradient analysis.

Domain sampling in the existing Chapter 10 API identifies:
- `IsFastProximalGradientProblem` as the owner of Assumption 10.31;
- `fista f g x0 L` from Algorithm 10.6 as the canonical FISTA state trajectory owner;
- `fista_x f g x0 L` and `fista_y f g x0 L` from Algorithm 10.6 as the derived iterate and
  extrapolated sequences attached to that owner;
- `hproblem.SublinearRateStepsizeRule (fista_y f g x0 L) L α` from Algorithm 10.6 as the
  canonical owner-level bridge for the admissible constant/B3 stepsize regimes and the
  auxiliary constant `α`.

Layer triage:
- `source-facing`: the accelerated objective-gap theorem stated for the canonical FISTA iterates;
- `core/canonical`: `composite_model_objective`, `fista f g x0 L`, and
  `fast_proximal_gradient_sublinear_rate_stepsize_rule f g Lf`;
- `bridge/view`: `hproblem.SublinearRateStepsizeRule (fista_y f g x0 L) L α`, the optimizer
  membership hypothesis `xStar ∈ XStar`, and the canonical derived views `fista_x f g x0 L`
  and `fista_y f g x0 L`.

Primitive data are the standing problem assumptions, the initial point `x0`, the curvature
schedule `L`, the optimizer `xStar`, and the admissible stepsize regime. The concrete sequences
`x^k` and `y^k` are derived API from the FISTA owner `fista f g x0 L`, so the theorem should
reuse those canonical views on the theorem surface, with theorem-local notation exposing the
canonical derived views rather than introducing parallel wrapper declarations while the standing
fast problem supplies the regularity of `g` locally. -/

-- Proof sketch: combine the fundamental prox-gradient inequality with the FISTA extrapolation
-- identity, rewrite the resulting estimate in terms of the Lyapunov quantity
-- `‖u^k‖² + (2 / L_(k-1)) t_(k-1)^2 (F(x^k) - F_opt)`, telescope this recursion, bound the
-- initial energy by `‖x^0 - x*‖²`, and then use the lower bound on `t_(k-1)` together with the
-- constant/B3 stepsize bound `L_(k-1) ≤ α L_f` to obtain the `O(1 / k^2)` objective estimate.
/-- Theorem 10.34: under Assumption 10.31, if the FISTA iterates use either the constant
stepsize rule `L_k = L_f` with `α = 1` or backtracking procedure B3 with
`α = max {η, s / L_f}`, then for every optimizer `xStar ∈ X^*` and every `k ≥ 1` one has
`F(x^k) - F_opt ≤ 2 α L_f ‖x^0 - xStar‖² / (k + 1)^2`. -/
theorem fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq
    (hrule : hproblem.SublinearRateStepsizeRule y L α)
    (hxStar : xStar ∈ XStar) (k : ℕ) (hk : 1 ≤ k) :
    F (x k) - (FOpt : EReal) ≤
      ((2 * α * (Lf : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) / (k + 1 : ℝ) ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Route correction: the exact source pre-step identity `(10.42)` and the owner/source post-step
  -- decomposition are now separated. The remaining blocker is the quadratic energy bridge that
  -- pays for the post-step correction term by a `gap (k + 1)` budget; it is no longer an indexing
  -- mismatch in the raw vectors.
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    fista_objective_eq_optimal_value_of_mem_optimal_set
      (xStar := xStar) hproblem hxStar
  have hgapk_coe :
      ((((F (x k)).toReal - FOpt : ℝ)) : EReal) = F (x k) - (FOpt : EReal) :=
    fista_positive_iterate_gap_coe
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) (n := k) hk
  have hgapk_nonneg :
      0 ≤ (F (x k)).toReal - FOpt :=
    fista_positive_iterate_gap_nonneg
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) (n := k) hk
  have hu_one :
      @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar 1 =
        x 1 - xStar :=
    fista_lyapunov_residual_one
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) (hproblem := hproblem) (xStar := xStar)
  have hprestep :
      (t (k + 1) : ℝ) • y k - (xStar + (t (k + 1) - 1) • x k) =
        @fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k :=
    fista_scaled_extrapolation_residual
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) (hproblem := hproblem) (xStar := xStar) k
  have hprestep_shift :
      @fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k =
        @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar k +
          (t k - t (k - 1)) • (x k - x (k - 1)) :=
    fista_owner_source_residual_decomposition
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) (hproblem := hproblem) (xStar := xStar) hk
  have hpoststep :
      let θ : ℝ := (t (k + 1))⁻¹
      let z : E := θ • xStar + (1 - θ) • x k
      (t (k + 1) : ℝ) • (x (k + 1) - z) =
        @fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1) +
          (t (k + 1) - t k) • (x (k + 1) - x k) :=
    fista_poststep_owner_source_decomposition
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) (hproblem := hproblem) (xStar := xStar) k
  have hsqdiff :
      ‖@fista_residual_to_optimum E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
          (2 : ℕ) =
        ‖@fista_lyapunov_residual E _ _ _ f g XStar FOpt Lf x0 L hproblem xStar (k + 1)‖ ^
            (2 : ℕ) +
          (t (k + 1) - t k) *
            (‖x (k + 1) - xStar‖ ^ (2 : ℕ) - ‖x k - xStar‖ ^ (2 : ℕ)) +
          (t k) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) :=
    fista_owner_source_residual_sqdiff
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x0 := x0) (L := L) (hproblem := hproblem) (xStar := xStar) k
  -- TODO: combine `fundamental_prox_grad_inequality`, `fista_combination_objective_upper_bound`,
  -- the owner pre-step rewrite `hprestep`, the same-index source bridge `hprestep_shift`, the
  -- exact squared-norm normalization `hsqdiff`, and the new post-step decomposition with the still
  -- missing scalar estimate that controls the correction term by
  -- `(2 / L_k) * t_(k+1) * gap_(k+1)`. Once that bridge is proved, the source-energy telescope
  -- and the scalar finish should follow from `fista_momentum_quadratic_identity`,
  -- `fista_stepsize_mono`, `fista_stepsize_control`, and `fista_t_lower_bound`.
  clear hu_one hprestep hprestep_shift hpoststep hsqdiff
  sorry

end

end
