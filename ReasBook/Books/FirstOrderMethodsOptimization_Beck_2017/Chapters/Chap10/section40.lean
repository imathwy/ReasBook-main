import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_10_40 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]
variable {x y z : ℕ → E} {t : ℕ → ℝ} {L : ℕ → PosReal} {xStar : E} {α : ℝ}

local notation "F" => composite_model_objective f.toEReal g

set_option quotPrecheck false in
local notation "B2Accepts" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  proximal_gradient_backtracking_B2_accepts f.toEReal g

set_option quotPrecheck false in
local notation "UsesB3" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  uses_backtracking_procedure_B3_rule f g y L

/-- Helper for Theorem 10.40: the source post-step residual attached to the MFISTA iterate and an
optimizer `xStar`. -/
def mfista_residual_to_optimum (xStar : E) : ℕ → E
  | 0 => x 0 - xStar
  | k + 1 => (t k : ℝ) • z k - (xStar + (t k - 1) • x k)

/-- Helper for Theorem 10.40: the FISTA momentum recursion implies the quadratic identity
`t_(k+1)^2 - t_(k+1) = t_k^2`. -/
lemma mfista_momentum_quadratic_identity
    (htraj : hproblem.IsMfistaTrajectory x y z t L) (k : ℕ) :
    t (k + 1) ^ (2 : ℕ) - t (k + 1) = t k ^ (2 : ℕ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- Rewrite the successor momentum through the canonical FISTA update.
  rw [is_mfista_trajectory_t_succ htraj, fista_momentum_update_eq]
  have hsqrt_sq :
      Real.sqrt (1 + 4 * t k ^ (2 : ℕ)) * Real.sqrt (1 + 4 * t k ^ (2 : ℕ)) =
        1 + 4 * t k ^ (2 : ℕ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + 4 * t k ^ (2 : ℕ) by positivity)]
  -- The displayed identity is then a direct scalar simplification.
  nlinarith

/-- Helper for Theorem 10.40: for positive indices, the current MFISTA owner rewrites `y^k`
using the coefficient `mfista_previous_momentum t (k - 1) - 1` in the last affine term. -/
lemma mfista_extrapolation_step
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (k : ℕ) (hk : 1 ≤ k) :
    y k =
      x k +
        (t (k - 1) / t k) • (z (k - 1) - x k) +
        ((mfista_previous_momentum t (k - 1) - 1) / t k) • (x k - x (k - 1)) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  rcases Nat.exists_eq_add_of_le hk with ⟨n, rfl⟩
  -- Reindex the successor-form MFISTA owner to obtain the exact statement at index `n + 1`.
  simpa [Nat.add_comm] using is_mfista_trajectory_y_succ htraj n

/-- Helper for Theorem 10.40: any optimizer in `XStar` attains the composite objective value
`FOpt`. -/
lemma mfista_objective_eq_optimal_value_of_mem_optimal_set
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (hxStar : xStar ∈ XStar) :
    F xStar = (FOpt : EReal) := by
  -- Pass to the canonical convex-composite owner and reuse its optimizer-value identity.
  simpa using
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      (h :=
        IsFastProximalGradientProblem.toIsConvexCompositeSmoothMinimizationProblem
          hproblem)
      hxStar

/-- Helper for Theorem 10.40: every MFISTA momentum parameter is strictly positive. -/
lemma mfista_momentum_pos
    (htraj : hproblem.IsMfistaTrajectory x y z t L) (k : ℕ) :
    0 < t k := by
  have hbound := hproblem.isMfistaTrajectory_t_lower_bound htraj k
  have hpos : 0 < (((k : ℝ) + 2) / 2) := by
    positivity
  -- The lower bound from Lemma 10.33 keeps every denominator in the MFISTA extrapolation positive.
  exact lt_of_lt_of_le hpos hbound

/-- Helper for Theorem 10.40: any trial curvature at least `L_f` satisfies the B3 upper-model
acceptance predicate at the MFISTA extrapolated point `y^k`. -/
lemma mfista_upper_model_accepts_of_stepsize_ge_Lf
    (k : ℕ) (Lbar : PosReal) (hLbar : (Lf : ℝ) ≤ (Lbar : ℝ)) :
    B2Accepts Lbar (interior_effective_domain_point_of_real f (y k)) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- Rewrite B3 acceptance into the displayed upper-model inequality at `y^k`.
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

/-- Helper for Theorem 10.40: the accepted B3 curvature is bounded below by the previous trial
curvature and above by `max {η L_f, L_prev}`. -/
lemma mfista_b3_local_stepsize_bounds
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
            mfista_upper_model_accepts_of_stepsize_ge_Lf (k := k) (Lbar := Ltrial) hnot
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

/-- Helper for Theorem 10.40: if `α = max {η, s / L_f}` with `L_f > 0`, then
`α L_f = max {η L_f, s}`. -/
lemma mfista_alpha_mul_lf_eq_max_stepsize
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

/-- Helper for Theorem 10.40: the admissible constant/B3 stepsize rule always yields the uniform
bound `L_k ≤ α L_f`. -/
lemma mfista_stepsize_control
    (hrule : hproblem.SublinearRateStepsizeRule y L α) (k : ℕ) :
    (L k : ℝ) ≤ α * (Lf : ℝ) := by
  rcases hrule with ⟨rfl, hconst⟩ | ⟨hLf, s, η, hα, hB3⟩
  · -- In the constant branch, `α = 1` and all curvatures equal `L_f`.
    simpa [hconst k]
  · have hmax :
        max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) = α * (Lf : ℝ) := by
      exact mfista_alpha_mul_lf_eq_max_stepsize (Lf := Lf) hLf hα
    induction k with
    | zero =>
        -- The initial accepted curvature is controlled by the first local B3 comparison.
        have hlocal := mfista_b3_local_stepsize_bounds (Lf := Lf) (hB3 := hB3) 0
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
            mfista_b3_local_stepsize_bounds (Lf := Lf) (hB3 := hB3) (k + 1)
          simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using hlocal.2
        have hmax_le : max ((η : ℝ) * (Lf : ℝ)) (L k : ℝ) ≤ α * (Lf : ℝ) := by
          exact max_le hη_le ih
        exact le_trans hstep hmax_le

/-- Helper for Theorem 10.40: every admissible MFISTA stepsize is at least the previous accepted
curvature estimate. -/
lemma mfista_stepsize_mono
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
          (mfista_b3_local_stepsize_bounds (Lf := Lf) (hB3 := hB3) (n + 1)).1

/-- Helper for Theorem 10.40: scaling the stored MFISTA extrapolation formula exposes the exact
correction term that separates the owner-level recurrence from the textbook residual identity. -/
lemma mfista_scaled_extrapolation_residual
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (xStar : E) {k : ℕ} (hk : 1 ≤ k) :
    (t k : ℝ) • y k - (xStar + (t k - 1) • x k) =
      (t (k - 1) : ℝ) • z (k - 1) - (xStar + (t (k - 1) - 1) • x (k - 1)) +
        (mfista_previous_momentum t (k - 1) - t (k - 1)) • (x k - x (k - 1)) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have htk_pos : 0 < t k := mfista_momentum_pos htraj k
  have hcancel_prev :
      (t k : ℝ) * (t (k - 1) / t k) = t (k - 1) := by
    field_simp [htk_pos.ne']
  have hcancel_momentum :
      (t k : ℝ) * ((mfista_previous_momentum t (k - 1) - 1) / t k) =
        mfista_previous_momentum t (k - 1) - 1 := by
    field_simp [htk_pos.ne']
  -- Expand the stored MFISTA extrapolation once and cancel the denominator `t_k`.
  rw [mfista_extrapolation_step htraj k hk]
  simp_rw [smul_add, smul_sub, smul_smul]
  rw [hcancel_prev, hcancel_momentum]
  -- The remaining affine terms collect into the previous residual plus the explicit correction.
  simp only [sub_eq_add_neg, add_assoc]
  module

/-- Helper for Theorem 10.40: in the stay branch of the MFISTA choice rule, the pre-step vector is
exactly the source post-step residual `u^k`. -/
lemma mfista_prestep_vector_eq_residual_of_stay
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (xStar : E) {k : ℕ} (hk : 1 ≤ k)
    (hstay : x k = x (k - 1)) :
    (t k : ℝ) • y k - (xStar + (t k - 1) • x k) =
      mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar k := by
  cases k with
  | zero =>
      cases hk
  | succ n =>
      -- In the stay branch, the correction term from the owner-level MFISTA recurrence vanishes.
      have hscaled :=
        mfista_scaled_extrapolation_residual
          (htraj := htraj) (xStar := xStar) (k := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      simpa [mfista_residual_to_optimum, hstay, sub_self] using hscaled

/-- Helper for Theorem 10.40: at the first moving step `k = 1`, the MFISTA pre-step vector
reduces to the initial residual `x^0 - xStar`. -/
lemma mfista_prestep_vector_eq_initial_residual_of_move_one
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (xStar : E) (hmove : x 1 = z 0) :
    (t 1 : ℝ) • y 1 - (xStar + (t 1 - 1) • x 1) = x 0 - xStar := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have ht0 : t 0 = 1 := by
    simpa using is_mfista_trajectory_t_zero htraj
  have hscaled :=
    mfista_scaled_extrapolation_residual
      (htraj := htraj) (xStar := xStar) (k := 1) (by simpa)
  -- At `k = 1`, the boundary convention `t_(-1) = 0` collapses the correction to `-(x¹ - x⁰)`.
  simpa [hmove, ht0, mfista_previous_momentum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hscaled

/-- Helper for Theorem 10.40: the MFISTA momentum update strictly increases the stored momentum
parameter at every step. -/
lemma mfista_momentum_strict_step
    (htraj : hproblem.IsMfistaTrajectory x y z t L) (k : ℕ) :
    t k < t (k + 1) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  -- The owner recurrence advances the momentum by at least `1 / 2`, so in particular it is
  -- strictly increasing.
  rw [is_mfista_trajectory_t_succ htraj]
  have hstep : t k + 1 / 2 ≤ fista_momentum_update (t k) :=
    add_one_half_le_fista_momentum_update (t k)
  linarith

/-- Helper for Theorem 10.40: in the move branch with `k ≥ 2`, the source interpolation weight
`(t_(k-2) - 1) / (t_(k-1) - 1)` is a genuine convex coefficient. -/
lemma mfista_move_branch_weight_mem_Icc
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    {k : ℕ} (hk : 2 ≤ k) :
    let lamk : ℝ := (t (k - 2) - 1) / (t (k - 1) - 1)
    lamk ∈ Set.Icc (0 : ℝ) 1 := by
  rcases Nat.exists_eq_add_of_le hk with ⟨n, rfl⟩
  suffices
      let lamk : ℝ := (t n - 1) / (t (n + 1) - 1)
      lamk ∈ Set.Icc (0 : ℝ) 1 by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  dsimp
  have hn_nonneg : (0 : ℝ) ≤ n := by
    exact_mod_cast (Nat.zero_le n)
  have ht_num : 1 ≤ t n := by
    have hshift : (((n : ℕ) : ℝ) + 2) / 2 = (n : ℝ) / 2 + 1 := by
      ring
    have hone : (1 : ℝ) ≤ (((n : ℕ) : ℝ) + 2) / 2 := by
      rw [hshift]
      nlinarith
    have hbound := hproblem.isMfistaTrajectory_t_lower_bound htraj n
    linarith
  have ht_den : 1 < t (n + 1) := by
    have hshift : (((n + 1 : ℕ) : ℝ) + 2) / 2 = (n : ℝ) / 2 + (3 : ℝ) / 2 := by
      calc
        (((n + 1 : ℕ) : ℝ) + 2) / 2 = (((n : ℝ) + 1) + 2) / 2 := by norm_num
        _ = (n : ℝ) / 2 + (3 : ℝ) / 2 := by ring
    have hthree_halves : (3 : ℝ) / 2 ≤ (((n + 1 : ℕ) : ℝ) + 2) / 2 := by
      rw [hshift]
      nlinarith
    have hbound := hproblem.isMfistaTrajectory_t_lower_bound htraj (n + 1)
    linarith
  have hden_pos : 0 < t (n + 1) - 1 := by
    linarith
  have hnum_nonneg : 0 ≤ t n - 1 := by
    linarith
  have hnum_le_den : t n - 1 ≤ t (n + 1) - 1 := by
    have hmono := mfista_momentum_strict_step (htraj := htraj) n
    linarith
  refine ⟨div_nonneg hnum_nonneg hden_pos.le, ?_⟩
  exact (div_le_iff₀ hden_pos).2 (by simpa using hnum_le_den)

/-- Helper for Theorem 10.40: in a move branch, the source residual is the current distance to
`xStar` plus the previous-step displacement scaled by `t_(k-1) - 1`. -/
lemma mfista_residual_to_optimum_eq_move_branch
    (xStar : E) {k : ℕ} (hk : 1 ≤ k) (hmove : x k = z (k - 1)) :
    mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar k =
      (x k - xStar) + (t (k - 1) - 1) • (x k - x (k - 1)) := by
  cases k with
  | zero =>
      cases hk
  | succ n =>
      -- Rewrite the residual at the move step and collect the affine terms into the displacement
      -- form used by the source proof.
      simp [mfista_residual_to_optimum, hmove, sub_eq_add_neg]
      module

/-- Helper for Theorem 10.40: for `k ≥ 2`, the MFISTA pre-step vector in the move branch is the
convex interpolation of the current source residual and the plain distance to `xStar` predicted by
the textbook proof. -/
lemma mfista_prestep_vector_move_branch_affine_form
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (xStar : E) {k : ℕ} (hk : 2 ≤ k) (hmove : x k = z (k - 1)) :
    let lamk : ℝ := (t (k - 2) - 1) / (t (k - 1) - 1)
    lamk ∈ Set.Icc (0 : ℝ) 1 ∧
      (t k : ℝ) • y k - (xStar + (t k - 1) • x k) =
        lamk • mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar k +
          (1 - lamk) • (x k - xStar) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨n, rfl⟩
  suffices
      let lamk : ℝ := (t n - 1) / (t (n + 1) - 1)
      lamk ∈ Set.Icc (0 : ℝ) 1 ∧
        (t (n + 2) : ℝ) • y (n + 2) - (xStar + (t (n + 2) - 1) • x (n + 2)) =
          lamk • mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar (n + 2) +
            (1 - lamk) • (x (n + 2) - xStar) by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  dsimp
  set lamk : ℝ := (t n - 1) / (t (n + 1) - 1)
  have hlam_mem :
      lamk ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [lamk] using
      mfista_move_branch_weight_mem_Icc (htraj := htraj) (k := n + 2) (by omega)
  have hscaled :=
    mfista_scaled_extrapolation_residual
      (htraj := htraj) (xStar := xStar) (k := n + 2) (by omega)
  have hprestep :
      (t (n + 2) : ℝ) • y (n + 2) - (xStar + (t (n + 2) - 1) • x (n + 2)) =
        mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar (n + 2) +
          (t n - t (n + 1)) • (x (n + 2) - x (n + 1)) := by
    -- Route correction: the owner recurrence contributes the explicit correction
    -- `(t_n - t_(n+1)) • (x^(n+2) - x^(n+1))`; rewriting through the move branch isolates it.
    simpa [mfista_residual_to_optimum, hmove, mfista_previous_momentum_succ, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using hscaled
  have hresidual :
      mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar (n + 2) =
        (x (n + 2) - xStar) + (t (n + 1) - 1) • (x (n + 2) - x (n + 1)) :=
    by
      have hmove' : x (n + 2) = z (n + 2 - 1) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmove
      exact
        mfista_residual_to_optimum_eq_move_branch
          (x := x) (z := z) (t := t) (xStar := xStar) (k := n + 2) (by omega) hmove'
  have hn_nonneg : (0 : ℝ) ≤ n := by
    exact_mod_cast (Nat.zero_le n)
  have hthree_halves :
      (3 : ℝ) / 2 ≤ t (n + 1) := by
    have hshift : (((n + 1 : ℕ) : ℝ) + 2) / 2 = (n : ℝ) / 2 + (3 : ℝ) / 2 := by
      calc
        (((n + 1 : ℕ) : ℝ) + 2) / 2 = (((n : ℝ) + 1) + 2) / 2 := by norm_num
        _ = (n : ℝ) / 2 + (3 : ℝ) / 2 := by ring
    have hthree_halves' : (3 : ℝ) / 2 ≤ (((n + 1 : ℕ) : ℝ) + 2) / 2 := by
      rw [hshift]
      nlinarith
    have hbound := hproblem.isMfistaTrajectory_t_lower_bound htraj (n + 1)
    linarith
  have hden_pos : 0 < t (n + 1) - 1 := by
    linarith
  have hlam_coeff :
      lamk * (t (n + 1) - 1) = t n - 1 := by
    dsimp [lamk]
    field_simp [hden_pos.ne']
  have hscaled_coeff :
      lamk • ((t (n + 1) - 1) • (x (n + 2) - x (n + 1))) =
        (t n - 1) • (x (n + 2) - x (n + 1)) := by
    simpa [smul_smul] using congrArg (fun a : ℝ ↦ a • (x (n + 2) - x (n + 1))) hlam_coeff
  refine ⟨hlam_mem, ?_⟩
  calc
    (t (n + 2) : ℝ) • y (n + 2) - (xStar + (t (n + 2) - 1) • x (n + 2)) =
        mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar (n + 2) +
          (t n - t (n + 1)) • (x (n + 2) - x (n + 1)) := hprestep
    _ = (x (n + 2) - xStar) + (t n - 1) • (x (n + 2) - x (n + 1)) := by
      rw [hresidual]
      module
    _ = lamk • mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar (n + 2) +
          (1 - lamk) • (x (n + 2) - xStar) := by
      rw [hresidual, smul_add, hscaled_coeff]
      module

/-- Helper for Theorem 10.40: every optimizer has finite `g`-value, hence belongs to
`effective_domain g`. -/
lemma mfista_optimal_point_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    mfista_objective_eq_optimal_value_of_mem_optimal_set
      (xStar := xStar) hproblem hxStar
  have hg_top : g xStar ≠ ⊤ := by
    intro hg_top
    have hFx_top : F xStar = ⊤ := by
      rw [composite_model_objective_apply, Function.toEReal, hg_top]
      simpa using (EReal.coe_add_top (f xStar))
    rw [hFx_top] at hxStar_value
    simpa using hxStar_value
  -- Finite `g`-value is exactly membership in the effective domain.
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_top)

/-- Helper for Theorem 10.40: on `effective_domain g`, the composite objective is the real sum
`f x + g(x).toReal`. -/
lemma mfista_objective_eq_real_of_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    F xPoint = ((((f xPoint + (g xPoint).toReal : ℝ))) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hgx_val :
      g xPoint = ((((g xPoint).toReal : ℝ)) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne (hg_proper.ne_bot xPoint)).symm
  -- Once `g x` is finite, the objective is just the sum of two real casts.
  rw [composite_model_objective_apply, Function.toEReal, hgx_val]
  simp

/-- Helper for Theorem 10.40: every positive-index MFISTA iterate has finite objective value, so
it lies in `effective_domain g`. -/
lemma mfista_iterate_mem_effective_domain
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    {k : ℕ} (hk : 1 ≤ k) :
    x k ∈ effective_domain g := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  cases k with
  | zero =>
      cases hk
  | succ n =>
      have hz_eff : z n ∈ effective_domain g := by
        -- The auxiliary point `z^n` is always the prox-gradient step, hence it has finite
        -- regularizer value.
        rw [is_mfista_trajectory_z_eq htraj n]
        simpa using
          (prox_grad_step_mem_effective_domain_g
            (f := f.toEReal) (g := g)
            (y := interior_effective_domain_point_of_real f (y n))
            (L n))
      have hz_obj :
          F (z n) = ((((f (z n) + (g (z n)).toReal : ℝ))) : EReal) :=
        mfista_objective_eq_real_of_mem_effective_domain
          (xPoint := z n) hproblem hz_eff
      have hxnext_le :
          F (x (n + 1)) ≤ F (z n) := by
        -- The MFISTA choice rule bounds the chosen iterate by each candidate, in particular by
        -- `z^n`.
        exact le_trans (is_mfista_trajectory_objective_le_min htraj n) (min_le_left _ _)
      have hxnext_top : F (x (n + 1)) ≠ ⊤ := by
        intro htop
        have htop_le : (⊤ : EReal) ≤ F (z n) := by
          simpa [htop] using hxnext_le
        have hFz_ne_top : F (z n) ≠ ⊤ := by
          rw [hz_obj]
          exact EReal.coe_ne_top _
        exact hFz_ne_top (top_le_iff.mp htop_le)
      have hg_top : g (x (n + 1)) ≠ ⊤ := by
        intro hg_top
        have hFx_top : F (x (n + 1)) = ⊤ := by
          rw [composite_model_objective_apply, Function.toEReal, hg_top]
          simpa using (EReal.coe_add_top (f (x (n + 1))))
        exact hxnext_top hFx_top
      -- Returning to `effective_domain g` only needs the exclusion of the `⊤` branch.
      exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_top)

/-- Helper for Theorem 10.40: the optimal value is a lower bound for every MFISTA objective
value, which is the order-theoretic form of nonnegativity of the objective gap. -/
lemma mfista_objective_gap_nonneg
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (n : ℕ) :
    (FOpt : EReal) ≤ F (x n) := by
  -- This is exactly the greatest-lower-bound clause from the standing fast problem.
  exact hproblem.optimal_value_isGLB.1 ⟨x n, rfl⟩

/-- Helper for Theorem 10.40: every positive-index MFISTA objective gap is finite, so its real
value casts back to the displayed `EReal` gap `F(x^n) - F_opt`. -/
lemma mfista_positive_iterate_gap_coe
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    {n : ℕ} (hn : 1 ≤ n) :
    ((((F (x n)).toReal - FOpt : ℝ)) : EReal) = F (x n) - (FOpt : EReal) := by
  have hxn_eff : x n ∈ effective_domain g :=
    mfista_iterate_mem_effective_domain
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
      (x := x) (y := y) (z := z) (t := t) (L := L) htraj hn
  have hxn_obj :
      F (x n) = ((((f (x n) + (g (x n)).toReal : ℝ))) : EReal) :=
    mfista_objective_eq_real_of_mem_effective_domain
      (xPoint := x n) hproblem hxn_eff
  -- Rewrite the iterate value through its finite real representative, then simplify the
  -- `EReal` subtraction as an ordinary real subtraction.
  rw [hxn_obj]
  rw [EReal.toReal_coe]
  simp [EReal.coe_sub]

/-- Helper for Theorem 10.40: every positive-index MFISTA objective gap is nonnegative as a real
number, once the finite-value transport from `EReal` has been isolated. -/
lemma mfista_positive_iterate_gap_nonneg
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (F (x n)).toReal - FOpt := by
  have hgapE :
      (0 : EReal) ≤ F (x n) - (FOpt : EReal) := by
    -- Convert the global lower bound `F_opt ≤ F(x^n)` into nonnegativity of the shifted gap.
    exact (EReal.sub_nonneg (Or.inr (by simp)) (Or.inr (by simp))).2 <|
      mfista_objective_gap_nonneg
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
        (Lf := Lf) (x := x) hproblem n
  have hgapE' :
      (0 : EReal) ≤ ((((F (x n)).toReal - FOpt : ℝ)) : EReal) := by
    rw [mfista_positive_iterate_gap_coe
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x := x) (y := y) (z := z) (t := t) (L := L)
      htraj (n := n) hn]
    exact hgapE
  -- Strip the final `EReal` cast to recover the real nonnegativity statement.
  exact EReal.coe_nonneg.mp hgapE'

/-- Helper for Theorem 10.40: every reciprocal MFISTA momentum coefficient `1 / t_k` is a
genuine convex-combination weight. -/
lemma mfista_one_div_t_mem_Icc
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (k : ℕ) :
    ((t k)⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have ht_ge_one : (1 : ℝ) ≤ t k := by
    have hbound := hproblem.isMfistaTrajectory_t_lower_bound htraj k
    have haux : (1 : ℝ) ≤ (((k : ℕ) : ℝ) + 2) / 2 := by
      have hk_nonneg : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le k
      nlinarith
    exact le_trans haux hbound
  have ht_pos : 0 < t k := lt_of_lt_of_le zero_lt_one ht_ge_one
  refine ⟨inv_nonneg.mpr (le_of_lt ht_pos), ?_⟩
  have hrecip : 1 / t k ≤ 1 / (1 : ℝ) :=
    one_div_le_one_div_of_le zero_lt_one ht_ge_one
  simpa [one_div] using hrecip

/-- Helper for Theorem 10.40: convexity of the smooth term gives the supporting-hyperplane lower
bound at any base point. -/
lemma mfista_convex_support_at_basepoint
    (hfast : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (xPoint yPoint : E) :
    f xPoint ≥ f yPoint + inner ℝ (∇ f yPoint) (xPoint - yPoint) := by
  have hconv : ConvexOn ℝ Set.univ f := hfast.f_convex
  let line : ℝ → E := AffineMap.lineMap yPoint xPoint
  let φ : ℝ → ℝ := fun s ↦ f (line s)
  have hφ_convex : ConvexOn ℝ Set.univ φ := by
    -- Restrict the global convexity of `f` to the segment from `y` to `x`.
    simpa [φ, line] using
      hconv.comp_affineMap (AffineMap.lineMap (k := ℝ) yPoint xPoint)
  have hy_diff : DifferentiableAt ℝ f yPoint := hfast.f_smooth.1 yPoint (by simp)
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

/-- Helper for Theorem 10.40: convexity of `f` makes the prox-gradient linearization defect
nonnegative at every real base point. -/
lemma mfista_linearization_defect_nonneg
    (hfast : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (xPoint yPoint : E) :
    (0 : EReal) ≤
      ℓ[f.toEReal, xPoint, interior_effective_domain_point_of_real f yPoint] := by
  let yI := interior_effective_domain_point_of_real f yPoint
  have hsupport :
      0 ≤ f xPoint - f yPoint - inner ℝ (∇ f yPoint) (xPoint - yPoint) := by
    -- Rearrange the convex supporting-hyperplane inequality into the standard defect form.
    have hbase :=
      mfista_convex_support_at_basepoint
        (hfast := hfast) (xPoint := xPoint) (yPoint := yPoint)
    linarith
  have hsupportE :
      (0 : EReal) ≤
        ((((f xPoint - f yPoint - inner ℝ (∇ f yPoint) (xPoint - yPoint) : ℝ))) : EReal) := by
    exact EReal.coe_nonneg.mpr hsupport
  -- Evaluating the linearization defect at a real base point collapses to the same real scalar.
  simpa [yI, prox_gradient_linearization_defect_eq, Function.toEReal, EReal.coe_sub] using
    hsupportE

/-- Helper for Theorem 10.40: the source comparison point
`(1 / t_k) xStar + (1 - 1 / t_k) x^k` satisfies the convex objective upper bound coming from the
convexity of `f` and `g`. -/
lemma mfista_combination_objective_upper_bound
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (hxStar : xStar ∈ XStar)
    {k : ℕ} (hk : 1 ≤ k) :
    let θ : ℝ := (t k)⁻¹
    let c : E := θ • xStar + (1 - θ) • x k
    F c ≤
      ((((1 - θ) * ((F (x k)).toReal - FOpt) + FOpt : ℝ)) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  let θ : ℝ := (t k)⁻¹
  let c : E := θ • xStar + (1 - θ) • x k
  have hxStar_eff : xStar ∈ effective_domain g :=
    mfista_optimal_point_mem_effective_domain (xStar := xStar) hproblem hxStar
  have hxk_eff : x k ∈ effective_domain g :=
    mfista_iterate_mem_effective_domain
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
      (x := x) (y := y) (z := z) (t := t) (L := L) htraj hk
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using mfista_one_div_t_mem_Icc (htraj := htraj) k
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hθ_le_one : θ ≤ 1 := hθ_mem.2
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_le_one
  have hθ_sum : θ + (1 - θ) = 1 := by ring
  have hc_eff : c ∈ effective_domain g := by
    -- Convexity of `g` keeps the source comparison point finite-valued.
    exact combo_mem_effective_domain_of_is_convex_function hproblem.g_convex
      hxStar_eff hxk_eff hθ_mem
  have hc_obj :
      F c = ((((f c + (g c).toReal : ℝ))) : EReal) :=
    mfista_objective_eq_real_of_mem_effective_domain
      (xPoint := c) hproblem hc_eff
  have hxk_obj :
      F (x k) = ((((f (x k) + (g (x k)).toReal : ℝ))) : EReal) :=
    mfista_objective_eq_real_of_mem_effective_domain
      (xPoint := x k) hproblem hxk_eff
  have hxStar_obj :
      F xStar = ((((f xStar + (g xStar).toReal : ℝ))) : EReal) :=
    mfista_objective_eq_real_of_mem_effective_domain
      (xPoint := xStar) hproblem hxStar_eff
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    mfista_objective_eq_optimal_value_of_mem_optimal_set
      (xStar := xStar) hproblem hxStar
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
      g c ≤
        (θ : EReal) * g xStar + ((1 - θ : ℝ) : EReal) * g (x k) := by
    -- This is the source Jensen inequality for the nonsmooth term.
    simpa [c, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (is_convex_function_iff_segment_ineq.mp hproblem.g_convex)
        xStar hxStar_eff (x k) hxk_eff hθ_mem
  have hg_convex :
      (g c).toReal ≤ θ * (g xStar).toReal + (1 - θ) * (g (x k)).toReal := by
    have hgxStar_val :
        g xStar = ((((g xStar).toReal : ℝ)) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxStar_eff).ne
        (hproblem.g_proper.ne_bot xStar)).symm
    have hgxk_val :
        g (x k) = ((((g (x k)).toReal : ℝ)) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxk_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hgc_val :
        g c = ((((g c).toReal : ℝ)) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hc_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hg_convex' :
        ((((g c).toReal : ℝ)) : EReal) ≤
          (((((θ * (g xStar).toReal + (1 - θ) * (g (x k)).toReal : ℝ))) : EReal)) := by
      rw [hgc_val, hgxStar_val, hgxk_val] at hg_convexE
      simpa [EReal.coe_add, EReal.coe_mul] using hg_convexE
    exact EReal.coe_le_coe_iff.mp hg_convex'
  have hf_convex :
      f c ≤ θ * f xStar + (1 - θ) * f (x k) := by
    have hseg :=
      hproblem.f_convex.2
        (show xStar ∈ Set.univ by simp)
        (show x k ∈ Set.univ by simp)
        hθ_nonneg hone_sub_nonneg hθ_sum
    -- Specialize convexity of `f` to the same source comparison point.
    simpa [c, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      hseg
  have hc_toReal :
      (F c).toReal = f c + (g c).toReal := by
    rw [hc_obj, EReal.toReal_coe]
  have hupper_real :
      (F c).toReal ≤
        (1 - θ) * ((F (x k)).toReal - FOpt) + FOpt := by
    -- Add the smooth and nonsmooth convexity bounds, then replace `F xStar` by `FOpt`.
    rw [hc_toReal, hxk_toReal]
    nlinarith [hf_convex, hg_convex, hxStar_toReal]
  -- Return to `EReal` after the real inequality has been normalized.
  simpa [θ, c, hc_obj] using (EReal.coe_le_coe_iff.mpr hupper_real)

/-- Helper for Theorem 10.40: scaling the displacement from the source comparison point clears
the reciprocal coefficient `1 / t_k` and leaves the affine vector used in the Lyapunov energy. -/
lemma mfista_scaled_sub_comparison_point
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (xStar point : E) (k : ℕ) :
    let θ : ℝ := (t k)⁻¹
    let c : E := θ • xStar + (1 - θ) • x k
    (t k : ℝ) • (point - c) = (t k : ℝ) • point - (xStar + (t k - 1) • x k) := by
  have htk_pos : 0 < t k := mfista_momentum_pos htraj k
  have hθ : (t k : ℝ) * (t k)⁻¹ = 1 := by
    exact mul_inv_cancel₀ htk_pos.ne'
  have hxcoeff : (t k : ℝ) * (1 - (t k)⁻¹) = t k - 1 := by
    -- Expand the scalar coefficient once, then cancel `t_k * t_k⁻¹`.
    calc
      (t k : ℝ) * (1 - (t k)⁻¹) = (t k : ℝ) - (t k : ℝ) * (t k)⁻¹ := by ring
      _ = t k - 1 := by rw [hθ]
  -- Expand the comparison point and collect the cleared scalar coefficients.
  dsimp
  simp_rw [smul_sub, smul_add, smul_smul]
  rw [hθ, hxcoeff]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 10.40: applying the scaled comparison-point rewrite to `z^k` recovers the
source post-step residual `u^(k+1)`. -/
lemma mfista_scaled_step_sub_comparison_point_eq_residual
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (xStar : E) (k : ℕ) :
    let θ : ℝ := (t k)⁻¹
    let c : E := θ • xStar + (1 - θ) • x k
    (t k : ℝ) • (z k - c) =
      mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar (k + 1) := by
  -- The generic comparison-point rewrite matches the residual definition exactly at `z^k`.
  simpa [mfista_residual_to_optimum] using
    (mfista_scaled_sub_comparison_point
      (htraj := htraj) (xStar := xStar) (point := z k) k)

/- Theorem 10.40 is `source-facing` in the MFISTA convergence analysis.

Domain sampling in the surrounding chapter identifies:
- `is_mfista_trajectory` from Algorithm 10.11 as the owner of the MFISTA iterate data;
- `hproblem.SublinearRateStepsizeRule y L α` from Algorithm 10.6 as the canonical owner-level
  bridge for the admissible constant/B3 stepsize regimes with the auxiliary constant `α`;
- `composite_model_objective` from Definition 10.2 as the owner of the composite value
  `F = f + g`.

Layer triage:
- `source-facing`: the accelerated objective-gap estimate for an MFISTA trajectory;
- `core/canonical`: `F`, `hproblem.IsMfistaTrajectory`, and
  `fast_proximal_gradient_sublinear_rate_stepsize_rule f g Lf`;
- `bridge/view`: `hproblem.SublinearRateStepsizeRule y L α` and the optimizer membership
  hypothesis `xStar ∈ XStar`.

Primitive data are the trajectory, the standing problem assumptions, the optimizer `xStar`, and
the single shared stepsize-rule owner. The theorem therefore uses the bridge/view surfaces
`hproblem.IsMfistaTrajectory` and
`hproblem.SublinearRateStepsizeRule y L α`, so the Assumption 10.31 owner supplies the
regularity fields canonically instead of exposing them in the theorem statement. -/

-- Proof sketch: combine the MFISTA descent recursion from the prox-gradient inequality with the
-- acceptance property `(10.39)` supplied either by the constant rule `L_k = L_f` or by
-- backtracking procedure B3, telescope the Lyapunov estimate built from `t_k` and the auxiliary
-- vectors `u^k`, bound the initial energy by `‖x^0 - x*‖²`, and then use the standard lower bound
-- on `t_(k-1)` to convert the estimate into the `O(1 / k^2)` rate.
/-- Theorem 10.40: under Assumption 10.31, any MFISTA trajectory whose curvature estimates are
chosen either by the constant rule `L_k = L_f` with `α = 1` or by backtracking procedure B3 with
`α = max {η, s / L_f}` satisfies the accelerated objective bound
`F(x^k) - F_opt ≤ 2 α L_f ‖x^0 - x*‖² / (k + 1)²` for every optimizer `x* ∈ X^*` and every
iteration `k ≥ 1`. -/
theorem mfista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq
    (htraj : hproblem.IsMfistaTrajectory x y z t L)
    (hrule : hproblem.SublinearRateStepsizeRule y L α)
    (hxStar : xStar ∈ XStar) (k : ℕ) (hk : 1 ≤ k) :
    F (x k) - (FOpt : EReal) ≤
      ((2 * α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (k + 1 : ℝ) ^ (2 : ℕ) : ℝ) :
        EReal) := by
  -- Route correction: `mfista_scaled_extrapolation_residual` shows that the owner-level MFISTA
  -- recurrence produces an extra correction term, so the textbook Lyapunov telescope does not
  -- close verbatim from the current `y_succ` field.
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    mfista_objective_eq_optimal_value_of_mem_optimal_set
      (xStar := xStar) hproblem hxStar
  have hgapk_coe :
      ((((F (x k)).toReal - FOpt : ℝ)) : EReal) = F (x k) - (FOpt : EReal) :=
    mfista_positive_iterate_gap_coe
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x := x) (y := y) (z := z) (t := t) (L := L)
      htraj hk
  have hgapk_nonneg :
      0 ≤ (F (x k)).toReal - FOpt :=
    mfista_positive_iterate_gap_nonneg
      (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) (x := x) (y := y) (z := z) (t := t) (L := L)
      htraj hk
  let v : ℕ → ℝ := fun n ↦ (F (x n)).toReal - FOpt
  let A : ℕ → ℝ := fun n ↦
    ‖mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar n‖ ^ (2 : ℕ) +
      (2 / (L (n - 1) : ℝ)) * t (n - 1) ^ (2 : ℕ) * v n
  let B : ℕ → ℝ := fun n ↦
    ‖x n - xStar‖ ^ (2 : ℕ) +
      (2 / (L (n - 1) : ℝ)) * t (n - 1) ^ (2 : ℕ) * v n
  let M : ℕ → ℝ := fun n ↦ max (A n) (B n)
  have hvk_nonneg : 0 ≤ v k := by
    simpa [v] using hgapk_nonneg
  have hcomparison_upper :
      let θ : ℝ := (t k)⁻¹
      let c : E := θ • xStar + (1 - θ) • x k
      F c ≤ ((((1 - θ) * v k + FOpt : ℝ)) : EReal) := by
    -- The source comparison point already has the correct convex objective upper bound.
    simpa [v] using
      (mfista_combination_objective_upper_bound
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
        (x := x) (y := y) (z := z) (t := t) (L := L)
        (hproblem := hproblem) (htraj := htraj) (hxStar := hxStar) hk)
  have hcomparison_step :
      let θ : ℝ := (t k)⁻¹
      let c : E := θ • xStar + (1 - θ) • x k
      (t k : ℝ) • (z k - c) =
        mfista_residual_to_optimum (x := x) (z := z) (t := t) xStar (k + 1) := by
    -- This is the post-step quadratic rewrite required by the source comparison-point estimate.
    simpa using
      (mfista_scaled_step_sub_comparison_point_eq_residual
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
        (x := x) (y := y) (z := z) (t := t) (L := L)
        (hproblem := hproblem) (htraj := htraj) (xStar := xStar) k)
  have hcomparison_prestep :
      let θ : ℝ := (t k)⁻¹
      let c : E := θ • xStar + (1 - θ) • x k
      (t k : ℝ) • (y k - c) = (t k : ℝ) • y k - (xStar + (t k - 1) • x k) := by
    -- The same comparison point also rewrites the pre-step quadratic term into the owner vector.
    simpa using
      (mfista_scaled_sub_comparison_point
        (f := f) (g := g) (XStar := XStar) (FOpt := FOpt) (Lf := Lf)
        (x := x) (y := y) (z := z) (t := t) (L := L)
        (hproblem := hproblem) (htraj := htraj) (xStar := xStar) (point := y k) k)
  -- TODO: the finite-value transport is now normalized through `v`, `hgapk_coe`, and
  -- `hgapk_nonneg`, `hcomparison_upper`, `hcomparison_step`, and `hcomparison_prestep`. The
  -- remaining source-faithful step is now exactly the prox-gradient specialization:
  -- apply `fundamental_prox_grad_inequality` at the comparison point, rewrite the two quadratic
  -- terms via `hcomparison_step` and `hcomparison_prestep`, and then package the stay/move
  -- branches into the `k ≥ 2` two-state monotonicity from the re-plan.
  clear hxStar_value hgapk_coe hvk_nonneg hcomparison_upper hcomparison_step
    hcomparison_prestep M B A v
  sorry

end
