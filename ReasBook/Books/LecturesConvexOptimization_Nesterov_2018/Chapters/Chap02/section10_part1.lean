import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_10 (from Chap02) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 2.10 lies in the Euclidean quadratic hard-instance domain.

Sampled owner-style declarations in this domain:
* `smoothLowerBoundFunction` in `Definition_2_11`
* `quadraticObjective` in `Definition_1_9_1`
* `EuclideanSpace.equiv` in mathlib for the canonical coordinate model of `EuclideanSpace`
* the project's private `prefixPoint` pattern in `Algorithm_3_1` and `Proposition_3_28`, where
  prefix restriction is kept internal via `WithLp.toLp`

Best owner abstraction:
* `smoothLowerBoundFunction`

Primitive data:
* the hard-instance parameters `L` and `k`

Derived API:
* the ambient hard instance `quadraticHardInstanceFamily`

Source/core/bridge triage:
* source-facing: `quadraticHardInstanceFamily L k`
* core/canonical: `smoothLowerBoundFunction L (Nat.succPNat k.1)`
* bridge/view: the internal restriction from `ℝⁿ` to the first `k.1 + 1` coordinates
-/

private def hardInstancePrefix (k : Fin n) (x : E) :
    EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  (EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm
    (fun i ↦ x (Fin.castLE (Nat.succ_le_of_lt k.2) i))

/-- Definition 2.10: for fixed `L` and `k : Fin n`, the textbook hard instance with one-based
index `k.1 + 1 ∈ {1, ..., n}` is the quadratic objective on `ℝⁿ` obtained by applying
`smoothLowerBoundFunction L (Nat.succPNat k.1)` to the first `k.1 + 1` zero-based
coordinates. -/
def quadraticHardInstanceFamily (L : ℝ) (k : Fin n) : E → ℝ :=
  fun x ↦ smoothLowerBoundFunction L (Nat.succPNat k.1) (hardInstancePrefix k x)

/-! ### Lemma_2_10 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace OptimalMethodRecurrence

variable {f : E → ℝ} {L μ gamma0 : ℝ} {x0 : E}

open Real
open scoped StrongConvexSmooth

local notation "qf" => q[μ, L]

/-
Primary domain: scalar weight recurrences attached to the chapter's optimal-method estimating
sequences.

Owner declarations sampled before refining this file:
* `OptimalMethodRecurrence` in `Algorithm_2_2`, which owns the trajectory data and the scalar
  recurrences `αₖ`, `γₖ`;
* `OptimalMethodRecurrence.weight`, `OptimalMethodRecurrence.weight_pos`, and
  `OptimalMethodRecurrence.gamma_sub_mu_eq_weight_mul_initial_gap` in `Algorithm_2_2`, which own
  the canonical estimating-sequence weight `λₖ` and its basic scalar recurrence API;
* `OptimalMethodRecurrence.gamma_succ_eq_L_mul_sq` in `Algorithm_2_2`, which converts the owner
  curvature update into the scalar quadratic identity used in this lemma;
* `optimal_method_alpha0_initial_curvature` in `Algorithm_2_4`, which is only a downstream
  bridge `α₀ ↦ γ₀`, not a second owner for the same weight sequence.

Layer triage:
* `source-facing`: the textbook upper bounds on the owner weight sequence and the `γ₀ = μ`
  closed form;
* `core/canonical`: `OptimalMethodRecurrence` together with `weight`;
* `bridge/view`: later reparametrizations of `γ₀` in terms of `α₀`.

Primitive data:
* the owner recurrence `method`;
* the positivity / interval hypotheses on `μ` and `γ₀` when they change the mathematics.

Derived API:
* the hyperbolic and quadratic upper bounds for `method.weight k`;
* the geometric closed form when `γ₀ = μ`.

The redundant public inequality `μ ≤ L` is not kept below: in the interval case it follows from
the owner recurrence together with `γ₀ ∈ (μ, 3L + μ]`, and in the `γ₀ = μ` case the owner
recurrence already forces the required range conditions.
-/

/-- Helper for Lemma 2.10: when `γ₀ ∈ (μ, 3L + μ]`, the owner recurrence forces `μ < L`. -/
lemma mu_lt_L_of_interval_init
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ)) :
    μ < L := by
  have halpha0 : method.alpha 0 ∈ Set.Ioo (0 : ℝ) 1 := method.alpha_mem_Ioo 0
  have hgamma1_gt : μ < method.gamma 1 := by
    -- The owner curvature-gap identity stays positive at `k = 1`.
    have hgap1 := gamma_sub_mu_eq_weight_mul_initial_gap method 1
    have hpos : 0 < method.weight 1 * (gamma0 - μ) := by
      exact mul_pos (weight_pos method 1) (sub_pos.mpr hgamma0.1)
    linarith
  have hgamma1_lt : method.gamma 1 < L := by
    -- The quadratic identity rewrites `γ₁` as `L α₀²`, and `α₀ ∈ (0, 1)` makes this `< L`.
    rw [method.gamma_succ_eq_L_mul_sq 0]
    have hsq_lt : method.alpha 0 ^ (2 : ℕ) < 1 := by
      nlinarith [halpha0.1, halpha0.2]
    nlinarith [method.L_pos, hsq_lt]
  linarith

/-- Helper for Lemma 2.10: the interval hypothesis implies `q[μ, L] ∈ (0, 1)`. -/
lemma qf_mem_Ioo_of_interval_init
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hμ : 0 < μ)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ)) :
    q[μ, L] ∈ Set.Ioo (0 : ℝ) 1 := by
  have hμL : μ < L := mu_lt_L_of_interval_init method hgamma0
  exact ⟨div_pos hμ method.L_pos, (div_lt_one method.L_pos).2 hμL⟩

/-- Helper for Lemma 2.10: `1 - sqrt (1 - a)` always dominates `a / 2` on `[0, 1]`. -/
lemma half_le_one_sub_sqrt_sub
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a / 2 ≤ 1 - Real.sqrt (1 - a) := by
  -- Squaring the auxiliary square root reduces the claim to a quadratic identity.
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - a) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (1 - a)) ^ (2 : ℕ) = 1 - a := by
    rw [Real.sq_sqrt]
    linarith
  nlinarith

/-- Helper for Lemma 2.10: the rescaled inverse-square-root weight satisfies the one-step
lower bound coming from the owner scalar recurrence. -/
lemma weight_xi_step_lower_bound
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hγ0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (j : ℕ) :
    let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((gamma0 - μ) * method.weight m))
    ξ (j + 1) - ξ j ≥
      (1 / 2 : ℝ) * Real.sqrt (1 + q[μ, L] * ξ (j + 1) ^ (2 : ℕ)) := by
  dsimp
  have hgap : 0 < gamma0 - μ := by
    linarith [hγ0.1]
  have hα0 : 0 ≤ method.alpha j := (method.alpha_mem_Ioo j).1.le
  have hα1 : method.alpha j < 1 := (method.alpha_mem_Ioo j).2
  have hwj : 0 < method.weight j := weight_pos method j
  have hwj1 : 0 < method.weight (j + 1) := weight_pos method (j + 1)
  have hξj :
      Real.sqrt (L / ((gamma0 - μ) * method.weight j)) =
        Real.sqrt (1 - method.alpha j) *
          Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
    -- Rewrite `ξ_j` using the exact weight recurrence `λ_{j+1} = (1 - α_j) λ_j`.
    have hrew :
        L / ((gamma0 - μ) * method.weight j) =
          (1 - method.alpha j) * (L / ((gamma0 - μ) * method.weight (j + 1))) := by
      rw [method.weight_succ]
      field_simp [hgap.ne', hwj.ne', sub_ne_zero.mpr hα1.ne']
    rw [hrew, Real.sqrt_mul (sub_nonneg.mpr hα1.le)]
  have hroot :
      Real.sqrt
          (1 + qf *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ)) =
        method.alpha j *
          Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
    -- The quadratic owner identity rewrites the square root exactly as `α_j ξ_{j+1}`.
    have hξsq :
        Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ) =
          L / ((gamma0 - μ) * method.weight (j + 1)) := by
      rw [Real.sq_sqrt]
      apply div_nonneg
      · exact method.L_pos.le
      · positivity
    have hgapw :
        (gamma0 - μ) * method.weight (j + 1) = method.gamma (j + 1) - μ := by
      simpa [mul_comm] using
        (gamma_sub_mu_eq_weight_mul_initial_gap method (j + 1)).symm
    have hsq :
        1 + qf *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ) =
          method.alpha j ^ (2 : ℕ) *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ) := by
      rw [hξsq]
      rw [method.gamma_succ_eq_L_mul_sq j] at hgapw
      field_simp [method.L_pos.ne', hgap.ne', hwj1.ne'] at hgapw ⊢
      nlinarith
    have hnonneg :
        0 ≤
          method.alpha j *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
      positivity
    rw [hsq, ← mul_pow]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
  calc
    Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) -
        Real.sqrt (L / ((gamma0 - μ) * method.weight j))
        =
      (1 - Real.sqrt (1 - method.alpha j)) *
        Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
          rw [hξj]
          ring
    _ ≥ (method.alpha j / 2) *
        Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) := by
          -- The scalar inequality `1 - sqrt (1 - α_j) ≥ α_j / 2` finishes the discrete step.
          gcongr
          exact half_le_one_sub_sqrt_sub hα0 hα1.le
    _ = (1 / 2 : ℝ) *
        Real.sqrt
          (1 + qf *
            Real.sqrt (L / ((gamma0 - μ) * method.weight (j + 1))) ^ (2 : ℕ)) := by
          rw [hroot]
          ring

/-- Helper for Lemma 2.10: a one-step lower bound of the form
`b - a ≥ δ * sqrt (1 + b^2)` implies an additive `arsinh` increment. -/
lemma arsinh_sub_ge_of_sub_ge_mul_sqrt
    {a b δ : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hδ : 0 ≤ δ)
    (hstep : b - a ≥ δ * Real.sqrt (1 + b ^ (2 : ℕ))) :
    δ ≤ Real.arsinh b - Real.arsinh a := by
  by_cases hab_eq : a = b
  · -- In the degenerate case, the step inequality already forces `δ = 0`.
    subst hab_eq
    have hδ_zero : δ = 0 := by
      have hsqrt_pos : 0 < Real.sqrt (1 + a ^ (2 : ℕ)) := by positivity
      nlinarith
    simp [hδ_zero]
  · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
    rcases exists_deriv_eq_slope Real.arsinh hab_lt Real.continuous_arsinh.continuousOn
        (fun x hx ↦ (Real.hasDerivAt_arsinh x).differentiableAt.differentiableWithinAt) with
      ⟨c, hc, hcderiv⟩
    have hc_nonneg : 0 ≤ c := le_trans ha hc.1.le
    have hsqrt_le :
        Real.sqrt (1 + c ^ (2 : ℕ)) ≤ Real.sqrt (1 + b ^ (2 : ℕ)) := by
      gcongr
      nlinarith [hc_nonneg, hc.2.le]
    have hderiv_lb :
        (Real.sqrt (1 + b ^ (2 : ℕ)))⁻¹ ≤ deriv Real.arsinh c := by
      -- The derivative of `arsinh` decreases on `[0, ∞)`, so the slope is bounded below by
      -- its right-endpoint value.
      have h_inv :
          (Real.sqrt (1 + b ^ (2 : ℕ)))⁻¹ ≤
            (Real.sqrt (1 + c ^ (2 : ℕ)))⁻¹ := by
        simpa [one_div] using
          (one_div_le_one_div_of_le (by positivity) hsqrt_le)
      simpa using h_inv.trans_eq (by simpa using (Real.hasDerivAt_arsinh c).deriv.symm)
    have hsqrt_pos : 0 < Real.sqrt (1 + b ^ (2 : ℕ)) := by positivity
    have hδ_le_div : δ ≤ (b - a) / Real.sqrt (1 + b ^ (2 : ℕ)) := by
      rw [le_div_iff₀ hsqrt_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hstep
    have hmul_le :
        (b - a) / Real.sqrt (1 + b ^ (2 : ℕ)) ≤
          (b - a) * deriv Real.arsinh c := by
      have hba_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hderiv_lb hba_nonneg
    have hslope_eq :
        Real.arsinh b - Real.arsinh a = (b - a) * deriv Real.arsinh c := by
      -- Lagrange's theorem turns the difference of `arsinh` values into an exact slope.
      have hmul := congrArg (fun t ↦ t * (b - a)) hcderiv
      have hne : b - a ≠ 0 := sub_ne_zero.mpr hab_lt.ne'
      field_simp [hne] at hmul
      linarith
    exact (hδ_le_div.trans hmul_le).trans_eq hslope_eq.symm

/-- Helper for Lemma 2.10: the interval constraint on `γ₀` gives the base lower bound for the
rescaled inverse-square-root weight `ξ₀`. -/
lemma initial_weight_xi_lower_bound
    (hγ0 : gamma0 ∈ Set.Ioc μ (3 * L + μ)) :
    1 / Real.sqrt 3 ≤ Real.sqrt (L / (gamma0 - μ)) := by
  -- Rewriting `γ₀ - μ ≤ 3L` as a reciprocal estimate gives the textbook base bound on `ξ₀`.
  have hgap_pos : 0 < gamma0 - μ := by
    linarith [hγ0.1]
  have hdiv_le : (1 : ℝ) / 3 ≤ L / (gamma0 - μ) := by
    have hgap_le : gamma0 - μ ≤ 3 * L := by
      linarith [hγ0.2]
    field_simp [hgap_pos.ne', (show (3 : ℝ) ≠ 0 by norm_num)]
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hdiv_le
  have hleft : Real.sqrt ((1 : ℝ) / 3) = 1 / Real.sqrt 3 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (3 : ℝ), Real.sqrt_one]
  simpa [hleft] using hsqrt

/-- Helper for Lemma 2.10: on `[0, 1]`, the scalar map `s ↦ arsinh (s / √3)` dominates `s / 2`.
-/
lemma half_le_arsinh_div_sqrt_three
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s / 2 ≤ Real.arsinh (s / Real.sqrt 3) := by
  let h : ℝ → ℝ := fun t ↦ Real.arsinh (t / Real.sqrt 3) - t / 2
  have hcont : ContinuousOn h (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    have harsinh :
        ContinuousAt (fun t : ℝ ↦ Real.arsinh (t / Real.sqrt 3)) x :=
      continuous_arsinh.continuousAt.comp
        (continuousAt_id.div_const (Real.sqrt 3))
    exact (harsinh.sub (continuousAt_id.div_const 2)).continuousWithinAt
  have hderiv :
      ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
        HasDerivWithinAt h
          ((((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3) - 1 / 2)
          (interior (Set.Icc (0 : ℝ) 1)) x := by
    intro x hx
    have harsinh :
        HasDerivAt (fun t : ℝ ↦ Real.arsinh (t / Real.sqrt 3))
          (((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3) x := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (Real.hasDerivAt_arsinh (x / Real.sqrt 3)).comp x
          ((hasDerivAt_id x).div_const (Real.sqrt 3))
    simpa [h] using
      harsinh.hasDerivWithinAt.sub ((hasDerivAt_id x).div_const 2).hasDerivWithinAt
  have hderiv_nonneg :
      ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
        0 ≤ (((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3) - 1 / 2 := by
    intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hsqrt3_ne : Real.sqrt 3 ≠ 0 := hsqrt3_pos.ne'
    have hx_sq_le : x ^ (2 : ℕ) ≤ 1 := by
      nlinarith [hx.1.le, hx.2.le]
    have hsq_eq : (x / Real.sqrt 3) ^ (2 : ℕ) = x ^ (2 : ℕ) / 3 := by
      field_simp [pow_two, hsqrt3_ne]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have hinside_le : 1 + (x / Real.sqrt 3) ^ (2 : ℕ) ≤ 4 / 3 := by
      rw [hsq_eq]
      nlinarith
    have hsqrt_le : Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)) ≤ 2 / Real.sqrt 3 := by
      refine (Real.sqrt_le_sqrt hinside_le).trans_eq ?_
      have hfour : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
        rw [Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
      have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
      calc
        Real.sqrt (4 / 3 : ℝ) = Real.sqrt 4 / Real.sqrt 3 := by
          rw [Real.sqrt_div h4_nonneg (3 : ℝ)]
        _ = 2 / Real.sqrt 3 := by simp [hfour]
    have hInv :
        (1 / (2 / Real.sqrt 3 : ℝ)) ≤
          1 / Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)) :=
      one_div_le_one_div_of_le (by positivity) hsqrt_le
    have hmul := mul_le_mul_of_nonneg_right hInv
      (by positivity : 0 ≤ (1 / Real.sqrt 3 : ℝ))
    have hhalf : (1 / 2 : ℝ) = (1 / (2 / Real.sqrt 3 : ℝ)) * (1 / Real.sqrt 3) := by
      have hrewrite : (1 / 2 : ℝ) = (Real.sqrt 3 / 2) * (1 / Real.sqrt 3) := by
        field_simp [hsqrt3_ne]
      simpa [one_div_div] using hrewrite
    have hderiv_ge_half :
        (1 / 2 : ℝ) ≤ ((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3 := by
      calc
        (1 / 2 : ℝ) = (1 / (2 / Real.sqrt 3 : ℝ)) * (1 / Real.sqrt 3) := hhalf
        _ ≤ (1 / Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ))) * (1 / Real.sqrt 3) := hmul
        _ = ((Real.sqrt (1 + (x / Real.sqrt 3) ^ (2 : ℕ)))⁻¹) / Real.sqrt 3 := by
            ring_nf
    linarith
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    hcont hderiv hderiv_nonneg
  have hzero : h 0 = 0 := by
    simp [h]
  have hstep : h 0 ≤ h s := hmono (by simp) ⟨hs0, hs1⟩ hs0
  -- Evaluating the monotone auxiliary function at `0` and `s` gives the desired bound.
  simpa [h, hzero] using hstep

/-- Helper for Lemma 2.10: the interval initialization already satisfies the base `arsinh`
barrier used in the discrete induction. -/
lemma initial_arsinh_barrier
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hμ : 0 < μ)
    (hγ0 : gamma0 ∈ Set.Ioc μ (3 * L + μ)) :
    Real.sqrt q[μ, L] / 2 ≤
      Real.arsinh (Real.sqrt q[μ, L] * Real.sqrt (L / (gamma0 - μ))) := by
  -- Combine the scalar interval estimate `ξ₀ ≥ 1 / √3` with the monotone `arsinh` bridge.
  have hqf : qf ∈ Set.Ioo (0 : ℝ) 1 := qf_mem_Ioo_of_interval_init method hμ hγ0
  have hs0 : 0 ≤ Real.sqrt qf := Real.sqrt_nonneg qf
  have hs1 : Real.sqrt qf ≤ 1 := by
    simpa using (Real.sqrt_le_one.2 hqf.2.le)
  have hbase :
      Real.sqrt qf / 2 ≤ Real.arsinh (Real.sqrt qf / Real.sqrt 3) :=
    half_le_arsinh_div_sqrt_three hs0 hs1
  have hxi0 :
      Real.sqrt qf / Real.sqrt 3 ≤
        Real.sqrt qf * Real.sqrt (L / (gamma0 - μ)) := by
    have hξ := initial_weight_xi_lower_bound hγ0
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hξ hs0
  exact hbase.trans ((Real.arsinh_le_arsinh).2 hxi0)

/-- Helper for Lemma 2.10: the discrete `arsinh` barrier accumulated along the `ξ` recurrence. -/
lemma weight_xi_arsinh_lower_bound
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hμ : 0 < μ)
    (hγ0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((gamma0 - μ) * method.weight m))
    (((k + 1 : ℝ) * Real.sqrt q[μ, L]) / 2) ≤
      Real.arsinh (Real.sqrt q[μ, L] * ξ k) := by
  let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((gamma0 - μ) * method.weight m))
  have hqf : qf ∈ Set.Ioo (0 : ℝ) 1 := qf_mem_Ioo_of_interval_init method hμ hγ0
  induction k with
  | zero =>
      -- The new standalone base barrier matches the `k = 0` case after `weight_zero`.
      simpa [ξ] using initial_arsinh_barrier method hμ hγ0
  | succ k ih =>
      -- The step recurrence for `ξ` yields an additive `arsinh` increment after rescaling by `√qf`.
      have ih' :
          (((k + 1 : ℝ) * Real.sqrt qf) / 2) ≤
            Real.arsinh (Real.sqrt qf * ξ k) := by
        simpa [ξ] using ih
      have hstep :
          ξ (k + 1) - ξ k ≥
            (1 / 2 : ℝ) * Real.sqrt (1 + qf * ξ (k + 1) ^ (2 : ℕ)) := by
        simpa [ξ] using weight_xi_step_lower_bound method hγ0 k
      have hξ_nonneg : 0 ≤ ξ k := by
        dsimp [ξ]
        positivity
      have hscaled_step :
          Real.sqrt qf * ξ (k + 1) - Real.sqrt qf * ξ k ≥
            (Real.sqrt qf / 2) *
              Real.sqrt (1 + qf * ξ (k + 1) ^ (2 : ℕ)) := by
        have hmul := mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg qf)
        nlinarith
      have hscaled_step' :
          Real.sqrt qf * ξ (k + 1) - Real.sqrt qf * ξ k ≥
            (Real.sqrt qf / 2) *
              Real.sqrt (1 + (Real.sqrt qf * ξ (k + 1)) ^ (2 : ℕ)) := by
        have hsq_rewrite :
            qf * ξ (k + 1) ^ (2 : ℕ) = (Real.sqrt qf * ξ (k + 1)) ^ (2 : ℕ) := by
          nlinarith [Real.sq_sqrt hqf.1.le]
        simpa [hsq_rewrite] using hscaled_step
      have hξ_mono :
          Real.sqrt qf * ξ k ≤ Real.sqrt qf * ξ (k + 1) := by
        have hstep_nonneg :
            0 ≤
              (Real.sqrt qf / 2) *
                Real.sqrt (1 + (Real.sqrt qf * ξ (k + 1)) ^ (2 : ℕ)) := by
          positivity
        nlinarith [hscaled_step', hstep_nonneg]
      have hscaled_nonneg : 0 ≤ Real.sqrt qf * ξ k := by
        positivity
      have harsinh_step :
          Real.sqrt qf / 2 ≤
            Real.arsinh (Real.sqrt qf * ξ (k + 1)) -
              Real.arsinh (Real.sqrt qf * ξ k) := by
        exact arsinh_sub_ge_of_sub_ge_mul_sqrt hscaled_nonneg hξ_mono
          (by positivity) hscaled_step'
      have hacc :
          (((k + 1 : ℝ) * Real.sqrt qf) / 2) + Real.sqrt qf / 2 ≤
            Real.arsinh (Real.sqrt qf * ξ (k + 1)) := by
        linarith
      have hacc' :
          (((k + 2 : ℝ) * Real.sqrt qf) / 2) ≤
            Real.arsinh (Real.sqrt qf * ξ (k + 1)) := by
        have hrewrite :
            (((k + 1 : ℝ) * Real.sqrt qf) / 2) + Real.sqrt qf / 2 =
              (((k + 2 : ℝ) * Real.sqrt qf) / 2) := by
          ring
        rw [← hrewrite]
        exact hacc
      have hacc'' :
          (((k + 1 + 1 : ℝ) * Real.sqrt qf) / 2) ≤
            Real.arsinh (Real.sqrt qf * ξ (k + 1)) := by
        have hrewrite' :
            (((k + 1 + 1 : ℝ) * Real.sqrt qf) / 2) =
              (((k + 2 : ℝ) * Real.sqrt qf) / 2) := by
          ring
        rw [hrewrite']
        exact hacc'
      simpa [ξ] using hacc''

/-- Helper for Lemma 2.10: the hyperbolic denominator dominates the quadratic one because
`t ≤ sinh t` on `[0, ∞)`. -/
lemma hyperbolic_bound_le_quadratic_bound
    (hμ : 0 < μ)
    (hL : 0 < L)
    (hgap : 0 < gamma0 - μ)
    (hqf : q[μ, L] ∈ Set.Ioo (0 : ℝ) 1)
    (k : ℕ) :
    let t := ((k + 1 : ℝ) * Real.sqrt q[μ, L]) / 2
    4 * μ / ((gamma0 - μ) * (Real.exp t - Real.exp (-t)) ^ (2 : ℕ)) ≤
      4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  dsimp
  have ht_nonneg : 0 ≤ ((k + 1 : ℝ) * Real.sqrt qf) / 2 := by positivity
  have ht_pos : 0 < ((k + 1 : ℝ) * Real.sqrt qf) / 2 := by positivity
  have hsinh_eq :
      Real.exp (((k + 1 : ℝ) * Real.sqrt qf) / 2) -
          Real.exp (-(((k + 1 : ℝ) * Real.sqrt qf) / 2)) =
        2 * Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) := by
    rw [Real.sinh_eq]
    ring
  have hhyper_eq :
      4 * μ /
          ((gamma0 - μ) *
            (Real.exp (((k + 1 : ℝ) * Real.sqrt qf) / 2) -
                Real.exp (-(((k + 1 : ℝ) * Real.sqrt qf) / 2))) ^ (2 : ℕ)) =
        μ /
          ((gamma0 - μ) *
            Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) := by
    calc
      4 * μ /
          ((gamma0 - μ) *
            (Real.exp (((k + 1 : ℝ) * Real.sqrt qf) / 2) -
                Real.exp (-(((k + 1 : ℝ) * Real.sqrt qf) / 2))) ^ (2 : ℕ))
          =
        4 * μ /
          ((gamma0 - μ) *
            (2 * Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2)) ^ (2 : ℕ)) := by
              rw [hsinh_eq]
      _ =
        μ /
          ((gamma0 - μ) *
            Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) := by
              by_cases hs :
                  Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) = 0
              · simp [hs]
              · field_simp [hs]
                ring
  have hsinh_ge :
      ((k + 1 : ℝ) * Real.sqrt qf) / 2 ≤
        Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) := by
    exact (Real.self_le_sinh_iff).2 ht_nonneg
  have hsinh_sq_ge :
      (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ) ≤
        Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ) := by
    have hsinh_nonneg :
        0 ≤ Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) := by
      exact (Real.sinh_nonneg_iff).2 ht_nonneg
    nlinarith [hsinh_ge, hsinh_nonneg]
  have hmono :
      μ /
          ((gamma0 - μ) *
            Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) ≤
        μ /
          ((gamma0 - μ) *
            (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) := by
    have hdenom_le :
        (gamma0 - μ) * (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ) ≤
          (gamma0 - μ) *
            Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ) := by
      gcongr
    have hInv :
        1 /
            ((gamma0 - μ) *
              Real.sinh (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) ≤
          1 /
            ((gamma0 - μ) *
              (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) := by
      exact one_div_le_one_div_of_le (by positivity) hdenom_le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hInv hμ.le
  have hquad_eq :
      μ /
          ((gamma0 - μ) *
            (((k + 1 : ℝ) * Real.sqrt qf) / 2) ^ (2 : ℕ)) =
        4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
    field_simp [hL.ne', hgap.ne']
    rw [Real.sq_sqrt hqf.1.le, div_eq_mul_inv]
    ring_nf
    field_simp [hL.ne']
  exact hhyper_eq.trans_le (hmono.trans_eq hquad_eq)

/-- Lemma 2.10: if an optimal-method recurrence has `μ > 0` and initial curvature
`γ₀ ∈ (μ, 3L + μ]`, then its canonical estimating-sequence weight `λₖ = method.weight k` is
bounded above by the stated hyperbolic expression, and that hyperbolic bound is itself bounded
above by `4L / ((γ₀ - μ) (k + 1)^2)`. -/
-- Proof sketch: first use the step-`(a)` recurrences for `γ_k` and `λ_k` to show
-- `γ_{k+1} - μ = λ_{k+1} (γ₀ - μ)`. Substitute this identity into the quadratic equation from
-- step `(a)` to obtain a scalar recurrence for `λ_k`, introduce
-- `ξ_k = sqrt (L / ((γ₀ - μ) λ_k))`, prove the claimed hyperbolic lower bound on `ξ_k` by
-- induction, and then translate that estimate back into the two displayed upper bounds for `λ_k`.
theorem weight_bounds
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (hμ : 0 < μ)
    (hgamma0 : gamma0 ∈ Set.Ioc μ (3 * L + μ))
    (k : ℕ) :
    let t := ((k + 1 : ℝ) * Real.sqrt q[μ, L]) / 2
    let hyperbolicBound :=
      4 * μ / ((gamma0 - μ) * (Real.exp t - Real.exp (-t)) ^ (2 : ℕ))
    method.weight k ≤ hyperbolicBound ∧
      hyperbolicBound ≤ 4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  let ξ : ℕ → ℝ := fun m ↦ Real.sqrt (L / ((gamma0 - μ) * method.weight m))
  let t := ((k + 1 : ℝ) * Real.sqrt qf) / 2
  let hyperbolicBound :=
    4 * μ / ((gamma0 - μ) * (Real.exp t - Real.exp (-t)) ^ (2 : ℕ))
  have hqf : qf ∈ Set.Ioo (0 : ℝ) 1 := qf_mem_Ioo_of_interval_init method hμ hgamma0
  have hgap : 0 < gamma0 - μ := by
    linarith [hgamma0.1]
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_pos : 0 < t := by
    dsimp [t]
    have hsqrt_qf_pos : 0 < Real.sqrt qf := Real.sqrt_pos.2 hqf.1
    have hk_pos : 0 < (k + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos k
    positivity
  have hxi_nonneg : 0 ≤ ξ k := by
    dsimp [ξ]
    positivity
  have hsinh_le : Real.sinh t ≤ Real.sqrt qf * ξ k := by
    -- Applying `sinh` to the discrete `arsinh` barrier exposes the exact lower bound on `ξ_k`.
    simpa [t, ξ] using
      (Real.sinh_le_sinh).2 (weight_xi_arsinh_lower_bound method hμ hgamma0 k)
  have hsinh_sq_le :
      Real.sinh t ^ (2 : ℕ) ≤ qf * ξ k ^ (2 : ℕ) := by
    have hsinh_nonneg : 0 ≤ Real.sinh t := (Real.sinh_nonneg_iff).2 ht_nonneg
    have hscaled_nonneg : 0 ≤ Real.sqrt qf * ξ k := by positivity
    have hsinh_sq_le_scaled :
        Real.sinh t ^ (2 : ℕ) ≤ (Real.sqrt qf * ξ k) ^ (2 : ℕ) := by
      nlinarith
    have hscaled_sq : (Real.sqrt qf * ξ k) ^ (2 : ℕ) = qf * ξ k ^ (2 : ℕ) := by
      nlinarith [Real.sq_sqrt hqf.1.le]
    exact hsinh_sq_le_scaled.trans_eq hscaled_sq
  have hξ_sq : ξ k ^ (2 : ℕ) = L / ((gamma0 - μ) * method.weight k) := by
    dsimp [ξ]
    rw [Real.sq_sqrt]
    apply div_nonneg
    · exact method.L_pos.le
    · exact mul_nonneg hgap.le (weight_pos method k).le
  have hqf_xi_sq :
      qf * ξ k ^ (2 : ℕ) = μ / ((gamma0 - μ) * method.weight k) := by
    let A := (gamma0 - μ) * method.weight k
    have hcancelL : (μ / L) * L = μ := by
      calc
        (μ / L) * L = μ * (L / L) := by
          field_simp [method.L_pos.ne']
        _ = μ := by
          have hLL : L / L = (1 : ℝ) := div_self method.L_pos.ne'
          calc
            μ * (L / L) = μ * 1 := by rw [hLL]
            _ = μ := by ring
    calc
      qf * ξ k ^ (2 : ℕ) =
          (μ / L) * (L / A) := by
            rw [hξ_sq]
      _ = ((μ / L) * L) * A⁻¹ := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      _ = μ * A⁻¹ := by
            rw [hcancelL]
      _ = μ / ((gamma0 - μ) * method.weight k) := by
            dsimp [A]
            rw [div_eq_mul_inv]
  have hsinh_sq_le' :
      Real.sinh t ^ (2 : ℕ) ≤ μ / ((gamma0 - μ) * method.weight k) := by
    simpa [hqf_xi_sq] using hsinh_sq_le
  have hfirst_aux :
      method.weight k ≤ μ / ((gamma0 - μ) * Real.sinh t ^ (2 : ℕ)) := by
    have hden_pos : 0 < (gamma0 - μ) * Real.sinh t ^ (2 : ℕ) := by
      positivity
    refine (le_div_iff₀ hden_pos).2 ?_
    have hweight_factor_nonneg : 0 ≤ (gamma0 - μ) * method.weight k := by
      exact mul_nonneg hgap.le (weight_pos method k).le
    have hmul := mul_le_mul_of_nonneg_left hsinh_sq_le' hweight_factor_nonneg
    have hcancel :
        ((gamma0 - μ) * method.weight k) *
            (μ / ((gamma0 - μ) * method.weight k)) = μ := by
      have hAne : ((gamma0 - μ) * method.weight k) ≠ 0 :=
        mul_ne_zero hgap.ne' (weight_pos method k).ne'
      calc
        ((gamma0 - μ) * method.weight k) *
            (μ / ((gamma0 - μ) * method.weight k))
            = μ * (((gamma0 - μ) * method.weight k) / ((gamma0 - μ) * method.weight k)) := by
                ring
        _ = μ * 1 := by rw [div_self hAne]
        _ = μ := by ring
    calc
      method.weight k * ((gamma0 - μ) * Real.sinh t ^ (2 : ℕ))
          = ((gamma0 - μ) * method.weight k) * Real.sinh t ^ (2 : ℕ) := by ring
      _ ≤ ((gamma0 - μ) * method.weight k) *
            (μ / ((gamma0 - μ) * method.weight k)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = μ := hcancel
  have hsinh_eq :
      Real.exp t - Real.exp (-t) = 2 * Real.sinh t := by
    rw [Real.sinh_eq]
    ring
  have hhyper_eq :
      μ / ((gamma0 - μ) * Real.sinh t ^ (2 : ℕ)) = hyperbolicBound := by
    dsimp [hyperbolicBound]
    calc
      μ / ((gamma0 - μ) * Real.sinh t ^ (2 : ℕ))
          =
        4 * μ / ((gamma0 - μ) * (2 * Real.sinh t) ^ (2 : ℕ)) := by
            by_cases hs : Real.sinh t = 0
            · exfalso
              exact (Real.sinh_pos_iff.2 ht_pos).ne' hs
            · field_simp [hs]
              ring
      _ = 4 * μ / ((gamma0 - μ) * (Real.exp t - Real.exp (-t)) ^ (2 : ℕ)) := by
            rw [hsinh_eq]
  have hfirst : method.weight k ≤ hyperbolicBound := by
    exact hfirst_aux.trans_eq hhyper_eq
  have hsecond : hyperbolicBound ≤ 4 * L / ((gamma0 - μ) * (k + 1 : ℝ) ^ (2 : ℕ)) := by
    simpa [t, hyperbolicBound] using
      hyperbolic_bound_le_quadratic_bound hμ method.L_pos hgap hqf k
  exact ⟨hfirst, hsecond⟩

/-- Helper for Lemma 2.10: if the initial curvature equals `μ`, then every later curvature also
equals `μ`. -/
lemma gamma_eq_mu_of_gamma0_eq_mu
    (method : OptimalMethodRecurrence f L μ x0 μ) (k : ℕ) :
    method.gamma k = μ := by
  -- The shared curvature-gap identity collapses because the initial gap is zero.
  have hgap : method.gamma k - μ = 0 := by
    simpa using gamma_sub_mu_eq_weight_mul_initial_gap method k
  linarith

/-- Helper for Lemma 2.10: in the `γ₀ = μ` regime, each owner scalar `α_k` is exactly
`sqrt q[μ, L]`. -/
lemma alpha_eq_sqrt_qf_of_gamma0_eq_mu
    (method : OptimalMethodRecurrence f L μ x0 μ) (k : ℕ) :
    method.alpha k = Real.sqrt q[μ, L] := by
  have hL : 0 < L := method.L_pos
  have hgamma : μ = L * method.alpha k ^ (2 : ℕ) := by
    simpa [gamma_eq_mu_of_gamma0_eq_mu method (k + 1)] using method.gamma_succ_eq_L_mul_sq k
  have hsq : method.alpha k ^ (2 : ℕ) = qf := by
    -- The curvature identity `γ_{k+1} = L α_k²` becomes `μ = L α_k²`.
    apply (eq_div_iff hL.ne').2
    simpa [mul_comm] using hgamma.symm
  have hsqrt_sq : (Real.sqrt qf) ^ (2 : ℕ) = qf := by
    apply Real.sq_sqrt
    exact div_nonneg method.mu_nonneg method.L_pos.le
  have hsq_eq : method.alpha k ^ (2 : ℕ) = (Real.sqrt qf) ^ (2 : ℕ) := by
    rw [hsq, hsqrt_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq with halpha | halpha
  · exact halpha
  · have halpha_pos : 0 < method.alpha k := method.alpha_pos k
    have hsqrt_nonneg : 0 ≤ Real.sqrt qf := Real.sqrt_nonneg qf
    linarith

/-- If an optimal-method recurrence is initialized with `γ₀ = μ`, expressed by specializing the
owner to `OptimalMethodRecurrence f L μ x0 μ`, then its canonical estimating-sequence weight is
the geometric progression `(1 - sqrt q[μ, L])^k`. -/
-- Proof sketch: from `γ₀ = μ` and the curvature recurrence, prove by induction that every
-- `γ_k = μ`. The quadratic equation from step `(a)` then forces `α_k = sqrt q[μ, L]` for all
-- `k`, and the recurrence `λ_{k+1} = (1 - α_k) λ_k` yields the displayed closed form.
theorem weight_eq_geometric_of_gamma0_eq_mu
    (method : OptimalMethodRecurrence f L μ x0 μ)
    (k : ℕ) :
    method.weight k = (1 - Real.sqrt q[μ, L]) ^ k := by
  induction k with
  | zero =>
      -- The zeroth weight is `1`, matching the zeroth geometric term.
      simp
  | succ k ih =>
      -- Once `α_k = sqrt q[μ, L]`, the owner weight recurrence becomes a constant-coefficient
      -- geometric recurrence.
      rw [method.weight_succ, ih, alpha_eq_sqrt_qf_of_gamma0_eq_mu method]
      simp [pow_succ, mul_comm]

/-- In the smooth-convex specialization `μ = 0`, `γ₀ = 3L`, the owner weight factor
`λₖ / (1 - λₖ)` is bounded by the rational expression used in Theorem 2.22. -/
-- Proof sketch: specialize the smooth-convex `γ₀ = 3L` scalar recurrence for `λₖ`, prove the
-- quadratic upper bound `λₖ ≤ 4 / (3 (k + 1)^2)`, and then rewrite `λₖ / (1 - λₖ)` using that
-- estimate.
theorem weight_ratio_le_of_gamma0_eq_three_mul
    (method : OptimalMethodRecurrence f L 0 x0 (3 * L))
    {k : ℕ} (hk : 1 ≤ k) :
    method.weight k / (1 - method.weight k) ≤
      4 / (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) := sorry

end OptimalMethodRecurrence

end

/-! ### Proposition_2_10 (from Chap02) -/
open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "p" => normSeminorm ℝ E

/-
Primary domain: smooth-convex accelerated first-order methods on real inner-product spaces.

Owner declarations sampled before refining this file:
* `ConvexOn ℝ Set.univ f`, `ContDiff ℝ 1 f`, and `LipschitzWith L (∇ f)` are the intrinsic
  smooth-convex objective data on the ambient real Hilbert space;
* `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` in `Theorem_2_5` is the finite-dimensional Chapter 2 bridge
  to that intrinsic owner layer;
* `ConstantStepSchemeIIMomentumRecurrence` in `Algorithm_2_4` owns the type-II acceleration data
  `(x_k, y_k, α_k)` together with the scalar and momentum recurrences.
* `ConstantStepSchemeIIRecurrence` in `Algorithm_2_4` adds the analytic side conditions for the
  same owner trajectory.
* `Theorem_2_16` shows the nearby chapter pattern: keep the accelerated trajectory as the
  source-facing owner and use `f ∈ 𝓕[L, p]¹¹` only as a finite-dimensional bridge, not as the
  primitive objective package.

Primitive data here are therefore the owner type-II recurrence specialized to `q_f = 0`,
`α₀ = 1`, together with the intrinsic smooth-convex hypotheses
`ConvexOn ℝ Set.univ f`, `ContDiff ℝ 1 f`, `LipschitzWith L (∇ f)`, and a minimizer `x*`.
The textbook parameters `t_k` are derived from the owner scalar sequence by `t_k = 1 / α_k`, so
this file keeps only bridge/view companion lemmas for that textbook reformulation on the
differentiable type-II owner. The chapter notation `f ∈ 𝓕[L, p]¹¹` is kept only as a thin
finite-dimensional specialization theorem for the main rate statement.
-/

namespace ConstantStepSchemeIIRecurrence

section

variable {L : NNReal}
variable {f : E → ℝ}
variable {x0 xStar : E}
variable
  (scheme :
    _root_.ConstantStepSchemeIIRecurrence
      E E f (L : ℝ) 0 x0 1)

local notation "t" => fun k : ℕ ↦ 1 / scheme.alpha k

private theorem alpha_pos
    (k : ℕ) :
    0 < scheme.alpha k := by
  cases k with
  | zero =>
      simp [scheme.alpha_zero]
  | succ k =>
      exact (scheme.alpha_succ_mem_Ioo k).1

/-- In the Proposition 2.10 specialization `q_f = 0`, `α₀ = 1`, the textbook parameter `t₀`
recovered from the owner scalar sequence by `t_k = 1 / α_k` is `1`. -/
theorem t_zero
    : t 0 = 1 := by
  change 1 / scheme.alpha 0 = 1
  simpa using congrArg (fun a : ℝ ↦ 1 / a) scheme.alpha_zero

/-- In the Proposition 2.10 specialization `q_f = 0`, the reciprocals `t_k = 1 / α_k` satisfy
the textbook scalar recurrence `t_{k+1} = (1 + sqrt (1 + 4 t_k^2)) / 2`. -/
theorem t_succ_eq_textbook
    (k : ℕ) :
    t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) / 2 := by
  have ht_sq :
      (t (k + 1)) ^ (2 : ℕ) =
        t (k + 1) + (t k) ^ (2 : ℕ) := by
    have hαk_ne : scheme.alpha k ≠ 0 := ne_of_gt (alpha_pos scheme k)
    have hαk1_ne : scheme.alpha (k + 1) ≠ 0 := ne_of_gt (alpha_pos scheme (k + 1))
    have hrec :
        (1 / scheme.alpha (k + 1)) ^ (2 : ℕ) =
          1 / scheme.alpha (k + 1) + (1 / scheme.alpha k) ^ (2 : ℕ) := by
      field_simp [hαk_ne, hαk1_ne]
      nlinarith [scheme.alpha_succ_equation k]
    change
      (1 / scheme.alpha (k + 1)) ^ (2 : ℕ) =
        1 / scheme.alpha (k + 1) + (1 / scheme.alpha k) ^ (2 : ℕ)
    exact hrec
  have hsq :
      (2 * t (k + 1) - 1) ^ (2 : ℕ) =
        1 + 4 * (t k) ^ (2 : ℕ) := by
    nlinarith [ht_sq]
  have hnonneg : 0 ≤ 2 * t (k + 1) - 1 := by
    have ht_gt_one : 1 < t (k + 1) := by
      change 1 < 1 / scheme.alpha (k + 1)
      exact one_lt_one_div (alpha_pos scheme (k + 1)) (scheme.alpha_succ_mem_Ioo k).2
    nlinarith
  have hsqrt :
      Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ)) =
        2 * t (k + 1) - 1 := by
    have hsqrt_sq :
        (Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) ^ (2 : ℕ) =
          (2 * t (k + 1) - 1) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt]
      · exact hsq.symm
      · positivity
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqrt_sq with hEq | hEq
    · exact hEq
    · have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ)) := Real.sqrt_nonneg _
      linarith
  nlinarith [hsqrt]

/-- In the Proposition 2.10 specialization `q_f = 0`, the owner momentum update rewrites as the
textbook formula `y_{k+1} = x_{k+1} + ((t_k - 1) / t_{k+1}) (x_{k+1} - x_k)` with
`t_k = 1 / α_k`. -/
theorem y_succ_eq_textbook
    (k : ℕ) :
    scheme.y (k + 1) =
      scheme.x (k + 1) +
        ((t k - 1) / t (k + 1)) •
          (scheme.x (k + 1) - scheme.x k) := by
  have hcoeff :
      (scheme.alpha k * (1 - scheme.alpha k)) /
          (scheme.alpha k ^ (2 : ℕ) + scheme.alpha (k + 1)) =
        (t k - 1) / t (k + 1) := by
    have hαk : 0 < scheme.alpha k := alpha_pos scheme k
    have hαk1 : 0 < scheme.alpha (k + 1) := alpha_pos scheme (k + 1)
    change
      (scheme.alpha k * (1 - scheme.alpha k)) /
          (scheme.alpha k ^ (2 : ℕ) + scheme.alpha (k + 1)) =
        ((1 / scheme.alpha k) - 1) / (1 / scheme.alpha (k + 1))
    field_simp [ne_of_gt hαk, ne_of_gt hαk1]
    nlinarith [scheme.alpha_succ_equation k]
  simpa [hcoeff] using scheme.y_succ k

/-- Helper for Proposition 2.10: the textbook scalar sequence satisfies the quadratic identity
`t_{k+1}^2 - t_{k+1} = t_k^2`. -/
private lemma t_succ_sq_sub_t_succ_eq_t_sq
    (k : ℕ) :
    (t (k + 1)) ^ (2 : ℕ) - t (k + 1) = (t k) ^ (2 : ℕ) := by
  -- Clear the reciprocal denominators in the owner scalar equation.
  have hαk_ne : scheme.alpha k ≠ 0 := ne_of_gt (alpha_pos scheme k)
  have hαk1_ne : scheme.alpha (k + 1) ≠ 0 := ne_of_gt (alpha_pos scheme (k + 1))
  change
    (1 / scheme.alpha (k + 1)) ^ (2 : ℕ) - 1 / scheme.alpha (k + 1) =
      (1 / scheme.alpha k) ^ (2 : ℕ)
  field_simp [hαk_ne, hαk1_ne]
  nlinarith [scheme.alpha_succ_equation k]

/-- Helper for Proposition 2.10: the initial objective gap is bounded by the quadratic Taylor
upper model at the minimizer. -/
private lemma initial_objective_gap_le_half_lipschitz_sqdist
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hxStar : IsMinOn f Set.univ xStar) :
    f (scheme.x 0) - f xStar ≤ ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
  have hgrad_zero : ∇ f xStar = 0 :=
    isMinOn_gradient_eq_zero hxStar
  -- Apply the smooth Taylor upper bound at the minimizer and kill the linear term.
  calc
    f (scheme.x 0) - f xStar
        ≤ firstOrderTaylorModelAt f xStar (scheme.x 0) - f xStar +
            ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
          have hupper :=
            taylor_upper_bound_of_contDiffOne_withLipschitzGradient
              hcontDiff hgrad_lipschitz xStar (scheme.x 0)
          simpa [firstOrderTaylorModelAt_apply, hgrad_zero, add_comm, add_left_comm, add_assoc]
            using hupper
    _ = ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
          simp [hgrad_zero]

/-- Helper for Proposition 2.10: the textbook scalar sequence grows by at least `1 / 2` at each
step. -/
private lemma t_succ_ge_add_half
    (k : ℕ) :
    t k + (1 : ℝ) / 2 ≤ t (k + 1) := by
  -- Compare the textbook square root with `2 * t_k` and rewrite the recurrence.
  rw [t_succ_eq_textbook scheme k]
  have ht_nonneg : 0 ≤ t k := le_of_lt (one_div_pos.mpr (alpha_pos scheme k))
  have hsq :
      (2 * t k) ^ (2 : ℕ) ≤
        (Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) ^ (2 : ℕ) := by
    rw [Real.sq_sqrt]
    · nlinarith
    · positivity
  have hsqrt_lower : 2 * t k ≤ Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ)) := by
    nlinarith [hsq, Real.sqrt_nonneg (1 + 4 * (t k) ^ (2 : ℕ))]
  nlinarith

/-- Helper for Proposition 2.10: the textbook sequence satisfies the elementary lower bound
`(k + 2) / 2 ≤ t_k`. -/
private lemma nat_add_two_div_two_le_t
    : ∀ k : ℕ, ((k + 2 : ℕ) : ℝ) / 2 ≤ t k := by
  intro k
  induction k with
  | zero =>
      -- Start the induction from the explicit initial scalar `t₀ = 1`.
      norm_num [t_zero scheme]
  | succ k hk =>
      -- Each step adds at least `1 / 2`, so the arithmetic lower bound propagates.
      have hstep := t_succ_ge_add_half scheme k
      have hnext : (((k + 3 : ℕ) : ℝ) / 2) ≤ t (k + 1) := by
        have hk' : (((k + 2 : ℕ) : ℝ) / 2) + (1 : ℝ) / 2 ≤ t (k + 1) := by
          nlinarith
        have harith :
            (((k + 3 : ℕ) : ℝ) / 2) = (((k + 2 : ℕ) : ℝ) / 2) + (1 : ℝ) / 2 := by
          have harith' : ((k : ℝ) + 3) / 2 = ((k : ℝ) + 2) / 2 + (1 : ℝ) / 2 := by
            ring
          simpa [Nat.cast_add, add_assoc] using harith'
        rw [harith]
        exact hk'
      simpa [Nat.succ_eq_add_one, add_assoc] using hnext

/-- Helper for Proposition 2.10: the transformed auxiliary point
`z_k = t_k y_k - (t_k - 1) x_k`. -/
private def textbookAuxPoint
    (k : ℕ) : E :=
  (t k) • scheme.y k - (t k - 1) • scheme.x k

/-- Helper for Proposition 2.10: the transformed auxiliary point starts from the initial
iterate. -/
private lemma textbook_aux_point_zero :
    textbookAuxPoint scheme 0 = scheme.x 0 := by
  -- At time `0`, both owner trajectories start from `x₀` and `t₀ = 1`.
  have hyx : scheme.y 0 = scheme.x 0 := by
    simpa [scheme.x_zero] using scheme.y_zero
  simp [textbookAuxPoint, t_zero scheme, hyx]

/-- Helper for Proposition 2.10: the transformed auxiliary point relative to the minimizer splits
into the base displacement and the momentum correction. -/
private lemma textbook_aux_point_affine_identity
    (k : ℕ) :
    textbookAuxPoint scheme k - xStar =
      (scheme.y k - xStar) + (t k - 1) • (scheme.y k - scheme.x k) := by
  -- Separate the `1 • y_k` part from `t_k • y_k` and then regroup the affine terms.
  have ht :
      (t k) • scheme.y k = scheme.y k + (t k - 1) • scheme.y k := by
    calc
      (t k) • scheme.y k = (1 + (t k - 1)) • scheme.y k := by
        congr 1
        ring
      _ = scheme.y k + (t k - 1) • scheme.y k := by
        rw [add_smul, one_smul]
  rw [textbookAuxPoint, ht, smul_sub, sub_eq_add_neg]
  abel

/-- Helper for Proposition 2.10: the momentum coefficient in the textbook `y_{k+1}` update
collapses after multiplication by `t_{k+1}`. -/
private lemma scaled_momentum_coefficient_smul
    (k : ℕ)
    (v : E) :
    (t (k + 1)) • (((t k - 1) / t (k + 1)) • v) = (t k - 1) • v := by
  -- Cancel the explicit `t_{k+1}` denominator before returning to module notation.
  have ht_ne : t (k + 1) ≠ 0 := by
    exact ne_of_gt (one_div_pos.mpr (alpha_pos scheme (k + 1)))
  calc
    (t (k + 1)) • (((t k - 1) / t (k + 1)) • v)
        = (t (k + 1) * ((t k - 1) / t (k + 1))) • v := by
            rw [smul_smul]
    _ = ((t k - 1) * (t (k + 1) * (t (k + 1))⁻¹)) • v := by
          rw [div_eq_mul_inv]
          ring_nf
    _ = (t k - 1) • v := by
          rw [mul_inv_cancel₀ ht_ne, mul_one]

/-- Helper for Proposition 2.10: the transformed auxiliary point satisfies the exact textbook
gradient-step update `z_{k+1} = z_k - (t_k / L) ∇ f(y_k)`. -/
private lemma textbook_aux_point_step
    (k : ℕ) :
    textbookAuxPoint scheme (k + 1) =
      textbookAuxPoint scheme k - ((t k) / (L : ℝ)) • ∇ f (scheme.y k) := by
  -- Rewrite `z_{k+1}` with the textbook `y_{k+1}` formula, cancel the scalar coefficient,
  -- and then substitute the exact gradient step for `x_{k+1}`.
  have hx_succ :
      ((scheme.x (k + 1) : E)) = scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k) := by
    simpa using scheme.x_succ k
  calc
    textbookAuxPoint scheme (k + 1)
        = (t (k + 1)) •
            (scheme.x (k + 1) +
              ((t k - 1) / t (k + 1)) • (scheme.x (k + 1) - scheme.x k)) -
            (t (k + 1) - 1) • scheme.x (k + 1) := by
              rw [textbookAuxPoint, y_succ_eq_textbook scheme k]
    _ = (t (k + 1)) • scheme.x (k + 1) +
          (t k - 1) • (scheme.x (k + 1) - scheme.x k) -
          (t (k + 1) - 1) • scheme.x (k + 1) := by
            rw [smul_add, scaled_momentum_coefficient_smul scheme k]
    _ = (t k) • scheme.x (k + 1) - (t k - 1) • scheme.x k := by
          rw [smul_sub]
          module
    _ = (t k) • (scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k)) -
          (t k - 1) • scheme.x k := by
            change
              (t k) • ((scheme.x (k + 1) : E)) - (t k - 1) • (scheme.x k : E) =
                (t k) • (scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k)) -
                  (t k - 1) • (scheme.x k : E)
            rw [hx_succ]
    _ = textbookAuxPoint scheme k - ((t k) / (L : ℝ)) • ∇ f (scheme.y k) := by
          rw [textbookAuxPoint, smul_sub, smul_smul]
          module

/-- Helper for Proposition 2.10: the convexity inequalities at `y_k` combine into the weighted
textbook bridge
`t_k (f(y_k) - f*) - (t_k - 1) (f(x_k) - f*) ≤ ⟪∇ f(y_k), z_k - x*⟫`. -/
private lemma textbook_weighted_convexity_bridge
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (k : ℕ) :
    (t k) * (f (scheme.y k) - f xStar) -
        (t k - 1) * (f (scheme.x k) - f xStar) ≤
      inner ℝ (∇ f (scheme.y k)) (textbookAuxPoint scheme k - xStar) := by
  let gk : E := ∇ f (scheme.y k)
  have lower_tangent_plane_gap (y : E) :
      f (scheme.y k) - f y ≤ inner ℝ gk (scheme.y k - y) := by
    have hsupport :
        f y ≥ f (scheme.y k) + inner ℝ gk (y - scheme.y k) := by
      simpa [gk, gradientWithin, gradient, fderivWithin_univ] using
        hconvex.lower_tangent_plane
          (scheme.y k) (by simp)
          ((hcontDiff.differentiable_one (scheme.y k)).differentiableWithinAt)
          y (by simp)
    have hinner :
        inner ℝ gk (y - scheme.y k) = -inner ℝ gk (scheme.y k - y) := by
      calc
        inner ℝ gk (y - scheme.y k) = inner ℝ gk (-(scheme.y k - y)) := by
          congr 2
          abel
        _ = -inner ℝ gk (scheme.y k - y) := by
          rw [inner_neg_right]
    rw [hinner] at hsupport
    linarith
  have hy_star :
      f (scheme.y k) - f xStar ≤ inner ℝ gk (scheme.y k - xStar) :=
    lower_tangent_plane_gap xStar
  have hy_x :
      f (scheme.y k) - f (scheme.x k) ≤ inner ℝ gk (scheme.y k - scheme.x k) :=
    lower_tangent_plane_gap (scheme.x k)
  have hweight : 0 ≤ t k - 1 := by
    have ht_lower := nat_add_two_div_two_le_t scheme k
    have hk_nonneg : (0 : ℝ) ≤ k := by
      exact_mod_cast Nat.zero_le k
    have hhalf_decomp : (((k + 2 : ℕ) : ℝ) / 2) = (k : ℝ) / 2 + 1 := by
      calc
        (((k + 2 : ℕ) : ℝ) / 2) = ((k : ℝ) + 2) / 2 := by
          norm_num [Nat.cast_add]
        _ = (k : ℝ) / 2 + 1 := by
          ring
    have hone : (1 : ℝ) ≤ (((k + 2 : ℕ) : ℝ) / 2) := by
      rw [hhalf_decomp]
      nlinarith
    nlinarith
  have hy_x_scaled :
      (t k - 1) * (f (scheme.y k) - f (scheme.x k)) ≤
        inner ℝ gk ((t k - 1) • (scheme.y k - scheme.x k)) := by
    -- Scale the second convexity bound by the nonnegative weight `t_k - 1`.
    have hscaled := mul_le_mul_of_nonneg_left hy_x hweight
    simpa [gk, real_inner_smul_right] using hscaled
  have hsum :
      (f (scheme.y k) - f xStar) + (t k - 1) * (f (scheme.y k) - f (scheme.x k)) ≤
        inner ℝ gk
          ((scheme.y k - xStar) + (t k - 1) • (scheme.y k - scheme.x k)) := by
    -- Add the two tangent-plane inequalities and package the right-hand side as one inner product.
    have hadd := add_le_add hy_star hy_x_scaled
    simpa [gk, inner_add_right] using hadd
  have hlhs :
      (t k) * (f (scheme.y k) - f xStar) -
          (t k - 1) * (f (scheme.x k) - f xStar) =
        (f (scheme.y k) - f xStar) +
          (t k - 1) * (f (scheme.y k) - f (scheme.x k)) := by
    ring
  have haux :
      textbookAuxPoint scheme k - xStar =
        (scheme.y k - xStar) + (t k - 1) • (scheme.y k - scheme.x k) :=
    textbook_aux_point_affine_identity scheme k
  rw [hlhs]
  simpa [haux] using hsum

/-- Helper for Proposition 2.10: the transformed textbook Lyapunov quantity decreases at each
step. -/
private lemma textbook_potential_drop
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (k : ℕ) :
    (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) +
        ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      ((t k) ^ (2 : ℕ) - t k) * (f (scheme.x k) - f xStar) +
        ((L : ℝ) / 2) * ‖textbookAuxPoint scheme k - xStar‖ ^ (2 : ℕ) := by
  let gk : E := ∇ f (scheme.y k)
  have hdescent :
      f (scheme.x (k + 1)) ≤
        f (scheme.y k) - (1 / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Use the direct smooth descent estimate at the extrapolated point `y_k`.
    have hcoeff :
        (1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2) =
          1 / (2 * (L : ℝ)) := by
      field_simp [scheme.L_pos.ne']
      ring
    have hx_succ :
        ((scheme.x (k + 1) : E)) = scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k) := by
      simpa using scheme.x_succ k
    have hstep :
        f (scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k)) ≤
          f (scheme.y k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := by
      simpa [gk] using
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          hcontDiff hgrad_lipschitz (scheme.y k) (1 / (L : ℝ))
    have hstep' :
        f (scheme.x (k + 1)) ≤
          f (scheme.y k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := by
      simpa [hx_succ] using hstep
    calc
      f (scheme.x (k + 1)) ≤
          f (scheme.y k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := hstep'
      _ = f (scheme.y k) - (1 / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
          rw [hcoeff]
  have hdescent_scaled :
      (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) ≤
        (t k) ^ (2 : ℕ) * (f (scheme.y k) - f xStar) -
          ((t k) ^ (2 : ℕ) / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Multiply the one-step descent estimate by `t_k^2`.
    have ht_sq_nonneg : 0 ≤ (t k) ^ (2 : ℕ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hdescent ht_sq_nonneg
    ring_nf at hscaled ⊢
    linarith
  have ht_nonneg : 0 ≤ t k := le_of_lt (one_div_pos.mpr (alpha_pos scheme k))
  have hbridge_scaled :
      (t k) ^ (2 : ℕ) * (f (scheme.y k) - f xStar) -
          (t k) * (t k - 1) * (f (scheme.x k) - f xStar) ≤
        (t k) * inner ℝ gk (textbookAuxPoint scheme k - xStar) := by
    -- Multiply the weighted convexity bridge by the nonnegative factor `t_k`.
    have hbridge :
        (t k) * (f (scheme.y k) - f xStar) -
            (t k - 1) * (f (scheme.x k) - f xStar) ≤
          inner ℝ (∇ f (scheme.y k)) (textbookAuxPoint scheme k - xStar) :=
      textbook_weighted_convexity_bridge scheme hconvex hcontDiff k
    have hscaled :=
      mul_le_mul_of_nonneg_left hbridge ht_nonneg
    nlinarith
  have hquad :
      ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) =
        ((L : ℝ) / 2) * ‖textbookAuxPoint scheme k - xStar‖ ^ (2 : ℕ) -
          (t k) * inner ℝ gk (textbookAuxPoint scheme k - xStar) +
          ((t k) ^ (2 : ℕ) / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Expand the next norm square after rewriting `z_{k+1}` as a single gradient step from `z_k`.
    have hz :
        textbookAuxPoint scheme (k + 1) - xStar =
          (textbookAuxPoint scheme k - xStar) - ((t k) / (L : ℝ)) • gk := by
      calc
        textbookAuxPoint scheme (k + 1) - xStar
            = (textbookAuxPoint scheme k - ((t k) / (L : ℝ)) • gk) - xStar := by
                rw [textbook_aux_point_step scheme k]
        _ = (textbookAuxPoint scheme k - xStar) - ((t k) / (L : ℝ)) • gk := by
              abel
    have hL_ne : (L : ℝ) ≠ 0 := scheme.L_pos.ne'
    rw [hz, norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm (textbookAuxPoint scheme k - xStar) gk]
    field_simp [hL_ne]
  -- Add the scaled descent inequality to the expanded norm-square identity and cancel the bridge.
  nlinarith [hdescent_scaled, hbridge_scaled, hquad]

/-- Helper for Proposition 2.10: the transformed textbook Lyapunov quantity is bounded by the
initial quadratic energy. -/
private lemma textbook_potential_le_initial
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    ∀ k : ℕ,
      (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) +
          ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
  intro k
  induction k with
  | zero =>
      -- Start the Lyapunov estimate from the step-`0` drop and the explicit identities `t₀ = 1`,
      -- `z₀ = x₀`.
      have hdrop :
          (t 0) ^ (2 : ℕ) * (f (scheme.x (0 + 1)) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (0 + 1) - xStar‖ ^ (2 : ℕ) ≤
            ((t 0) ^ (2 : ℕ) - t 0) * (f (scheme.x 0) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme 0 - xStar‖ ^ (2 : ℕ) :=
        textbook_potential_drop scheme hconvex hcontDiff hgrad_lipschitz 0
      simpa [scheme.alpha_zero, textbook_aux_point_zero scheme] using hdrop
  | succ k hk =>
      -- Use the one-step drop at time `k + 1` and identify the predecessor coefficient
      -- `t_{k+1}^2 - t_{k+1}` with `t_k^2`.
      have hdrop :
          (t (k + 1)) ^ (2 : ℕ) * (f (scheme.x (k + 2)) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 2) - xStar‖ ^ (2 : ℕ) ≤
            ((t (k + 1)) ^ (2 : ℕ) - t (k + 1)) * (f (scheme.x (k + 1)) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) :=
        textbook_potential_drop scheme hconvex hcontDiff hgrad_lipschitz (k + 1)
      rw [t_succ_sq_sub_t_succ_eq_t_sq scheme k] at hdrop
      exact hdrop.trans hk

/-- Proposition 2.10: for a smooth convex objective, every type-II recurrence specialized to
`q_f = 0`, `α₀ = 1`, and the exact gradient step
`x_{k+1} = y_k - (1 / L) ∇ f(y_k)` satisfies the textbook quadratic function-value bound.

This is the owner-abstraction form of the proposition: the textbook sequence `t_k` is the derived
reciprocal `t_k = 1 / α_k`, and the iterate sequence is the owner field `scheme.x`, equivalently
the coercion `scheme : ℕ → E`. -/
-- Proof sketch: view the `q_f = 0` type-II recurrence as the smooth-convex optimal-method
-- specialization with `γ₀ = 3L` encoded through the owner scalar sequence `α_k`. Apply the
-- chapter's estimating-sequence quadratic-rate argument to the owner trajectory, then rewrite the
-- displayed textbook constants using `scheme.x_zero`, equivalently `scheme.x 0 = x₀`.
theorem objective_gap_le_quadratic_rate
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (scheme.x k) - f xStar ≤
      (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  -- Route correction: the old placeholder cited the later optimal-method theorem. Here we keep
  -- the dependency-closed route inside Proposition 2.10 itself via the textbook `t_k` scalars.
  have hbase :
      f (scheme.x 0) - f xStar ≤
        (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
          (3 * (0 + 1 : ℝ) ^ (2 : ℕ)) := by
    have hinit :=
      initial_objective_gap_le_half_lipschitz_sqdist scheme hcontDiff hgrad_lipschitz hxStar
    have hscaled : ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) ≤
        (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
          (3 * (0 + 1 : ℝ) ^ (2 : ℕ)) := by
      nlinarith [L.2, sq_nonneg ‖scheme.x 0 - xStar‖]
    exact hinit.trans hscaled
  cases k with
  | zero =>
      simpa using hbase
  | succ k =>
      -- Use the Lyapunov bound at index `k`, discard the nonnegative quadratic term,
      -- and convert the remaining `t_k` denominator using the elementary scalar lower bound.
      have hpot :
          (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) ≤
            ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) :=
        textbook_potential_le_initial scheme hconvex hcontDiff hgrad_lipschitz k
      have hquad_nonneg :
          0 ≤ ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) := by
        positivity
      have hgap :
          (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) ≤
            ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
        linarith
      have hgap_nonneg : 0 ≤ f (scheme.x (k + 1)) - f xStar := by
        exact sub_nonneg.mpr ((isMinOn_iff.mp hxStar) (scheme.x (k + 1)) (by simp))
      have ht_lower := nat_add_two_div_two_le_t scheme k
      have hrate_mul :
          (f (scheme.x (k + 1)) - f xStar) * ((k + 2 : ℕ) : ℝ) ^ (2 : ℕ) ≤
            2 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
        have htk :
            (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 4 * (t k) ^ (2 : ℕ) := by
          have hk_half_nonneg : 0 ≤ (((k + 2 : ℕ) : ℝ) / 2) := by
            positivity
          have ht_nonneg : 0 ≤ t k := by
            exact le_of_lt (one_div_pos.mpr (alpha_pos scheme k))
          nlinarith
        nlinarith [hgap, htk, hgap_nonneg]
      have hden_pos : 0 < (3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) := by
        positivity
      have hrate_target_mul :
          (f (scheme.x (k + 1)) - f xStar) * ((3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ))) ≤
            8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
        nlinarith [hrate_mul]
      have hfinal :
          f (scheme.x (k + 1)) - f xStar ≤
            (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
              ((3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ))) := by
        refine (le_div_iff₀ hden_pos).2 ?_
        nlinarith [hrate_target_mul]
      have hden_eq :
          ((3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ))) =
            3 * ((((k + 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ)) := by
        calc
          ((3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)))
              = (3 : ℝ) * ((((k : ℝ) + 1) + 1) ^ (2 : ℕ)) := by
                  norm_num [Nat.cast_add, add_assoc]
          _ = 3 * ((((k + 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ)) := by
                norm_num [Nat.cast_add, add_assoc]
      rw [hden_eq] at hfinal
      exact hfinal

/-- Finite-dimensional Chapter 2 bridge form of Proposition 2.10 using the source notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`. -/
theorem objective_gap_le_quadratic_rate_of_mem_F11
    [FiniteDimensional ℝ E]
    (hf : f ∈ 𝓕[L, p]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (scheme.x k) - f xStar ≤
      (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) :=
  objective_gap_le_quadratic_rate scheme
    hf.convexOn hf.contDiff hf.gradient_lipschitz hxStar k

end

end ConstantStepSchemeIIRecurrence

end
