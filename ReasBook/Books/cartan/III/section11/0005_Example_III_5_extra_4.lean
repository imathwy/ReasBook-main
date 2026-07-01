import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex
open scoped Topology

/-
This example is `source-facing` for one concrete meromorphic function. Its pole and residue data
use the core/canonical owners `meromorphicOrderAt` and `meromorphicTrailingCoeffAt`; the
punctured-neighborhood limit is kept only as a `bridge/view` companion via
`MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt`.
-/

local notation "f" => fun z : ℂ ↦ exp (I * z) / (z ^ 2 + 1)

/-- Helper for Example III.5-extra-4: on a punctured neighborhood of `I`, the function
`z ↦ exp (I * z) / (z ^ 2 + 1)` is the principal part `(z - I)⁻¹` times the analytic quotient
`z ↦ exp (I * z) / (z + I)`. -/
lemma eventuallyEq_exp_I_mul_div_z_sq_add_one_factor_at_I :
    f =ᶠ[𝓝[≠] I] fun z : ℂ ↦ (z - I) ^ (-1 : ℤ) • (exp (I * z) / (z + I)) := by
  -- Factor `z ^ 2 + 1` as `(z - I) * (z + I)` and then reorder the inverse factors.
  refine Filter.Eventually.of_forall fun z ↦ ?_
  change exp (I * z) / (z ^ 2 + 1) = (z - I) ^ (-1 : ℤ) • (exp (I * z) / (z + I))
  have hfactor : z ^ 2 + 1 = (z - I) * (z + I) := by
    calc
      z ^ 2 + 1 = z ^ 2 - I ^ 2 := by simp [pow_two, Complex.I_mul_I]
      _ = (z - I) * (z + I) := by ring
  rw [hfactor, div_eq_mul_inv, smul_eq_mul, zpow_neg_one, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Helper for Example III.5-extra-4: on a punctured neighborhood of `-I`, the function
`z ↦ exp (I * z) / (z ^ 2 + 1)` is the principal part `(z + I)⁻¹` times the analytic quotient
`z ↦ exp (I * z) / (z - I)`. -/
lemma eventuallyEq_exp_I_mul_div_z_sq_add_one_factor_at_neg_I :
    f =ᶠ[𝓝[≠] (-I)] fun z : ℂ ↦ (z - (-I)) ^ (-1 : ℤ) • (exp (I * z) / (z - I)) := by
  -- Use the symmetric factorization `z ^ 2 + 1 = (z + I) * (z - I)`.
  refine Filter.Eventually.of_forall fun z ↦ ?_
  change exp (I * z) / (z ^ 2 + 1) = (z - (-I)) ^ (-1 : ℤ) • (exp (I * z) / (z - I))
  have hfactor : z ^ 2 + 1 = (z - (-I)) * (z - I) := by
    calc
      z ^ 2 + 1 = z ^ 2 - I ^ 2 := by simp [pow_two, Complex.I_mul_I]
      _ = (z - (-I)) * (z - I) := by ring
  rw [hfactor, div_eq_mul_inv, smul_eq_mul, zpow_neg_one, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Helper for Example III.5-extra-4: the analytic quotient left after removing the simple pole at
`I` evaluates to the textbook residue value. -/
lemma exp_I_mul_div_z_add_I_at_I :
    (fun z : ℂ ↦ exp (I * z) / (z + I)) I = -I / ((((2 : ℝ) * Real.exp 1 : ℝ) : ℂ)) := by
  -- Evaluate the quotient at `I`, convert `exp (-1)` to `1 / exp 1`, and simplify `1 / I`.
  have htwoI : (I : ℂ) + I = 2 * I := by
    ring
  have hexp : exp (1 : ℂ) = (((Real.exp 1 : ℝ) : ℂ)) := by
    exact (Complex.ofReal_exp (1 : ℝ)).symm
  calc
    (fun z : ℂ ↦ exp (I * z) / (z + I)) I = exp (-1 : ℂ) / (2 * I) := by
      simp [Complex.I_mul_I, htwoI]
    _ = -I / ((((2 : ℝ) * Real.exp 1 : ℝ) : ℂ)) := by
      rw [Complex.exp_neg, hexp]
      simp [div_eq_mul_inv, Complex.inv_I, mul_comm, mul_left_comm]

/-- Example III.5-extra-4 (1): the function
`z ↦ exp (I * z) / (z ^ 2 + 1)` has a simple pole at `z = I`. -/
theorem meromorphicOrderAt_exp_I_mul_div_z_sq_add_one_at_I :
    meromorphicOrderAt f I =
      (-1 : ℤ) := by
  -- Use the isolated factor `(z - I)⁻¹` as the normal form at the pole.
  have hdenomAtI : (fun z : ℂ ↦ z + I) I ≠ 0 := by
    have hrewrite : (I : ℂ) + I = (2 : ℂ) * I := by
      ring
    have htwo_ne : (2 : ℂ) ≠ 0 := by
      norm_num
    simp [hrewrite, htwo_ne, Complex.I_ne_zero]
  have hanalyticExp : AnalyticAt ℂ (fun z : ℂ ↦ exp (I * z)) I := by
    fun_prop
  have hanalyticDen : AnalyticAt ℂ (fun z : ℂ ↦ z + I) I := by
    fun_prop
  have hanalytic : AnalyticAt ℂ (fun z : ℂ ↦ exp (I * z) / (z + I)) I :=
    hanalyticExp.div hanalyticDen hdenomAtI
  have hdenom : ((((2 : ℝ) * Real.exp 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (Real.exp_pos 1).ne'
  have hnonzero : (fun z : ℂ ↦ exp (I * z) / (z + I)) I ≠ 0 := by
    rw [exp_I_mul_div_z_add_I_at_I]
    exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hdenom
  have hf : MeromorphicAt f I := by
    -- The punctured-neighborhood factorization exhibits `f` as meromorphic at `I`.
    rw [MeromorphicAt.meromorphicAt_congr eventuallyEq_exp_I_mul_div_z_sq_add_one_factor_at_I]
    fun_prop
  rw [meromorphicOrderAt_eq_int_iff hf]
  exact ⟨fun z : ℂ ↦ exp (I * z) / (z + I), hanalytic, hnonzero,
    eventuallyEq_exp_I_mul_div_z_sq_add_one_factor_at_I⟩

/-- Example III.5-extra-4 (2): the function
`z ↦ exp (I * z) / (z ^ 2 + 1)` has a simple pole at `z = -I`. -/
theorem meromorphicOrderAt_exp_I_mul_div_z_sq_add_one_at_neg_I :
    meromorphicOrderAt f (-I) =
      (-1 : ℤ) := by
  -- The same isolated-factor argument works at `-I` after swapping the linear factors.
  have hdenomAtNegI : (fun z : ℂ ↦ z - I) (-I) ≠ 0 := by
    have hrewrite : ((-I : ℂ) - I) = (-2 : ℂ) * I := by
      ring
    have htwo_ne : (-2 : ℂ) ≠ 0 := by
      norm_num
    have hmul : ((-2 : ℂ) * I) ≠ 0 := mul_ne_zero htwo_ne Complex.I_ne_zero
    change ((-I : ℂ) - I) ≠ 0
    rw [hrewrite]
    exact hmul
  have hanalyticExp : AnalyticAt ℂ (fun z : ℂ ↦ exp (I * z)) (-I) := by
    fun_prop
  have hanalyticDen : AnalyticAt ℂ (fun z : ℂ ↦ z - I) (-I) := by
    fun_prop
  have hanalytic : AnalyticAt ℂ (fun z : ℂ ↦ exp (I * z) / (z - I)) (-I) :=
    hanalyticExp.div hanalyticDen hdenomAtNegI
  have hdenom : ((-I : ℂ) - I) ≠ 0 := by
    have hrewrite : ((-I : ℂ) - I) = (-2 : ℂ) * I := by ring
    rw [hrewrite]
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hnonzero : (fun z : ℂ ↦ exp (I * z) / (z - I)) (-I) ≠ 0 := by
    simpa using div_ne_zero (exp_ne_zero (I * (-I))) hdenom
  have hf : MeromorphicAt f (-I) := by
    -- This symmetric factorization again supplies the local meromorphic normal form.
    rw [MeromorphicAt.meromorphicAt_congr eventuallyEq_exp_I_mul_div_z_sq_add_one_factor_at_neg_I]
    fun_prop
  rw [meromorphicOrderAt_eq_int_iff hf]
  exact ⟨fun z : ℂ ↦ exp (I * z) / (z - I), hanalytic, hnonzero,
    eventuallyEq_exp_I_mul_div_z_sq_add_one_factor_at_neg_I⟩

/-- Example III.5-extra-4 (3): the residue of
`z ↦ exp (I * z) / (z ^ 2 + 1)` at the simple pole `z = I` is
`-I / (2 * exp 1)`. -/
theorem residue_exp_I_mul_div_z_sq_add_one_at_I :
    meromorphicTrailingCoeffAt f I =
      (-I / (((2 : ℝ) * Real.exp 1 : ℝ) : ℂ)) := by
  -- The trailing coefficient at a simple pole is the value of the analytic quotient.
  have hdenomAtI : (fun z : ℂ ↦ z + I) I ≠ 0 := by
    have hrewrite : (I : ℂ) + I = (2 : ℂ) * I := by
      ring
    have htwo_ne : (2 : ℂ) ≠ 0 := by
      norm_num
    simp [hrewrite, htwo_ne, Complex.I_ne_zero]
  have hanalyticExp : AnalyticAt ℂ (fun z : ℂ ↦ exp (I * z)) I := by
    fun_prop
  have hanalyticDen : AnalyticAt ℂ (fun z : ℂ ↦ z + I) I := by
    fun_prop
  have hanalytic : AnalyticAt ℂ (fun z : ℂ ↦ exp (I * z) / (z + I)) I :=
    hanalyticExp.div hanalyticDen hdenomAtI
  have hdenom : ((((2 : ℝ) * Real.exp 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (Real.exp_pos 1).ne'
  have hnonzero : (fun z : ℂ ↦ exp (I * z) / (z + I)) I ≠ 0 := by
    rw [exp_I_mul_div_z_add_I_at_I]
    exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hdenom
  rw [hanalytic.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := -1) hnonzero
    eventuallyEq_exp_I_mul_div_z_sq_add_one_factor_at_I]
  exact exp_I_mul_div_z_add_I_at_I

/-- Bridge/view form of Example III.5-extra-4 (3): the residue value above is equivalently the
punctured-neighborhood limit of `(z - I) * f z`. -/
theorem tendsto_sub_I_mul_exp_I_mul_div_z_sq_add_one_at_I :
    Filter.Tendsto
      (fun z : ℂ ↦
        (z - I) * f z)
      (𝓝[≠] I)
      (𝓝 (-I / (((2 : ℝ) * Real.exp 1 : ℝ) : ℂ))) := by
  -- On the punctured neighborhood, multiplying by `z - I` cancels the simple-pole factor.
  have hfactor :
      (fun z : ℂ ↦ (z - I) * f z) =ᶠ[𝓝[≠] I] fun z : ℂ ↦ exp (I * z) / (z + I) := by
    filter_upwards [eventuallyEq_exp_I_mul_div_z_sq_add_one_factor_at_I, self_mem_nhdsWithin] with
      z hz hz_ne
    rw [hz]
    have hsub : z - I ≠ 0 := sub_ne_zero.mpr hz_ne
    simp [smul_eq_mul, hsub]
  have hdenomAtI : (fun z : ℂ ↦ z + I) I ≠ 0 := by
    have hrewrite : (I : ℂ) + I = (2 : ℂ) * I := by
      ring
    have htwo_ne : (2 : ℂ) ≠ 0 := by
      norm_num
    simp [hrewrite, htwo_ne, Complex.I_ne_zero]
  have hanalyticExp : AnalyticAt ℂ (fun z : ℂ ↦ exp (I * z)) I := by
    fun_prop
  have hanalyticDen : AnalyticAt ℂ (fun z : ℂ ↦ z + I) I := by
    fun_prop
  have hanalytic : AnalyticAt ℂ (fun z : ℂ ↦ exp (I * z) / (z + I)) I :=
    hanalyticExp.div hanalyticDen hdenomAtI
  have htendsto :
      Filter.Tendsto (fun z : ℂ ↦ exp (I * z) / (z + I)) (𝓝[≠] I)
        (𝓝 (-I / (((2 : ℝ) * Real.exp 1 : ℝ) : ℂ))) := by
    -- The analytic quotient is continuous at `I`, so its punctured limit is its value there.
    have hcont :
        Filter.Tendsto (fun z : ℂ ↦ exp (I * z) / (z + I)) (𝓝[≠] I)
          (𝓝 ((fun z : ℂ ↦ exp (I * z) / (z + I)) I)) := by
      exact hanalytic.continuousAt.continuousWithinAt.tendsto
    rw [exp_I_mul_div_z_add_I_at_I] at hcont
    simpa [Complex.ofReal_exp, mul_comm, mul_left_comm, mul_assoc] using hcont
  exact Filter.Tendsto.congr' hfactor.symm htendsto
