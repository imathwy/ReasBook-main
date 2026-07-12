import Mathlib
import DifferentialForms_Cartan_1970.II.section06.«0010_Theorem_3»
import DifferentialForms_Cartan_1970.III.section07.«0001_Remark_III_1_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the proof is organized directly around mathlib's Taylor-series API and the local Cauchy bound.

open FormalMultilinearSeries
open scoped BigOperators Topology

noncomputable section

/-- The scalar Taylor coefficient of an entire complex function at the origin. -/
def taylorCoeff (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k f 0 / k.factorial

/-- Helper for Exercise 4: Cauchy's inequality bounds the `k`-th Taylor coefficient at `0` on a
large circle once the exterior growth hypothesis controls the boundary values there. -/
lemma taylor_coeff_norm_le_of_exterior_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M r : ℝ} (hr0 : 0 < r) (hR : R ≤ r)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) (k : ℕ) :
    ‖taylorCoeff f k‖ ≤ max M 0 * r ^ (n - (k : ℤ)) := by
  have hball : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (r + 1)) := by
    intro z hz
    exact (hf z).differentiableWithinAt
  let p : FormalMultilinearSeries ℂ ℂ ℂ := ofScalars ℂ (fun m ↦ taylorCoeff f m)
  have hseries : HasFPowerSeriesAt f p 0 := by
    -- The global Taylor series of an entire function is a power-series expansion at the origin.
    rw [hasFPowerSeriesAt_iff]
    refine Filter.Eventually.of_forall ?_
    intro z
    simpa [p, taylorCoeff, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (Complex.hasSum_taylorSeries_of_entire (f := f) hf 0 z)
  have hseriesBall :
      HasFPowerSeriesOnBall f p 0 (ENNReal.ofReal (r + 1)) := by
    rcases
        holomorphic_on_disc_has_power_series_expansion
          (f := f) (ρ := r + 1) (by positivity) hball with
      ⟨a, ha⟩
    have hcoeffs : a = fun m ↦ taylorCoeff f m := by
      funext m
      -- Uniqueness identifies the local disc expansion with the Taylor expansion at the origin.
      have hpeq :
          ofScalars ℂ a = p := ha.hasFPowerSeriesAt.eq_formalMultilinearSeries hseries
      have hm := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q.coeff m) hpeq
      simpa [p, FormalMultilinearSeries.coeff_ofScalars, taylorCoeff] using hm
    simpa [p, hcoeffs] using ha
  have hcircle :
      ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ max M 0 * r ^ n := by
    intro z hz
    have hznorm : ‖z‖ = r := by
      simpa [Metric.mem_sphere, sub_zero] using hz
    have hzR : R ≤ ‖z‖ := by
      rw [hznorm]
      exact hR
    calc
      ‖f z‖ ≤ M * ‖z‖ ^ n := hbound z hzR
      _ = M * r ^ n := by rw [hznorm]
      _ ≤ max M 0 * r ^ n := by
        exact mul_le_mul_of_nonneg_right (le_max_left M 0) (by positivity)
  have hcoeff :
      ‖p.coeff k‖ ≤ (max M 0 * r ^ n) / r ^ k := by
    simpa [p] using
      norm_taylor_coefficient_le_of_circle_bound (f := f) (a := fun m ↦ taylorCoeff f m) k
        hseriesBall hr0 (by linarith) hcircle
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  calc
    ‖taylorCoeff f k‖ = ‖p.coeff k‖ := by simp [p, taylorCoeff]
    _ ≤ (max M 0 * r ^ n) / r ^ k := hcoeff
    _ = max M 0 * r ^ (n - (k : ℤ)) := by
      calc
        (max M 0 * r ^ n) / r ^ k = max M 0 * (r ^ n / r ^ (k : ℤ)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
          simp [zpow_natCast]
        _ = max M 0 * r ^ (n - (k : ℤ)) := by
          rw [zpow_sub₀ hrne]

/-- Helper for Exercise 4: every Taylor coefficient whose degree is larger than the growth
exponent must vanish. -/
lemma taylor_coeff_eq_zero_of_int_lt
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M : ℝ}
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) {k : ℕ} (hk : n < (k : ℤ)) :
    taylorCoeff f k = 0 := by
  by_contra hk0
  let B : ℝ := max M 0
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_max_right M 0
  have hk_norm_pos : 0 < ‖taylorCoeff f k‖ := norm_pos_iff.mpr hk0
  obtain ⟨m, hm⟩ := exists_nat_gt (max R 2 + B / ‖taylorCoeff f k‖)
  have hm_two : (2 : ℝ) < m := by
    have hmax : (2 : ℝ) ≤ max R 2 := le_max_right R 2
    have haux : max R 2 < (m : ℝ) := by
      have hdiv_nonneg : 0 ≤ B / ‖taylorCoeff f k‖ := by positivity
      linarith
    linarith
  have hm_one : (1 : ℝ) < m := by linarith
  have hm_pos : 0 < (m : ℝ) := by linarith
  have hR : R ≤ (m : ℝ) := by
    have hmax : R ≤ max R 2 := le_max_left R 2
    have haux : max R 2 < (m : ℝ) := by
      have hdiv_nonneg : 0 ≤ B / ‖taylorCoeff f k‖ := by positivity
      linarith
    linarith
  have hcoeff :=
    taylor_coeff_norm_le_of_exterior_growth hf (n := n) (R := R) (M := M) hm_pos hR hbound k
  have hsub : n - (k : ℤ) ≤ (-1 : ℤ) := by linarith
  have hpow :
      (m : ℝ) ^ (n - (k : ℤ)) ≤ (m : ℝ) ^ (-1 : ℤ) := by
    exact (zpow_le_zpow_iff_right₀ hm_one).2 hsub
  have hnorm_le : ‖taylorCoeff f k‖ ≤ B / (m : ℝ) := by
    calc
      ‖taylorCoeff f k‖ ≤ B * (m : ℝ) ^ (n - (k : ℤ)) := by simpa [B] using hcoeff
      _ ≤ B * (m : ℝ) ^ (-1 : ℤ) := mul_le_mul_of_nonneg_left hpow hB_nonneg
      _ = B / (m : ℝ) := by simp [B, div_eq_mul_inv]
  have hdiv_lt_m : B / ‖taylorCoeff f k‖ < (m : ℝ) := by
    have hmax_nonneg : 0 ≤ max R 2 := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right R 2)
    linarith
  have hmul_lt : B < ‖taylorCoeff f k‖ * (m : ℝ) := by
    have := (div_lt_iff₀ hk_norm_pos).mp hdiv_lt_m
    simpa [mul_comm] using this
  have hnorm_lt : B / (m : ℝ) < ‖taylorCoeff f k‖ := by
    exact (div_lt_iff₀ hm_pos).2 hmul_lt
  exact (not_lt_of_ge hnorm_le) hnorm_lt

/-- Helper for Exercise 4: evaluating the finite monomial sum gives the corresponding scalar
finite sum. -/
lemma polynomial_eval_monomial_range (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    Polynomial.eval z
      (Finset.sum (Finset.range N) fun m : ℕ ↦ Polynomial.monomial m (c m)) =
      Finset.sum (Finset.range N) fun m : ℕ ↦ c m * z ^ m := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Polynomial.eval_add]
      simp [Finset.sum_range_succ, ih, add_comm]

/-- Helper for Exercise 4: once the scalar Taylor coefficients vanish above `N`, the remaining
scalar series is exactly the evaluation of the finite monomial sum polynomial. -/
lemma scalar_tsum_eq_polynomial_eval_of_eventually_zero
    {c : ℕ → ℂ} {N : ℕ} (hc : ∀ m > N, c m = 0) (z : ℂ) :
    ∑' m : ℕ, c m * z ^ m =
      Polynomial.eval z
        (Finset.sum (Finset.range (N + 1)) fun m : ℕ ↦ Polynomial.monomial m (c m)) := by
  have hzero :
      ∀ m ∉ Finset.range (N + 1), c m * z ^ m = 0 := by
    intro m hm
    have hm' : N < m := by
      exact Nat.lt_of_not_ge fun hge ↦ hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hge))
    simp [hc m hm']
  rw [tsum_eq_sum (s := Finset.range (N + 1)) hzero]
  -- Rewrite the finite Taylor sum termwise as polynomial evaluation.
  exact (polynomial_eval_monomial_range c (N + 1) z).symm

/-- Exercise 4: an entire function on `ℂ` with growth bounded by `M * ‖z‖ ^ n` outside some
radius, where `n : ℤ` acts by integer power, agrees with a complex polynomial supported in degrees
at most `n`. -/
theorem exists_polynomial_of_entire_norm_le_mul_zpow
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n : ℤ} {R M : ℝ}
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ n) :
    ∃ p : Polynomial ℂ, (∀ z : ℂ, f z = p.eval z) ∧ ∀ m ∈ p.support, (m : ℤ) ≤ n := by
  let c : ℕ → ℂ := taylorCoeff f
  have hc : ∀ m : ℕ, n < (m : ℤ) → c m = 0 := by
    intro m hm
    exact taylor_coeff_eq_zero_of_int_lt hf hbound hm
  by_cases hn : 0 ≤ n
  · let N : ℕ := Int.toNat n
    let p : Polynomial ℂ :=
      Finset.sum (Finset.range (N + 1)) fun m : ℕ ↦ Polynomial.monomial m (c m)
    refine ⟨p, ?_, ?_⟩
    · intro z
      have hsum : HasSum (fun m : ℕ ↦ c m * z ^ m) (f z) := by
        -- The entire Taylor expansion at `0` gives the global series representation.
        simpa [c, taylorCoeff, sub_zero, smul_eq_mul, div_eq_mul_inv,
          mul_comm, mul_left_comm, mul_assoc] using
          (Complex.hasSum_taylorSeries_of_entire (f := f) hf 0 z)
      have hcollapse : ∑' m : ℕ, c m * z ^ m = p.eval z := by
        apply scalar_tsum_eq_polynomial_eval_of_eventually_zero
        intro m hm
        have hm' : ((N : ℕ) : ℤ) < (m : ℤ) := by
          exact_mod_cast hm
        exact hc m (by simpa [N, Int.toNat_of_nonneg hn] using hm')
      calc
        f z = ∑' m : ℕ, c m * z ^ m := hsum.tsum_eq.symm
        _ = p.eval z := hcollapse
    · intro m hm
      have hpdeg : p.natDegree ≤ N := by
        dsimp [p]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
        exact
          (Polynomial.natDegree_monomial_le (R := ℂ) (m := i) (a := c i)).trans
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      have hm_le : m ≤ p.natDegree := by
        exact Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hm)
      have hm_int : (m : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast hm_le.trans hpdeg
      simpa [N, Int.toNat_of_nonneg hn] using hm_int
  · have hnneg : n < 0 := lt_of_not_ge hn
    refine ⟨0, ?_, ?_⟩
    · intro z
      have hsum : HasSum (fun m : ℕ ↦ c m * z ^ m) (f z) := by
        -- The entire Taylor expansion at `0` still represents the function globally; when every
        -- coefficient vanishes, the function is forced to be identically zero.
        simpa [c, taylorCoeff, sub_zero, smul_eq_mul, div_eq_mul_inv,
          mul_comm, mul_left_comm, mul_assoc] using
          (Complex.hasSum_taylorSeries_of_entire (f := f) hf 0 z)
      have hzero : HasSum (fun m : ℕ ↦ c m * z ^ m) 0 := by
        have hfun : (fun m : ℕ ↦ c m * z ^ m) = fun _ : ℕ ↦ 0 := by
          funext m
          have hm : n < (m : ℤ) := lt_of_lt_of_le hnneg (by exact_mod_cast (Nat.zero_le m))
          simp [c, hc m hm]
        rw [hfun]
        exact hasSum_zero
      simpa using hsum.unique hzero
    · intro m hm
      simp at hm
