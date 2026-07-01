import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

-- `lean_leansearch` was unavailable in this environment; local recall was checked against
-- `Complex.hasDerivAt_GammaIntegral`, `Complex.Gamma_eq_integral`, and `Complex.GammaSeq`.

/-- Helper for Exercise 7: the tail of the real Gamma integrand on `Set.Icc a b` is uniformly
dominated by the tail with the largest exponent `b` once `R ≥ 1`. -/
lemma gamma_integral_tail_norm_le_common_tail {a b x R : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) (hR : 1 ≤ R) :
    ‖(∫ t : ℝ in 0..R, Real.exp (-t) * t ^ (x - 1)) -
        ∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1)‖ ≤
      ∫ t : ℝ in Set.Ioi R, Real.exp (-t) * t ^ (b - 1) := by
  let fx : ℝ → ℝ := fun t ↦ Real.exp (-t) * t ^ (x - 1)
  let fb : ℝ → ℝ := fun t ↦ Real.exp (-t) * t ^ (b - 1)
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hfx_int : MeasureTheory.IntegrableOn fx (Set.Ioi (0 : ℝ)) := by
    simpa [fx] using Real.GammaIntegral_convergent hx0
  have hfb_int : MeasureTheory.IntegrableOn fb (Set.Ioi (0 : ℝ)) := by
    simpa [fb] using Real.GammaIntegral_convergent hb0
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hfx_int hR0
  have hdiff :
      (∫ t : ℝ in 0..R, fx t) - ∫ t : ℝ in Set.Ioi (0 : ℝ), fx t =
        -∫ t : ℝ in Set.Ioi R, fx t := by
    linarith
  have htail_nonneg : 0 ≤ ∫ t : ℝ in Set.Ioi R, fx t := by
    -- The tail integral is nonnegative because the real Gamma integrand is nonnegative on `Ioi R`.
    apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have ht1 : 1 ≤ t := hR.trans ht.le
    have ht0 : 0 ≤ t := le_trans (by norm_num) ht1
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0 _)
  rw [hdiff, norm_neg, Real.norm_eq_abs, abs_of_nonneg htail_nonneg]
  have hfx_R : MeasureTheory.IntegrableOn fx (Set.Ioi R) := hfx_int.mono_set (Set.Ioi_subset_Ioi hR0)
  have hfb_R : MeasureTheory.IntegrableOn fb (Set.Ioi R) := hfb_int.mono_set (Set.Ioi_subset_Ioi hR0)
  -- On `Set.Ioi R`, the base is at least `1`, so increasing the exponent from `x - 1` to `b - 1`
  -- gives a pointwise upper bound.
  refine MeasureTheory.setIntegral_mono_on hfx_R hfb_R measurableSet_Ioi ?_
  intro t ht
  have ht1 : 1 ≤ t := hR.trans ht.le
  have hpow : t ^ (x - 1) ≤ t ^ (b - 1) := by
    apply Real.rpow_le_rpow_of_exponent_le ht1
    linarith [hx.2]
  exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le

/-- Helper for Exercise 7: the real Euler approximation integral is exactly `Real.GammaSeq`. -/
lemma euler_approximation_integral_eq_gammaSeq {x : ℝ} (hx : 0 < x) {n : ℕ} :
    ∫ t : ℝ in 0..(n : ℝ), (1 - t / (n : ℝ)) ^ n * t ^ (x - 1) = Real.GammaSeq x n := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- The zero-th term is the tautological initial value of `GammaSeq`.
    simp [Real.GammaSeq, hx.ne']
  · have hcomplex :
        (((∫ t : ℝ in 0..(n : ℝ), (1 - t / (n : ℝ)) ^ n * t ^ (x - 1) : ℝ) : ℝ) : ℂ) =
          ((Real.GammaSeq x n : ℝ) : ℂ) := by
      calc
        (((∫ t : ℝ in 0..(n : ℝ), (1 - t / (n : ℝ)) ^ n * t ^ (x - 1) : ℝ) : ℝ) : ℂ) =
            ∫ t : ℝ in 0..(n : ℝ), (((1 - t / (n : ℝ)) ^ n * t ^ (x - 1) : ℝ) : ℂ) := by
              simpa using
                (RCLike.intervalIntegral_ofReal (𝕜 := ℂ) (a := (0 : ℝ)) (b := (n : ℝ))
                  (f := fun t : ℝ ↦ (1 - t / (n : ℝ)) ^ n * t ^ (x - 1))).symm
        _ = ∫ t : ℝ in 0..(n : ℝ), ↑((1 - t / (n : ℝ)) ^ n) * (t : ℂ) ^ ((x : ℂ) - 1) := by
              refine intervalIntegral.integral_congr ?_
              intro t ht
              have ht0 : 0 ≤ t := by
                simpa using ht.1
              calc
                (((1 - t / (n : ℝ)) ^ n * t ^ (x - 1) : ℝ) : ℂ) =
                    (((1 - t / (n : ℝ)) ^ n : ℝ) : ℂ) * ((t ^ (x - 1) : ℝ) : ℂ) := by
                      simp [Complex.ofReal_mul]
                _ = ↑((1 - t / (n : ℝ)) ^ n) * (t : ℂ) ^ ((x : ℂ) - 1) := by
                      rw [Complex.ofReal_cpow ht0, Complex.ofReal_sub, Complex.ofReal_one]
        _ = ((Real.GammaSeq x n : ℝ) : ℂ) := by
              have hseq :
                  Complex.GammaSeq (x : ℂ) n = ((Real.GammaSeq x n : ℝ) : ℂ) := by
                simp [Real.GammaSeq, Complex.GammaSeq, Complex.ofReal_cpow]
              rw [← hseq]
              symm
              simpa using
                Complex.GammaSeq_eq_approx_Gamma_integral (s := (x : ℂ))
                  (by simpa using hx) hn
    exact_mod_cast hcomplex

/-- Helper for Exercise 7: the scalar estimate `e^{-u} ≤ 1 - u + u^2 / 2` for `u ≥ 0`. -/
lemma exp_neg_le_one_sub_add_half_sq {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ (2 : ℕ) / 2 := by
  let f : ℝ → ℝ := fun y ↦ 1 - y + y ^ (2 : ℕ) / 2 - Real.exp (-y)
  have hmono : Monotone f := by
    -- The derivative is `y - 1 + exp (-y)`, which is nonnegative by the textbook bound
    -- `1 - y ≤ exp (-y)`.
    apply monotone_of_deriv_nonneg
    · intro y
      have hsq : HasDerivAt (fun z : ℝ ↦ z ^ (2 : ℕ) / 2) y y := by
        simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_id y).pow 2).div_const (2 : ℝ))
      have hexp : HasDerivAt (fun z : ℝ ↦ Real.exp (-z)) (-Real.exp (-y)) y := by
        simpa using (Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y)
      exact ((((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add hsq).sub hexp).differentiableAt
    · intro y
      have hy : 0 ≤ y - 1 + Real.exp (-y) := by
        linarith [Real.one_sub_le_exp_neg y]
      have hsq : HasDerivAt (fun z : ℝ ↦ z ^ (2 : ℕ) / 2) y y := by
        simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_id y).pow 2).div_const (2 : ℝ))
      have hexp : HasDerivAt (fun z : ℝ ↦ Real.exp (-z)) (-Real.exp (-y)) y := by
        simpa using (Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y)
      have hderiv :
          deriv f y = y - 1 + Real.exp (-y) := by
        have hderiv_raw :
            deriv (fun z : ℝ ↦ (1 - z + z ^ (2 : ℕ) / 2) - Real.exp (-z)) y =
              0 - 1 + y - -Real.exp (-y) := by
          simpa using ((((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add hsq).sub hexp).deriv
        dsimp [f] at *
        ring_nf at hderiv_raw ⊢
        exact hderiv_raw
      simpa [hderiv] using hy
  have h0 : f 0 = 0 := by
    simp [f]
  have hfu : 0 ≤ f u := by
    simpa [h0] using hmono hu
  -- Rewriting `f u ≥ 0` gives the desired quadratic upper bound.
  have hfu' : 0 ≤ 1 - u + u ^ (2 : ℕ) / 2 - Real.exp (-u) := by
    simpa [f] using hfu
  linarith [hfu']

/-- Helper for Exercise 7: the gap between `exp (-t)` and Euler's approximation is controlled by
the textbook quadratic error term. -/
lemma euler_approximation_exp_gap_bound {n : ℕ} {t : ℝ} (hn : n ≠ 0) (ht0 : 0 ≤ t)
    (htn : t ≤ n) :
    Real.exp (-t) - (1 - t / (n : ℝ)) ^ n ≤
      Real.exp (-t) * (Real.exp 1 / (2 * (n : ℝ)) * t ^ (2 : ℕ)) := by
  let u : ℝ := t / (n : ℝ)
  let a : ℝ := Real.exp (-u)
  let b : ℝ := 1 - u
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg ht0 hnR.le
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_iff₀ hnR]
    simpa using htn
  have hba : b ≤ a := by
    simpa [a, b, u] using Real.one_sub_le_exp_neg u
  have hb0 : 0 ≤ b := by
    linarith
  have hsub : a - b ≤ u ^ (2 : ℕ) / 2 := by
    -- The scalar Taylor estimate bounds the difference `a - b`.
    rw [sub_le_iff_le_add']
    simpa [a, b, u] using exp_neg_le_one_sub_add_half_sq hu0
  have hpow_le : b ^ n ≤ a ^ n := pow_le_pow_left₀ hb0 hba n
  have hpowdiff :
      a ^ n - b ^ n ≤ (u ^ (2 : ℕ) / 2) * (n : ℝ) * a ^ (n - 1) := by
    calc
      a ^ n - b ^ n = |a ^ n - b ^ n| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hpow_le)]
      _ ≤ |a - b| * (n : ℝ) * max |a| |b| ^ (n - 1) := by
        simpa using abs_pow_sub_pow_le (a := a) (b := b) (n := n)
      _ = (a - b) * (n : ℝ) * a ^ (n - 1) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (Real.exp_pos _).le,
          abs_of_nonneg hb0, max_eq_left hba]
      _ ≤ (u ^ (2 : ℕ) / 2) * (n : ℝ) * a ^ (n - 1) := by
        gcongr
  have ht_eq : t = u * (n : ℝ) := by
    dsimp [u]
    rw [div_mul_cancel₀ _ hnR.ne']
  have ha_pow : a ^ (n - 1) ≤ Real.exp (1 - t) := by
    have hpow_a : a ^ (n - 1) = Real.exp (u - t) := by
      dsimp [a]
      rw [← Real.exp_nat_mul]
      rw [ht_eq]
      have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one]
      congr 1
      rw [hnm1, sub_eq_add_neg]
      ring
    rw [hpow_a]
    exact Real.exp_le_exp.mpr (by linarith)
  have hquad :
      (u ^ (2 : ℕ) / 2) * (n : ℝ) * a ^ (n - 1) ≤
        Real.exp (-t) * (Real.exp 1 / (2 * (n : ℝ)) * t ^ (2 : ℕ)) := by
    calc
      (u ^ (2 : ℕ) / 2) * (n : ℝ) * a ^ (n - 1) ≤
          (u ^ (2 : ℕ) / 2) * (n : ℝ) * Real.exp (1 - t) := by
            gcongr
      _ = Real.exp (-t) * (Real.exp 1 / (2 * (n : ℝ)) * t ^ (2 : ℕ)) := by
            dsimp [u]
            rw [sub_eq_add_neg, Real.exp_add]
            field_simp [hnR.ne']
  -- Replacing `a` and `b` by their definitions yields the final gap estimate.
  calc
    Real.exp (-t) - (1 - t / (n : ℝ)) ^ n = Real.exp (-(u * (n : ℝ))) - (1 - u) ^ n := by
      rw [ht_eq]
      congr 1
      dsimp [u]
      field_simp [hnR.ne']
    _ = a ^ n - b ^ n := by
      dsimp [a, b]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (u ^ (2 : ℕ) / 2) * (n : ℝ) * a ^ (n - 1) := hpowdiff
    _ ≤ Real.exp (-t) * (Real.exp 1 / (2 * (n : ℝ)) * t ^ (2 : ℕ)) := hquad

/-- Exercise 7 (1): the Euler integral for `Γ` converges uniformly on every closed interval
`Set.Icc a b` with `0 < a`; when `b < a` this is the canonical vacuous empty-set case. -/
theorem exercise_7_gamma_integral_tendsto_uniformly_on {a b : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun R x : ℝ ↦ ∫ t in 0..R, Real.exp (-t) * t ^ (x - 1))
      (fun x : ℝ ↦ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1))
      atTop
      (Set.Icc a b) := by
  by_cases hba : b < a
  · -- When the interval is empty, uniform convergence is immediate.
    simpa [Set.Icc_eq_empty_of_lt hba] using
      (tendstoUniformlyOn_empty :
        TendstoUniformlyOn
          (fun R x : ℝ ↦ ∫ t in 0..R, Real.exp (-t) * t ^ (x - 1))
          (fun x : ℝ ↦ ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1))
          atTop
          (∅ : Set ℝ))
  · have hab : a ≤ b := le_of_not_gt hba
    have hb0 : 0 < b := lt_of_lt_of_le ha hab
    let g : ℝ → ℝ := fun t ↦ Real.exp (-t) * t ^ (b - 1)
    have htail0 : Tendsto (fun R : ℝ ↦ ∫ t : ℝ in Set.Ioi R, g t) atTop (𝓝 0) := by
      simpa [g] using
        (MeasureTheory.tendsto_integral_Ioi_zero (f := g) (μ := MeasureTheory.volume) tendsto_id)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htail : ∀ᶠ R in atTop, dist (∫ t : ℝ in Set.Ioi R, g t) 0 < ε := by
      exact htail0.eventually (Metric.ball_mem_nhds 0 hε)
    -- The common tail bound turns convergence of one scalar tail integral into uniform convergence.
    filter_upwards [htail, Filter.eventually_ge_atTop (1 : ℝ)] with R htailR hR x hx
    have hbound := gamma_integral_tail_norm_le_common_tail ha hab hx hR
    have htail_nonneg : 0 ≤ ∫ t : ℝ in Set.Ioi R, g t := by
      apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      intro t ht
      have ht1 : 1 ≤ t := hR.trans ht.le
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_trans (by norm_num) ht1) _)
    rw [dist_eq_norm]
    have hbound' :
        ‖(∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1)) -
            ∫ t : ℝ in 0..R, Real.exp (-t) * t ^ (x - 1)‖ ≤
          ∫ t : ℝ in Set.Ioi R, g t := by
      simpa [g, norm_sub_rev] using hbound
    exact lt_of_le_of_lt hbound' <| by
      simpa [g, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg htail_nonneg] using htailR

/-- Exercise 7 (2): the source's holomorphic function `G(z)` on `re z > 0` is mathlib's
`Complex.GammaIntegral`. -/
theorem exercise_7_gamma_integral_differentiable_on :
    DifferentiableOn ℂ Complex.GammaIntegral {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (Complex.hasDerivAt_GammaIntegral hz).differentiableAt.differentiableWithinAt

/-- Exercise 7 (3): Euler's finite-`n` approximation integral equals the explicit rational
expression from the text. -/
theorem exercise_7_euler_approximation_integral_eq {x : ℝ} (hx : 0 < x) {n : ℕ} :
    ∫ t : ℝ in 0..(n : ℝ), (1 - t / (n : ℝ)) ^ n * t ^ (x - 1) =
      (n : ℝ) ^ x * (Nat.factorial n : ℝ) /
        Finset.prod (Finset.range (n + 1)) (fun j ↦ x + (j : ℝ)) := by
  -- First identify the integral with `Real.GammaSeq`, then unfold that definition.
  simpa [Real.GammaSeq] using euler_approximation_integral_eq_gammaSeq hx (n := n)

/-- Exercise 7 (4): the lower bound in the Euler approximation estimate on `[0, n]`. -/
theorem exercise_7_euler_approximation_lower_bound {n : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (htn : t ≤ n) :
    Real.exp (-t) * (1 - Real.exp 1 / (2 * (n : ℝ)) * t ^ (2 : ℕ)) ≤
      (1 - t / (n : ℝ)) ^ n := by
  by_cases hn : n = 0
  · subst hn
    have ht : t = 0 := le_antisymm (by simpa using htn) ht0
    subst ht
    norm_num
  · -- Rearranging the gap estimate gives the desired lower bound.
    have hgap := euler_approximation_exp_gap_bound hn ht0 htn
    linarith

/-- Exercise 7 (5): the upper bound in the Euler approximation estimate on `[0, n]`. -/
theorem exercise_7_euler_approximation_upper_bound {n : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (htn : t ≤ n) :
    (1 - t / (n : ℝ)) ^ n ≤ Real.exp (-t) := by
  -- This is exactly the standard exponential bound already in mathlib.
  simpa using Real.one_sub_div_pow_le_exp_neg (n := n) (t := t) htn

/-- Exercise 7 (6): Euler's finite-`n` approximation integrals converge to the defining real
Gamma integral for every `x > 0`. -/
theorem exercise_7_euler_approximation_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun n : ℕ ↦ ∫ t : ℝ in 0..(n : ℝ), (1 - t / (n : ℝ)) ^ n * t ^ (x - 1))
      atTop
      (𝓝 <| ∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1)) := by
  -- Rewrite the whole sequence as `Real.GammaSeq` and use Euler's limit formula.
  have hseq :
      (fun n : ℕ ↦ ∫ t : ℝ in 0..(n : ℝ), (1 - t / (n : ℝ)) ^ n * t ^ (x - 1)) =
        Real.GammaSeq x := by
    funext n
    exact euler_approximation_integral_eq_gammaSeq hx (n := n)
  rw [hseq]
  simpa [Real.Gamma_eq_integral hx] using Real.GammaSeq_tendsto_Gamma x

/- Exercise 7 (7): on the half-plane `re z > 0`, the source's `G(z)` agrees with mathlib's
Gamma function. -/
#check Complex.Gamma_eq_integral
