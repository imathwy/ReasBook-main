import Mathlib
import StacksProject_2024.Chap09.Definition_9_26_1
import StacksProject_2024.Chap09.PiTranscendence.PI_02
import StacksProject_2024.Chap09.PiTranscendence.PI_04
import StacksProject_2024.Chap09.PiTranscendence.PI_07
import StacksProject_2024.Chap09.PiTranscendence.PI_10
import StacksProject_2024.Chap09.PiTranscendence.PI_12
import StacksProject_2024.Chap09.PiTranscendence.PI_13
import StacksProject_2024.Chap09.PiTranscendence.PI_14
import StacksProject_2024.Chap09.PiTranscendence.PI_15

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField
open IntermediateField.AdjoinSimple
open scoped RatFunc

/- Domain-style sampling for Example 9.26.2:
- primary domain: simple transcendental field extensions;
- sampled owner declarations:
  `IsPurelyTranscendental`,
  `isPurelyTranscendental_adjoin_simple_of_transcendental`,
  `RatFunc.algEquivOfTranscendental`,
  `transcendental_algebraMap_iff`;
- best owner abstraction: the chapter owner `IsPurelyTranscendental`;
- primitive data: transcendence of `π` over `ℚ`;
- derived API: pure transcendence of `ℚ⟮π⟯` via the upstream simple-extension owner theorem, and
  the resulting rational-function equivalence via `RatFunc.algEquivOfTranscendental`.
-/

/-- Helper for Example 9.26.2: real transcendence over `ℤ` base-changes to transcendence over
`ℚ`. -/
lemma real_transcendental_rat_of_int {x : ℝ} (hx : Transcendental ℤ x) :
    Transcendental ℚ x := by
  -- The only bridge is that `ℚ` is algebraic over `ℤ` because it is a localization.
  letI : Algebra.IsAlgebraic ℤ ℚ :=
    IsLocalization.isAlgebraic (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  -- Algebraic extension of scalars preserves transcendence of the same real element.
  exact hx.extendScalars ℚ

/-- Helper for Example 9.26.2: if `π` is algebraic, then the complex number `2πi` is
algebraic. -/
lemma two_mul_pi_mul_I_isAlgebraic_of_real_pi (hpi : IsAlgebraic ℚ Real.pi) :
    IsAlgebraic ℚ ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  -- The real-to-complex coercion is the algebra map, so algebraicity of `π` transports to `ℂ`.
  have hpiC : IsAlgebraic ℚ ((Real.pi : ℂ)) := by
    exact hpi.algebraMap
  -- Algebraic elements are closed under products, including rational constants and the imported
  -- `PI-15` algebraicity statement for `I`.
  exact ((isAlgebraic_rat ℚ (2 : ℚ)).mul hpiC).mul complex_I_isAlgebraic_over_rat

/-- Helper for Example 9.26.2: a nonzero algebraic complex number has a rational polynomial root
certificate with nonzero constant coefficient. -/
lemma exists_ratPolynomial_root_with_nonzero_constant_of_isAlgebraic_ne_zero {z : ℂ}
    (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) :
    ∃ f : Polynomial ℚ, f ≠ 0 ∧ f.coeff 0 ≠ 0 ∧ z ∈ f.aroots ℂ := by
  -- Remove possible zero-root factors from an algebraic witness to make the constant term nonzero.
  obtain ⟨f, hf0, hfz⟩ := hz.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_of_ne_zero hz0)
  have hf_ne : f ≠ 0 := by
    intro hf
    apply hf0
    simp [hf]
  -- The same witness is then exactly a root certificate in the `aroots` API.
  refine ⟨f, hf_ne, hf0, ?_⟩
  exact Polynomial.mem_aroots.mpr ⟨hf_ne, hfz⟩

/-- Helper for Example 9.26.2: clear denominators in the rational root certificate for a nonzero
algebraic complex number. -/
lemma exists_intPolynomial_root_of_isAlgebraic_ne_zero {z : ℂ}
    (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) :
    ∃ f : Polynomial ℤ, f ≠ 0 ∧ f.eval 0 ≠ 0 ∧ z ∈ f.aroots ℂ := by
  -- Start from the rational polynomial with nonzero constant term and root `z`.
  obtain ⟨q, hq_ne, hq_coeff_ne, hq_root⟩ :=
    exists_ratPolynomial_root_with_nonzero_constant_of_isAlgebraic_ne_zero hz hz0
  let f : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q
  obtain ⟨b, hbM, hmap⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  have hf_ne : f ≠ 0 := by
    intro hf
    have hq_zero : q = 0 := by
      exact (IsLocalization.integerNormalization_eq_zero_iff
        (M := nonZeroDivisors ℤ) (S := ℚ)
        (le_rfl : nonZeroDivisors ℤ ≤ nonZeroDivisors ℤ) q).mp hf
    exact hq_ne hq_zero
  have hq_aeval : Polynomial.aeval z q = 0 := (Polynomial.mem_aroots.mp hq_root).2
  -- Denominator clearing preserves the root equation after mapping to `ℂ`.
  have hf_aeval : Polynomial.aeval z f = 0 := by
    simpa [f] using
      (IsLocalization.integerNormalization_aeval_eq_zero
        (M := nonZeroDivisors ℤ) (R' := ℂ) q hq_aeval)
  have hf_coeff_ne : f.coeff 0 ≠ 0 := by
    have hb_ne : (b : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hbM
    have hbQ_ne : (algebraMap ℤ ℚ (b : ℤ)) ≠ 0 := by
      exact (map_ne_zero_iff (algebraMap ℤ ℚ)
        (FaithfulSMul.algebraMap_injective ℤ ℚ)).mpr hb_ne
    have hcoeff_image :
        algebraMap ℤ ℚ (f.coeff 0) = algebraMap ℤ ℚ (b : ℤ) * q.coeff 0 := by
      simpa [f, Polynomial.coeff_map, Algebra.smul_def] using
        congrArg (fun p : Polynomial ℚ => p.coeff 0) hmap
    intro hf0
    have himage_ne : algebraMap ℤ ℚ (f.coeff 0) ≠ 0 := by
      rw [hcoeff_image]
      exact mul_ne_zero hbQ_ne hq_coeff_ne
    exact himage_ne (by simp [hf0])
  -- Convert the coefficient statement into the constant-term surface used by the analytic theorem.
  refine ⟨f, hf_ne, ?_, ?_⟩
  · simpa [Polynomial.coeff_zero_eq_eval_zero] using hf_coeff_ne
  · exact Polynomial.mem_aroots.mpr ⟨hf_ne, hf_aeval⟩

/-- Helper for Example 9.26.2: a finite set of nonzero algebraic complex numbers is covered by
one integer polynomial whose constant term is nonzero. -/
lemma exists_intPolynomial_cover_of_finset_isAlgebraic_ne_zero (s : Finset ℂ)
    (hs_alg : ∀ z ∈ s, IsAlgebraic ℚ z) (hs0 : ∀ z ∈ s, z ≠ 0) :
    ∃ f : Polynomial ℤ, f ≠ 0 ∧ f.eval 0 ≠ 0 ∧ ∀ z ∈ s, z ∈ f.aroots ℂ := by
  classical
  -- Inductively multiply the individual root certificates; product roots are detected by `aeval`.
  revert hs_alg hs0
  refine Finset.induction_on s ?_ ?_
  · intro hs_alg hs0
    refine ⟨1, by simp, by simp, ?_⟩
    simp
  · intro z s hz_not_mem ih hs_alg hs0
    obtain ⟨fz, hfz_ne, hfz0, hz_root⟩ :=
      exists_intPolynomial_root_of_isAlgebraic_ne_zero
        (hs_alg z (Finset.mem_insert_self z s))
        (hs0 z (Finset.mem_insert_self z s))
    obtain ⟨fs, hfs_ne, hfs0, hs_root⟩ := ih
      (fun w hw ↦ hs_alg w (Finset.mem_insert_of_mem hw))
      (fun w hw ↦ hs0 w (Finset.mem_insert_of_mem hw))
    refine ⟨fz * fs, mul_ne_zero hfz_ne hfs_ne, ?_, ?_⟩
    · simpa [Polynomial.eval_mul] using mul_ne_zero hfz0 hfs0
    · intro w hw
      rw [Finset.mem_insert] at hw
      have hprod_aeval : Polynomial.aeval w (fz * fs) = 0 := by
        rcases hw with rfl | hw
        · have hfz_eval : Polynomial.aeval w fz = 0 := (Polynomial.mem_aroots.mp hz_root).2
          simpa [map_mul, hfz_eval]
        · have hfs_eval : Polynomial.aeval w fs = 0 := (Polynomial.mem_aroots.mp (hs_root w hw)).2
          simpa [map_mul, hfs_eval]
      exact Polynomial.mem_aroots.mpr ⟨mul_ne_zero hfz_ne hfs_ne, hprod_aeval⟩

namespace LindemannWeierstrass

/-- Helper for Example 9.26.2: if one exponential factor is `-1`, then the product of
`1 + exp` factors is zero. -/
private lemma prod_one_add_exp_eq_zero_of_exists_exp_eq_neg_one {n : ℕ} (a : Fin n → ℂ)
    (h : ∃ i₀ : Fin n, Complex.exp (a i₀) = -1) :
    ∏ i, (1 + Complex.exp (a i)) = 0 := by
  classical
  -- A single vanishing factor kills the finite product.
  obtain ⟨i₀, hi₀⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])

/-- Helper for Example 9.26.2: reindex `aeval` over the nonzero subset-sum family selected by
Lemma PI-05. -/
private lemma sum_aeval_relationFamily_eq_nonzeroSumSubsets {n m : ℕ} {a : Fin n → ℂ}
    {β : Fin m → ℂ} (e : Fin m ≃ {S : Finset (Fin n) // S ∈ nonzeroSumSubsets a})
    (hβ : ∀ j, β j = (e j).1.sum a) (g : Polynomial ℤ) :
    ∑ j, Polynomial.aeval (β j) g =
      ∑ S ∈ nonzeroSumSubsets a, Polynomial.aeval (S.sum a) g := by
  classical
  -- First replace `β` by the subset sums it enumerates.
  calc
    (∑ j, Polynomial.aeval (β j) g) =
        ∑ j, Polynomial.aeval ((e j).1.sum a) g := by
          simp [hβ]
    _ = ∑ S : {S : Finset (Fin n) // S ∈ nonzeroSumSubsets a},
          Polynomial.aeval (S.1.sum a) g := by
          exact (Fintype.sum_equiv e
            (fun j ↦ Polynomial.aeval ((e j).1.sum a) g)
            (fun S ↦ Polynomial.aeval (S.1.sum a) g)
            (fun j ↦ rfl))
    _ = ∑ S ∈ nonzeroSumSubsets a, Polynomial.aeval (S.sum a) g := by
          symm
          rw [← Finset.sum_attach]
          simp

/-- Helper for Example 9.26.2: the complex norm of an integer power is bounded by a larger
fixed real base to any larger exponent. -/
private lemma norm_int_pow_cast_complex_le {b : ℤ} {e N : ℕ} (he : e ≤ N) :
    ‖((b ^ e : ℤ) : ℂ)‖ ≤ (max |(b : ℝ)| 1) ^ N := by
  -- Normalize the complex norm to the real absolute value of the integer power.
  calc
    ‖((b ^ e : ℤ) : ℂ)‖ = |((b : ℝ) ^ e)| := by
      simp [Complex.norm_intCast]
    _ = |(b : ℝ)| ^ e := by
      exact abs_pow (b : ℝ) e
    _ ≤ (max |(b : ℝ)| 1) ^ e := by
      exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) e
    _ ≤ (max |(b : ℝ)| 1) ^ N := by
      exact pow_le_pow_right₀ (le_max_right |(b : ℝ)| 1) he

/-- Helper for Example 9.26.2: a prime that does not divide an integer also does not divide any
power of that integer. -/
private lemma not_dvd_int_pow_of_not_dvd {p : ℕ} {b : ℤ} {e : ℕ} (hp : Nat.Prime p)
    (hb : ¬ ((p : ℤ) ∣ b)) :
    ¬ ((p : ℤ) ∣ b ^ e) := by
  -- Prime divisibility descends from a power to its base.
  intro hpow
  exact hb (Int.Prime.dvd_pow' hp hpow)

/-- Helper for Example 9.26.2: a nonzero algebraic complex number cannot have exponential
equal to `-1`. -/
theorem exp_ne_neg_one_of_isAlgebraic_ne_zero {α : ℂ} (hα : IsAlgebraic ℚ α)
    (hα0 : α ≠ 0) :
    Complex.exp α ≠ -1 := by
  intro hexp
  -- Route correction: keep the root enumeration of the original polynomial for `α`; this is the
  -- normal form required by the PI-08 denominator-clearing theorem.
  obtain ⟨P, hP, hP0, hα_root⟩ :=
    _root_.exists_intPolynomial_root_of_isAlgebraic_ne_zero hα hα0
  obtain ⟨n, a, ha⟩ := exists_complex_root_fin_enumeration P
  obtain ⟨iα, hiα⟩ :=
    exists_index_of_mem_aroots_of_complex_root_fin_enumeration ha hα_root
  -- The root `α` gives one zero factor in the expanded product.
  have hprod_zero : ∏ i, (1 + Complex.exp (a i)) = 0 :=
    prod_one_add_exp_eq_zero_of_exists_exp_eq_neg_one a ⟨iα, by simpa [hiα] using hexp⟩
  have hpowerset_zero :
      (((Finset.univ : Finset (Fin n)).powerset).sum
        (fun S ↦ Complex.exp (S.sum a)) = 0) := by
    rw [← prod_one_add_exp_eq_sum_powerset_exp_sum n a]
    exact hprod_zero
  -- PI-05 splits the zero subset sums into a nonzero integer constant and enumerates the
  -- remaining nonzero subset sums.
  obtain ⟨C, m, β, e, hC_def, hC_ne, hβ_eq, hβ_ne, hrelation⟩ :=
    exists_integer_and_nonzero_subset_sum_family_of_sum_powerset_exp_eq_zero a hpowerset_zero
  have hβ_alg : ∀ z ∈ (Finset.univ.image β), IsAlgebraic ℚ z := by
    intro z hz
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hz
    -- Each `β j` is a subset sum of roots of `P`, hence algebraic over `ℚ`.
    rw [hβ_eq j]
    exact subset_sum_isAlgebraic_rat_of_complex_root_fin_enumeration hP ha (e j).1
  have hβ_nonzero : ∀ z ∈ (Finset.univ.image β), z ≠ 0 := by
    intro z hz
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hz
    exact hβ_ne j
  -- Cover all nonzero subset sums by one integer polynomial with nonzero constant term.
  obtain ⟨F, hF_ne, hF0, hF_roots⟩ :=
    _root_.exists_intPolynomial_cover_of_finset_isAlgebraic_ne_zero
      (Finset.univ.image β) hβ_alg hβ_nonzero
  obtain ⟨c, happrox⟩ := exp_polynomial_approx F hF0
  obtain ⟨K, hden⟩ :=
    exists_uniform_leadingCoeff_power_denominator_control_for_subset_sum_aeval ha
  let baseC : ℝ := max |c| 1
  let baseLC : ℝ := max |(P.leadingCoeff : ℝ)| 1
  let B : ℝ := baseC * baseLC ^ (K * (F.natDegree + 1))
  let avoid : Finset ℤ := {C, P.leadingCoeff}
  have hLC_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have avoid_nonzero : ∀ z ∈ avoid, z ≠ 0 := by
    intro z hz
    have hz_cases : z = C ∨ z = P.leadingCoeff := by
      simpa [avoid] using hz
    rcases hz_cases with rfl | rfl
    · exact hC_ne
    · exact hLC_ne
  -- Pick one prime large enough for the analytic estimate and avoiding the integer obstructions.
  obtain ⟨p, hp_prime, hp_large, hp_small, hp_avoid⟩ :=
    exists_large_prime_avoiding_finset_with_factorial_bound
      (m : ℝ) B (F.eval 0).natAbs avoid avoid_nonzero
  have hpF : (F.eval 0).natAbs < p := hp_large
  have hpC : ¬ ((p : ℤ) ∣ C) := hp_avoid C (by simp [avoid])
  have hpLC : ¬ ((p : ℤ) ∣ P.leadingCoeff) :=
    hp_avoid P.leadingCoeff (by simp [avoid])
  -- The analytic approximation theorem supplies the prime-indexed polynomial `gp`.
  obtain ⟨n_p, hn_p, gp, hgp_degree, hgp_approx⟩ := happrox p hpF hp_prime
  obtain ⟨Y_p, e_p, hD_ne, hY_p, he_p⟩ := hden gp
  let T : ℂ := ∑ S ∈ nonzeroSumSubsets a, Polynomial.aeval (S.sum a) gp
  let D_p : ℤ := P.leadingCoeff ^ e_p
  let Z_p : ℤ := D_p * C * n_p + (p : ℤ) * Y_p
  have hfactorial_pos : 0 < (((p - 1).factorial : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hc_pow_le : c ^ p ≤ |c| ^ p := by
    rw [← abs_pow]
    exact le_abs_self (c ^ p)
  have hc_div_le : c ^ p / (((p - 1).factorial : ℕ) : ℝ) ≤
      |c| ^ p / (((p - 1).factorial : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hc_pow_le (le_of_lt hfactorial_pos)
  have hβ_bound :
      ∀ j,
        ‖(n_p : ℂ) * Complex.exp (β j) -
            ((p : ℤ) : ℂ) * Polynomial.aeval (β j) gp‖ ≤
          |c| ^ p / (((p - 1).factorial : ℕ) : ℝ) := by
    intro j
    have hβ_mem : β j ∈ Finset.univ.image β :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    have hraw := hgp_approx (hF_roots (β j) hβ_mem)
    have hraw' :
        ‖(n_p : ℂ) * Complex.exp (β j) -
            ((p : ℤ) : ℂ) * Polynomial.aeval (β j) gp‖ ≤
          c ^ p / (((p - 1).factorial : ℕ) : ℝ) := by
      simpa [zsmul_eq_mul, nsmul_eq_mul] using hraw
    exact hraw'.trans hc_div_le
  have hsum_transport :
      ∑ j, Polynomial.aeval (β j) gp = T := by
    simpa [T] using sum_aeval_relationFamily_eq_nonzeroSumSubsets e hβ_eq gp
  have hrelation_norm :
      ‖(C : ℂ) * (n_p : ℂ) + ((p : ℤ) : ℂ) * T‖ ≤
        (m : ℝ) * (|c| ^ p / (((p - 1).factorial : ℕ) : ℝ)) := by
    have hpi10 :=
      norm_int_mul_add_sum_aeval_le_of_exp_relation
        m C n_p (p : ℤ) β gp hrelation hβ_bound
    simpa [hsum_transport] using hpi10
  have hD_not_dvd : ¬ ((p : ℤ) ∣ D_p) := by
    -- The selected prime avoids `P.leadingCoeff`, hence also its chosen denominator power.
    simpa [D_p] using not_dvd_int_pow_of_not_dvd hp_prime hpLC
  have hZ_ne : Z_p ≠ 0 :=
    integer_candidate_with_leadingCoeff_power_denominator_z_ne_zero
      hp_prime (by rfl) hn_p hpC hD_not_dvd
  have hY_cast : (Y_p : ℂ) = (D_p : ℂ) * T := by
    simpa [D_p, T] using hY_p.symm
  have hZ_cast :
      (Z_p : ℂ) =
        (D_p : ℂ) *
          ((C : ℂ) * (n_p : ℂ) + ((p : ℤ) : ℂ) * T) := by
    calc
      (Z_p : ℂ) = ((D_p * C * n_p + (p : ℤ) * Y_p : ℤ) : ℂ) := by
        simp [Z_p]
      _ = (D_p : ℂ) * (C : ℂ) * (n_p : ℂ) + ((p : ℤ) : ℂ) * (Y_p : ℂ) := by
        push_cast
        ring
      _ = (D_p : ℂ) * (C : ℂ) * (n_p : ℂ) +
          ((p : ℤ) : ℂ) * ((D_p : ℂ) * T) := by
        rw [hY_cast]
      _ = (D_p : ℂ) *
          ((C : ℂ) * (n_p : ℂ) + ((p : ℤ) : ℂ) * T) := by
        ring
  have hgp_degree_bound : gp.natDegree + 1 ≤ p * (F.natDegree + 1) := by
    have hle_degree : gp.natDegree ≤ p * F.natDegree :=
      hgp_degree.trans (Nat.sub_le _ _)
    calc
      gp.natDegree + 1 ≤ p * F.natDegree + 1 := Nat.succ_le_succ hle_degree
      _ ≤ p * F.natDegree + p := Nat.add_le_add_left hp_prime.one_le _
      _ = p * (F.natDegree + 1) := by
        rw [Nat.mul_succ]
  have he_bound : e_p ≤ p * (K * (F.natDegree + 1)) := by
    calc
      e_p ≤ K * (gp.natDegree + 1) := he_p
      _ ≤ K * (p * (F.natDegree + 1)) :=
        Nat.mul_le_mul_left K hgp_degree_bound
      _ = p * (K * (F.natDegree + 1)) := by
        ring
  have hD_norm_bound :
      ‖(D_p : ℂ)‖ ≤ (baseLC ^ (K * (F.natDegree + 1))) ^ p := by
    have hpow :=
      norm_int_pow_cast_complex_le
        (b := P.leadingCoeff) (e := e_p) (N := p * (K * (F.natDegree + 1))) he_bound
    have hpow' : ‖(D_p : ℂ)‖ ≤ baseLC ^ (p * (K * (F.natDegree + 1))) := by
      simpa [D_p, baseLC] using hpow
    have hpow_eq :
        baseLC ^ (p * (K * (F.natDegree + 1))) =
          (baseLC ^ (K * (F.natDegree + 1))) ^ p := by
      rw [Nat.mul_comm p (K * (F.natDegree + 1)), pow_mul]
    exact hpow'.trans_eq hpow_eq
  have hc_base_bound : |c| ^ p ≤ baseC ^ p := by
    exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left |c| 1) p
  have hbaseLC_nonneg : 0 ≤ baseLC := by
    positivity
  have hmul_bound : ‖(D_p : ℂ)‖ * |c| ^ p ≤ B ^ p := by
    calc
      ‖(D_p : ℂ)‖ * |c| ^ p ≤
          (baseLC ^ (K * (F.natDegree + 1))) ^ p * baseC ^ p := by
            exact mul_le_mul hD_norm_bound hc_base_bound (pow_nonneg (abs_nonneg c) p)
              (pow_nonneg (pow_nonneg hbaseLC_nonneg _) p)
      _ = B ^ p := by
        change
          (baseLC ^ (K * (F.natDegree + 1))) ^ p * baseC ^ p =
            (baseC * baseLC ^ (K * (F.natDegree + 1))) ^ p
        rw [mul_pow, mul_comm]
  have hZ_norm_lt_one : ‖(Z_p : ℂ)‖ < 1 := by
    have hZ_norm_le : ‖(Z_p : ℂ)‖ ≤
        (m : ℝ) * B ^ p / (((p - 1).factorial : ℕ) : ℝ) := by
      calc
        ‖(Z_p : ℂ)‖ =
            ‖(D_p : ℂ) *
              ((C : ℂ) * (n_p : ℂ) + ((p : ℤ) : ℂ) * T)‖ := by
              rw [hZ_cast]
        _ = ‖(D_p : ℂ)‖ *
            ‖(C : ℂ) * (n_p : ℂ) + ((p : ℤ) : ℂ) * T‖ := by
              rw [norm_mul]
        _ ≤ ‖(D_p : ℂ)‖ *
            ((m : ℝ) * (|c| ^ p / (((p - 1).factorial : ℕ) : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hrelation_norm (norm_nonneg _)
        _ = (m : ℝ) * (‖(D_p : ℂ)‖ * |c| ^ p) /
            (((p - 1).factorial : ℕ) : ℝ) := by
              ring
        _ ≤ (m : ℝ) * B ^ p / (((p - 1).factorial : ℕ) : ℝ) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hmul_bound (by positivity))
                (le_of_lt hfactorial_pos)
    exact lt_of_le_of_lt hZ_norm_le hp_small
  have hZ_norm_ge_one : ‖(Z_p : ℂ)‖ ≥ (1 : ℝ) :=
    norm_int_cast_complex_ge_one Z_p hZ_ne
  linarith

end LindemannWeierstrass

/-- Example 9.26.2: the real number `π` is transcendental over `ℚ`. -/
-- Route correction: the proof uses the source-facing `exp α ≠ -1` theorem at `α = π i`, matching
-- Euler's identity directly instead of detouring through `exp (2πi) = 1`.
@[stacks 09I8]
theorem real_pi_transcendental : Transcendental ℚ Real.pi := by
  -- It is enough to rule out algebraicity of `π`.
  rw [Transcendental]
  intro hpi
  let z : ℂ := (Real.pi : ℂ) * Complex.I
  -- Under the algebraicity assumption on `π`, the controlled complex number `πi` is algebraic.
  have hz_alg : IsAlgebraic ℚ z := by
    have hpiC : IsAlgebraic ℚ ((Real.pi : ℂ)) := hpi.algebraMap
    simpa [z] using hpiC.mul complex_I_isAlgebraic_over_rat
  -- The same complex number is nonzero because all three factors are nonzero.
  have hz_ne_zero : z ≠ 0 := by
    simp [z, Real.pi_ne_zero]
  -- Euler's identity gives `exp (πi) = -1` in exactly this normal form.
  have hz_exp : Complex.exp z = -1 := by
    simpa [z] using Complex.exp_pi_mul_I
  -- Hermite-Lindemann contradicts Euler's identity for this nonzero algebraic exponent.
  exact (LindemannWeierstrass.exp_ne_neg_one_of_isAlgebraic_ne_zero hz_alg hz_ne_zero) hz_exp

/-- Consequence of Example 9.26.2: the simple extension `ℚ(π)` is purely transcendental over
`ℚ`. -/
-- Proof sketch: since `π` is transcendental over `ℚ`, the distinguished generator of `ℚ⟮π⟯`
-- yields the canonical owner theorem for simple transcendental extensions.
theorem rat_adjoin_pi_isPurelyTranscendental :
    IsPurelyTranscendental ℚ ℚ⟮Real.pi⟯ :=
  isPurelyTranscendental_adjoin_simple_of_transcendental real_pi_transcendental

noncomputable section

section

local instance ratFuncRatAlgebra : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Helper for Example 9.26.2: the canonical rational-function-field model of `ℚ(π)`. -/
-- Route correction: `RatFunc.algEquivOfTranscendental` is structure-valued, so this helper is a
-- `def` under the polynomial-induced `ℚ`-algebra instance on `RatFunc ℚ`.
-- Proof sketch: once `π` is known transcendental, the standard `RatFunc` equivalence specializes
-- directly to the simple extension `ℚ⟮π⟯`.
noncomputable def rat_adjoin_pi_algEquiv_ratFunc :
    RatFunc ℚ ≃ₐ[ℚ] ℚ⟮Real.pi⟯ :=
  RatFunc.algEquivOfTranscendental Real.pi real_pi_transcendental

/- In particular, `ℚ(π)` is `ℚ`-isomorphic to the one-variable rational function field `ℚ(x)`;
this is the canonical specialization of `RatFunc.algEquivOfTranscendental`. -/
#check RatFunc.algEquivOfTranscendental Real.pi real_pi_transcendental

end
