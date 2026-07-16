import Mathlib
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_01
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_02
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_03
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_04
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_05
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_07
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_08
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_10
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_12
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_13
import stacks_proof.stacks_project.Chap09.PiTranscendence.PI_14

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped Nat

/-- Chap09 PiTranscendence/PI 18: if `α ∈ ℂ` is algebraic over `ℚ` and `α ≠ 0`, then
`Complex.exp α ≠ -1`.

This is the weak Lindemann theorem. The proof is the classical Hermite/Niven argument:
assuming `exp α = -1`, the integer-polynomial annihilator of `α` (PI-01) and the enumeration of
its roots (PI-02) make `∏ (1 + exp (a i)) = 0` (PI-03); expanding over subsets (PI-04) and
splitting off zero subset sums (PI-05) yields a relation `(C : ℂ) + ∑ exp (β j) = 0` with `C ≠ 0`.
The `β j` are roots of a fixed integer polynomial (PI-07); after dividing out the `X`-factor we get
`q` with `q.eval 0 ≠ 0` whose complex roots include all `β j`, so the analytic Hermite–Lindemann
estimate `LindemannWeierstrass.exp_polynomial_approx` applies. Summing the pointwise estimates
(PI-09/PI-10), clearing denominators by a power of the leading coefficient (PI-08), and choosing a
large prime that makes the whole analytic bound `< 1` while dividing neither `C` nor the
denominator (PI-13) produces a nonzero integer `Z_p` (PI-12) of complex norm `< 1` (analytic) yet
`≥ 1` (PI-14), a contradiction. -/
theorem complex_exp_ne_neg_one_of_isAlgebraic_rat_of_ne_zero {α : ℂ}
    (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0) : Complex.exp α ≠ -1 := by
  classical
  intro hExp
  -- Step 1: a nonzero integer polynomial `P` annihilating `α`.
  obtain ⟨P, hP0, hPα⟩ := exists_nonzero_int_polynomial_aeval_eq_zero_of_isAlgebraic_rat hα
  -- Step 2: enumerate the complex roots of `P`, and locate `α`.
  obtain ⟨n, a, ha⟩ := exists_complex_root_fin_enumeration P
  obtain ⟨i₀, hi₀⟩ := exists_index_of_aeval_eq_zero_of_complex_root_fin_enumeration hP0 ha hPα
  have ha_i₀_ne_zero : a i₀ ≠ 0 := by
    rwa [hi₀]
  -- Step 3: the product `∏ (1 + exp (a i))` vanishes.
  have hprod : ∏ i, (1 + Complex.exp (a i)) = 0 := by
    refine prod_one_add_exp_eq_zero_of_exists_exp_eq_neg_one a ⟨i₀, ?_⟩
    rw [hi₀]; exact hExp
  -- Step 4: expand the product as a powerset sum of exponentials of subset sums.
  have hpow :
      (((Finset.univ : Finset (Fin n)).powerset).sum (fun S ↦ Complex.exp (S.sum a))) = 0 := by
    rw [← prod_one_add_exp_eq_sum_powerset_exp_sum n a]; exact hprod
  -- Step 5: split off the zero subset sums.
  obtain ⟨C, m, β, e, hCval, hC0, hβval, hβ0, hrel⟩ :=
    exists_integer_and_nonzero_subset_sum_family_of_sum_powerset_exp_eq_zero a hpow
  -- Step 6: a nonzero integer polynomial `F` whose complex roots include every `β j`.
  have hβsub : ∀ j, ∃ S : Finset (Fin n), β j = S.sum a := fun j => ⟨(e j).1, hβval j⟩
  obtain ⟨F, hF0, hFβ⟩ :=
    exists_nonzero_int_polynomial_aeval_eq_zero_on_subset_sum_family_of_complex_root_fin_enumeration
      hP0 ha β hβsub
  -- Step 7: divide out the `X`-factor of `F` to obtain `q` with `q.eval 0 ≠ 0`.
  obtain ⟨q, hFq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd F hF0 0
  simp only [map_zero, sub_zero] at hFq hnd
  set k : ℕ := rootMultiplicity 0 F with hk
  have hq0 : q.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero]
    intro hc0
    exact hnd (X_dvd_iff.mpr hc0)
  have hq_ne : q ≠ 0 := by
    intro hq; rw [hq, mul_zero] at hFq; exact hF0 hFq
  have hβmem : ∀ j, β j ∈ q.aroots ℂ := by
    intro j
    have hsplit : aeval (β j) F = (β j) ^ k * aeval (β j) q := by
      rw [hFq, map_mul, map_pow, aeval_X]
    have hFzero : aeval (β j) F = 0 := hFβ j
    rw [hsplit] at hFzero
    have hbk : (β j) ^ k ≠ 0 := pow_ne_zero _ (hβ0 j)
    have hqz : aeval (β j) q = 0 := by
      rcases mul_eq_zero.mp hFzero with h | h
      · exact absurd h hbk
      · exact h
    exact (Polynomial.mem_aroots).mpr ⟨hq_ne, hqz⟩
  -- Step 8: the analytic Hermite–Lindemann estimate for `q`.
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx q hq0
  -- Step 9: uniform denominator control (power of the leading coefficient of `P`).
  obtain ⟨K, hK⟩ :=
    exists_uniform_leadingCoeff_power_denominator_control_for_subset_sum_aeval ha
  -- Step 10: constants for the analytic bound.
  set D : ℕ := K * (q.natDegree + 1) with hD
  have hlc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have hlc_abs : (1 : ℝ) ≤ |(P.leadingCoeff : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hlc0
  -- Step 11: forbid the prime from dividing `C` or the leading coefficient.
  set M : Finset ℤ := {C, P.leadingCoeff} with hM
  have hMne : ∀ x ∈ M, x ≠ 0 := by
    intro x hx
    rw [hM] at hx
    rcases Finset.mem_insert.mp hx with h | h
    · subst h; exact hC0
    · rw [Finset.mem_singleton] at h; subst h; exact hlc0
  -- Step 12: choose the large prime.
  obtain ⟨p, hp_prime, hp_gt, hp_bound, hp_ndvd⟩ :=
    exists_large_prime_avoiding_finset_with_factorial_bound
      ((m : ℝ)) (|(P.leadingCoeff : ℝ)| ^ D * |c|) ((q.eval 0).natAbs) M hMne
  -- Step 13: the analytic witnesses for this prime, and the denominator integer.
  obtain ⟨N, hN_ndvd, gp, hgp_deg, hgp_approx⟩ := hc p hp_gt hp_prime
  obtain ⟨Yp, eg, hlc_pow_ne, hT_eq, heg_bound⟩ := hK gp
  set Dp : ℤ := P.leadingCoeff ^ eg with hDp
  set Zp : ℤ := Dp * C * N + (p : ℤ) * Yp with hZp
  -- Step 14: `Z_p ≠ 0` from the prime divisibility constraints.
  have hCmem : C ∈ M := by rw [hM]; exact Finset.mem_insert_self _ _
  have hlcmem : P.leadingCoeff ∈ M := by
    rw [hM]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hC_ndvd : ¬ ((p : ℤ) ∣ C) := hp_ndvd C hCmem
  have hDp_ndvd : ¬ ((p : ℤ) ∣ Dp) := by
    rw [hDp]
    exact fun hdvd =>
      hp_ndvd P.leadingCoeff hlcmem
        ((Nat.prime_iff_prime_int.mp hp_prime).dvd_of_dvd_pow hdvd)
  have hZp_ne : Zp ≠ 0 :=
    integer_candidate_with_leadingCoeff_power_denominator_z_ne_zero
      hp_prime hZp hN_ndvd hC_ndvd hDp_ndvd
  -- Step 15: lower bound from PI-14.
  have hge1 : (1 : ℝ) ≤ ‖(Zp : ℂ)‖ := norm_int_cast_complex_ge_one Zp hZp_ne
  -- Step 16: reindex the nonzero-subset-sum family by `β`.
  set ε : ℝ := c ^ p / ((p - 1)! : ℝ) with hε
  have hreindex :
      ((nonzeroSumSubsets a).sum fun S => aeval (S.sum a) gp) = ∑ j, aeval (β j) gp := by
    rw [← Finset.sum_attach (nonzeroSumSubsets a) (fun S => aeval (S.sum a) gp),
        Finset.attach_eq_univ]
    refine (Fintype.sum_equiv e (fun j => aeval (β j) gp)
      (fun x => aeval ((x : Finset (Fin n)).sum a) gp) ?_).symm
    intro j
    simp only [hβval]
  -- Step 17: pointwise approximation at each `β j`.
  have hβ_approx :
      ∀ j, ‖(N : ℂ) * Complex.exp (β j) - ((p : ℤ) : ℂ) * aeval (β j) gp‖ ≤ ε := by
    intro j
    have h := hgp_approx (hβmem j)
    rw [zsmul_eq_mul, nsmul_eq_mul] at h
    rw [Int.cast_natCast]
    exact h
  -- Step 18: sum the pointwise estimates using the relation from PI-05.
  have h10 :
      ‖(C : ℂ) * (N : ℂ) + ((p : ℤ) : ℂ) * ∑ j, aeval (β j) gp‖ ≤ (m : ℝ) * ε :=
    norm_int_mul_add_sum_aeval_le_of_exp_relation m C N (p : ℤ) β gp hrel hβ_approx
  -- Step 19: identify `Z_p` with the denominator-cleared approximated quantity.
  have hZc :
      (Zp : ℂ) = (Dp : ℂ) *
        ((C : ℂ) * (N : ℂ) + ((p : ℤ) : ℂ) * ∑ j, aeval (β j) gp) := by
    have hYc : (Yp : ℂ) = (Dp : ℂ) * ∑ j, aeval (β j) gp := by
      rw [hDp, ← hreindex, ← hT_eq]
      push_cast
      ring
    rw [hZp]
    push_cast
    rw [hYc]
    ring
  have hZnorm : ‖(Zp : ℂ)‖ ≤ ‖(Dp : ℂ)‖ * ((m : ℝ) * ε) := by
    rw [hZc, norm_mul]
    exact mul_le_mul_of_nonneg_left h10 (norm_nonneg _)
  have hDp_norm : ‖(Dp : ℂ)‖ = |(P.leadingCoeff : ℝ)| ^ eg := by
    rw [Complex.norm_intCast, hDp]
    push_cast
    rw [abs_pow]
  -- Step 20: the analytic upper bound `< 1`.
  have hpfac_pos : (0 : ℝ) < ((p - 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos (p - 1)
  have heg : eg ≤ D * p := by
    have h1 : gp.natDegree ≤ p * q.natDegree := hgp_deg.trans (Nat.sub_le _ _)
    have hp1 : 1 ≤ p := hp_prime.one_lt.le
    have h5 : gp.natDegree + 1 ≤ p * (q.natDegree + 1) := by
      calc gp.natDegree + 1
          ≤ p * q.natDegree + 1 := Nat.add_le_add_right h1 1
        _ ≤ p * q.natDegree + p := Nat.add_le_add_left hp1 _
        _ = p * (q.natDegree + 1) := by ring
    calc eg
        ≤ K * (gp.natDegree + 1) := heg_bound
      _ ≤ K * (p * (q.natDegree + 1)) := Nat.mul_le_mul (le_refl K) h5
      _ = D * p := by rw [hD]; ring
  have hcp_le : c ^ p ≤ |c| ^ p := (le_abs_self (c ^ p)).trans_eq (abs_pow c p)
  have hbase :
      |(P.leadingCoeff : ℝ)| ^ eg * c ^ p ≤
        |(P.leadingCoeff : ℝ)| ^ (D * p) * |c| ^ p := by
    calc |(P.leadingCoeff : ℝ)| ^ eg * c ^ p
        ≤ |(P.leadingCoeff : ℝ)| ^ eg * |c| ^ p :=
          mul_le_mul_of_nonneg_left hcp_le (pow_nonneg (abs_nonneg _) eg)
      _ ≤ |(P.leadingCoeff : ℝ)| ^ (D * p) * |c| ^ p :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlc_abs heg)
            (pow_nonneg (abs_nonneg _) p)
  have hbound2 : |(P.leadingCoeff : ℝ)| ^ eg * ((m : ℝ) * ε) < 1 := by
    have hnum :
        (m : ℝ) * (|(P.leadingCoeff : ℝ)| ^ eg * c ^ p) ≤
          (m : ℝ) * (|(P.leadingCoeff : ℝ)| ^ (D * p) * |c| ^ p) :=
      mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg m)
    calc |(P.leadingCoeff : ℝ)| ^ eg * ((m : ℝ) * ε)
        = ((m : ℝ) * (|(P.leadingCoeff : ℝ)| ^ eg * c ^ p)) * (((p - 1)! : ℝ)⁻¹) := by
          rw [hε]; ring
      _ ≤ ((m : ℝ) * (|(P.leadingCoeff : ℝ)| ^ (D * p) * |c| ^ p)) * (((p - 1)! : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hpfac_pos.le)
      _ = (m : ℝ) * (|(P.leadingCoeff : ℝ)| ^ D * |c|) ^ p / ((p - 1)! : ℝ) := by
          rw [mul_pow, ← pow_mul]; ring
      _ < 1 := hp_bound
  have hkey : ‖(Zp : ℂ)‖ < 1 := by
    have hZ2 : ‖(Zp : ℂ)‖ ≤ |(P.leadingCoeff : ℝ)| ^ eg * ((m : ℝ) * ε) := by
      rw [← hDp_norm]; exact hZnorm
    exact lt_of_le_of_lt hZ2 hbound2
  exact absurd hge1 (not_le.mpr hkey)
