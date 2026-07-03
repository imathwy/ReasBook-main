import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Order.Filter.AtTopBot.Tendsto
import DifferentialForms_Cartan_1970.V.section20.«0002_Definition_V_3_extra_2»
import DifferentialForms_Cartan_1970.V.section20.«0003_Theorem_1»
import DifferentialForms_Cartan_1970.V.section20.«0004_Theorem_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology

-- Domain sampling: this file lies in the Gamma / digamma special-functions domain.
-- Sampled owner-layer declarations:
-- * `Complex.digamma`
-- * `Real.eulerMascheroniConstant`
-- * `Summable.multipliableUniformlyOn_nat_one_add`
-- * `Real.convexOn_log_Gamma`
-- Owner abstraction: the canonical owners are mathlib's `Complex.Gamma`, `Complex.digamma`, and
-- `Real.convexOn_log_Gamma`.
-- Primitive data: the Gamma and digamma functions together with the Euler-Mascheroni constant and
-- the generic uniform infinite-product API.
-- Derived API: the Weierstrass product, digamma series identities, and convexity.
-- Layer triage: items (1)–(5) remain source-facing companion statements, while item (6) is a
-- direct core/canonical recall.

local notation "γ" => Real.eulerMascheroniConstant
local notation "W" => fun n : ℕ => fun z : ℂ =>
  (1 + z / (n + 1 : ℂ)) * Complex.exp (-z / (n + 1 : ℂ))
local notation "D" => (Set.range fun n : ℕ => -(n : ℂ))ᶜ

/-- Helper for Remark V.3-extra-5: the nonnegative integers form a closed subset of `ℂ`. -/
lemma complex_isClosed_range_natCast : IsClosed (Set.range ((↑) : ℕ → ℂ)) := by
  have hEq :
      Set.range ((↑) : ℕ → ℂ) =
        Set.range ((↑) : ℤ → ℂ) ∩ {z : ℂ | 0 ≤ z.re} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩
      constructor
      · exact ⟨(n : ℤ), by simp⟩
      · simp
    · rintro ⟨⟨m, rfl⟩, hm⟩
      have hm' : 0 ≤ m := by simpa using hm
      lift m to ℕ using hm' with n hn
      exact ⟨n, by simpa using congrArg (fun t : ℤ => (t : ℂ)) hn⟩
  rw [hEq]
  exact Complex.isClosed_range_intCast.inter (isClosed_le continuous_const Complex.continuous_re)

/-- Helper for Remark V.3-extra-5: the pole-free Weierstrass domain is the complement of the
non-positive integers. -/
lemma mem_weierstrass_domain_iff (z : ℂ) :
    z ∈ D ↔ ∀ n : ℕ, z ≠ -(n : ℂ) := by
  constructor
  · intro hz n hzn
    exact hz ⟨n, hzn.symm⟩
  · intro hz hzD
    rcases hzD with ⟨n, rfl⟩
    exact hz n rfl

/-- Helper for Remark V.3-extra-5: the complement of the non-positive integers is open. -/
lemma isOpen_weierstrass_domain : IsOpen D := by
  have hEq :
      Set.range (fun n : ℕ => -(n : ℂ)) = (fun z : ℂ => -z) ⁻¹' Set.range ((↑) : ℕ → ℂ) := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩
      simp
    · intro hz
      rcases hz with ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Neg.neg hn⟩
  have hClosed : IsClosed (Set.range fun n : ℕ => -(n : ℂ)) := by
    rw [hEq]
    exact complex_isClosed_range_natCast.preimage continuous_neg
  simpa using hClosed.isOpen_compl

/-- Helper for Remark V.3-extra-5: on the unit ball, a single Weierstrass Gamma factor differs
from `1` by a quadratic error term. -/
lemma weierstrass_gamma_factor_sub_one_norm_le (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖(1 + w) * Complex.exp (-w) - 1‖ ≤ 3 * ‖w‖ ^ (2 : ℕ) := by
  -- Split the factor into the quadratic Taylor remainder and a product of first-order errors.
  have hsplit :
      (1 + w) * Complex.exp (-w) - 1 =
        (Complex.exp (-w) - 1 + w) + w * (Complex.exp (-w) - 1) := by
    ring
  have hquad : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ (2 : ℕ) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Complex.norm_exp_sub_one_sub_id_le (x := -w) (by simpa using hw))
  have hlin : ‖Complex.exp (-w) - 1‖ ≤ 2 * ‖w‖ := by
    simpa using (Complex.norm_exp_sub_one_le (x := -w) (by simpa using hw))
  have hmul : ‖w * (Complex.exp (-w) - 1)‖ ≤ ‖w‖ * (2 * ‖w‖) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hlin (norm_nonneg _)
  calc
    ‖(1 + w) * Complex.exp (-w) - 1‖
        ≤ ‖Complex.exp (-w) - 1 + w‖ + ‖w * (Complex.exp (-w) - 1)‖ := by
          rw [hsplit]
          exact norm_add_le _ _
    _ ≤ ‖w‖ ^ (2 : ℕ) + ‖w‖ * (2 * ‖w‖) := add_le_add hquad hmul
    _ = 3 * ‖w‖ ^ (2 : ℕ) := by ring

/-- Helper for Remark V.3-extra-5: on a compact set, the Weierstrass Gamma perturbations admit an
eventual inverse-square uniform majorant. -/
lemma weierstrass_gamma_factor_sub_one_eventually_norm_le_on_compact {K : Set ℂ}
    (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∀ z ∈ K,
        ‖((1 + z / (n + 1 : ℂ)) * Complex.exp (-z / (n + 1 : ℂ))) - 1‖
          ≤ 3 * C ^ (2 : ℕ) / ((n + 1 : ℝ) ^ (2 : ℕ)) := by
  -- Compactness gives a uniform bound for `‖z‖`, which becomes a small parameter after division
  -- by `n + 1`.
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℂ ↦ z) continuousOn_id
  let C : ℝ := max R 0
  refine ⟨C, le_max_right _ _, ?_⟩
  have hC : ∀ z ∈ K, ‖z‖ ≤ C := fun z hz ↦ (hR z hz).trans (le_max_left _ _)
  filter_upwards [Filter.eventually_atTop.2 ⟨⌈C⌉₊, fun n hn ↦ hn⟩] with n hn z hz
  have hCn : C ≤ n + 1 := by
    calc
      C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
      _ ≤ n := by exact_mod_cast hn
      _ ≤ n + 1 := by linarith
  let w : ℂ := z / (n + 1 : ℂ)
  have hw_le : ‖w‖ ≤ C / (n + 1 : ℝ) := by
    calc
      ‖w‖ = ‖z‖ / (n + 1 : ℝ) := by
        calc
          ‖w‖ = ‖z‖ / ‖(n + 1 : ℂ)‖ := by simp [w]
          _ = ‖z‖ / (n + 1 : ℝ) := by
            have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
              simpa using (Complex.norm_natCast (n + 1))
            rw [hnorm]
      _ ≤ C / (n + 1 : ℝ) := by
        gcongr
        exact hC z hz
  have hw_one : ‖w‖ ≤ 1 := by
    calc
      ‖w‖ ≤ C / (n + 1 : ℝ) := hw_le
      _ ≤ 1 := by
        have hn_pos : (0 : ℝ) < n + 1 := by positivity
        have hCn' : C ≤ 1 * (n + 1 : ℝ) := by simpa using hCn
        exact (div_le_iff₀ hn_pos).2 hCn'
  calc
    ‖((1 + z / (n + 1 : ℂ)) * Complex.exp (-z / (n + 1 : ℂ))) - 1‖
        = ‖(1 + w) * Complex.exp (-w) - 1‖ := by
          simp [w, neg_div]
    _ ≤ 3 * ‖w‖ ^ (2 : ℕ) := weierstrass_gamma_factor_sub_one_norm_le w hw_one
    _ ≤ 3 * (C / (n + 1 : ℝ)) ^ (2 : ℕ) := by
      gcongr
    _ = 3 * C ^ (2 : ℕ) / ((n + 1 : ℝ) ^ (2 : ℕ)) := by
      rw [div_pow]
      ring

/-- Helper for Remark V.3-extra-5: the reciprocal of the finite Euler Gamma approximant already
matches the textbook finite Weierstrass product before inserting the harmonic correction. -/
lemma one_div_gammaSeq_eq_partial_weierstrass_prefactor (z : ℂ) (n : ℕ) :
    ((Complex.GammaSeq z (n + 1)) : ℂ)⁻¹ =
      z * (Finset.range (n + 1)).prod (fun k ↦ 1 + z / (k + 1 : ℂ)) *
        Complex.exp (-(Real.log (n + 1)) * z) := by
  have hnp1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsplit :
      ∀ k : ℕ, z + (k + 1 : ℂ) = (k + 1 : ℂ) * (1 + z / (k + 1 : ℂ)) := by
    intro k
    field_simp [show (k + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero k]
    ring
  have hfact :
      (∏ k ∈ Finset.range (n + 1), (k + 1 : ℂ)) = ((n + 1).factorial : ℂ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial (n + 1)
  have hcpow :
      ((n + 1 : ℂ) ^ z)⁻¹ = Complex.exp (-(Real.log (n + 1)) * z) := by
    rw [Complex.cpow_def_of_ne_zero hnp1]
    have hlog_nat : Complex.log (n + 1 : ℂ) = (Real.log (n + 1) : ℂ) := by
      simpa using (Complex.ofReal_log (show 0 ≤ (n + 1 : ℝ) by positivity)).symm
    rw [hlog_nat]
    simpa [Complex.exp_neg]
  have hcpow_ne : (n + 1 : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnp1]
    exact Complex.exp_ne_zero _
  -- Expand the finite product, peel off the `k = 0` factor, and then factor each
  -- remaining term into `(k + 1) * (1 + z / (k + 1))`.
  calc
    ((Complex.GammaSeq z (n + 1)) : ℂ)⁻¹
        = (∏ j ∈ Finset.range (n + 2), (z + j)) /
            (((n + 1 : ℂ) ^ z) * ((n + 1).factorial : ℂ)) := by
              simp [Complex.GammaSeq, inv_div, mul_comm, mul_left_comm, mul_assoc]
    _ = ((∏ k ∈ Finset.range (n + 1), (z + (k + 1 : ℂ))) * z) *
          ((((n + 1 : ℂ) ^ z) * ((n + 1).factorial : ℂ))⁻¹) := by
            rw [Finset.prod_range_succ']
            simp [div_eq_mul_inv, mul_assoc]
    _ = (((∏ k ∈ Finset.range (n + 1), (k + 1 : ℂ)) *
            (∏ k ∈ Finset.range (n + 1), (1 + z / (k + 1 : ℂ)))) * z) *
          ((((n + 1 : ℂ) ^ z) * ((n + 1).factorial : ℂ))⁻¹) := by
            simp_rw [hsplit]
            rw [Finset.prod_mul_distrib]
    _ = ((((n + 1).factorial : ℂ) *
            (∏ k ∈ Finset.range (n + 1), (1 + z / (k + 1 : ℂ))) * z) *
          ((((n + 1 : ℂ) ^ z) * ((n + 1).factorial : ℂ))⁻¹)) := by
            rw [hfact]
    _ = z * (Finset.range (n + 1)).prod (fun k ↦ 1 + z / (k + 1 : ℂ)) *
          ((n + 1 : ℂ) ^ z)⁻¹ := by
            field_simp [hcpow_ne, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))]
    _ = z * (Finset.range (n + 1)).prod (fun k ↦ 1 + z / (k + 1 : ℂ)) *
          Complex.exp (-(Real.log (n + 1)) * z) := by
            rw [hcpow]

/-- Helper for Remark V.3-extra-5: the textbook finite Weierstrass product is exactly the
finite reciprocal Gamma approximant after splitting off the harmonic exponential correction. -/
lemma one_div_gammaSeq_eq_weierstrass_partial (z : ℂ) (n : ℕ) :
    ((Complex.GammaSeq z (n + 1)) : ℂ)⁻¹ =
      z * (Finset.range (n + 1)).prod (fun k ↦ W k z) *
        Complex.exp ((((harmonic (n + 1) : ℚ) : ℂ) - Real.log (n + 1)) * z) := by
  have hsum_inv :
      ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℂ)⁻¹) = ((harmonic (n + 1) : ℚ) : ℂ) := by
    simp [harmonic]
  have hsum_div :
      ∑ k ∈ Finset.range (n + 1), z / (k + 1 : ℂ) = ((harmonic (n + 1) : ℚ) : ℂ) * z := by
    calc
      ∑ k ∈ Finset.range (n + 1), z / (k + 1 : ℂ)
          = ∑ k ∈ Finset.range (n + 1), z * ((k + 1 : ℂ)⁻¹) := by
              simp [div_eq_mul_inv]
      _ = z * ∑ k ∈ Finset.range (n + 1), ((k + 1 : ℂ)⁻¹) := by
            rw [← Finset.mul_sum]
      _ = ((harmonic (n + 1) : ℚ) : ℂ) * z := by
            rw [hsum_inv]
            ring
  have hprod_exp :
      (∏ k ∈ Finset.range (n + 1), Complex.exp (-z / (k + 1 : ℂ))) =
        Complex.exp (-(((harmonic (n + 1) : ℚ) : ℂ) * z)) := by
    -- Compress the finite exponential correction into the harmonic-number sum.
    rw [← Complex.exp_sum]
    congr 1
    simpa [neg_div] using congrArg Neg.neg hsum_div
  have hprod_W :
      (∏ k ∈ Finset.range (n + 1), W k z) =
        (∏ k ∈ Finset.range (n + 1), (1 + z / (k + 1 : ℂ))) *
          Complex.exp (-(((harmonic (n + 1) : ℚ) : ℂ) * z)) := by
    -- Split the finite product into the algebraic factor and the exponential factor.
    rw [Finset.prod_mul_distrib, hprod_exp]
  -- Reinsert the harmonic correction so the finite Gamma approximant matches the textbook formula.
  calc
    ((Complex.GammaSeq z (n + 1)) : ℂ)⁻¹
        = z * (∏ k ∈ Finset.range (n + 1), (1 + z / (k + 1 : ℂ))) *
            Complex.exp (-(Real.log (n + 1)) * z) :=
          one_div_gammaSeq_eq_partial_weierstrass_prefactor z n
    _ = z * (∏ k ∈ Finset.range (n + 1), W k z) *
          Complex.exp ((((harmonic (n + 1) : ℚ) : ℂ) - Real.log (n + 1)) * z) := by
            rw [hprod_W]
            have hexp :
                Complex.exp (-(((harmonic (n + 1) : ℚ) : ℂ) * z)) *
                    Complex.exp ((((harmonic (n + 1) : ℚ) : ℂ) - Real.log (n + 1)) * z) =
                  Complex.exp (-(Real.log (n + 1)) * z) := by
              rw [← Complex.exp_add]
              congr 1
              ring
            rw [← hexp]
            ring

/-- Helper for Remark V.3-extra-5: on each compact subset of the pole-free domain, a tail of the
Weierstrass factors lies in the slit plane and its logarithms admit a normal inverse-square
majorant. -/
lemma weierstrass_log_tail_on_compact {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ N : ℕ, (∀ n, Set.MapsTo (fun z ↦ W (n + N) z) K Complex.slitPlane) ∧
      NormallySummableOn (fun n z ↦ Complex.log (W (n + N) z)) K := by
  let _ := hKD
  obtain ⟨C, hC_nonneg, hbound⟩ :=
    weierstrass_gamma_factor_sub_one_eventually_norm_le_on_compact hK
  rw [Filter.eventually_atTop] at hbound
  rcases hbound with ⟨N₁, hN₁⟩
  let N₂ : ℕ := ⌈6 * C ^ (2 : ℕ)⌉₊
  let N : ℕ := max N₁ N₂
  refine ⟨N, ?_, ?_⟩
  · intro n z hz
    -- The quadratic compact bound becomes `< 1`, so the shifted factor stays in the slit plane.
    have hN₁le : N₁ ≤ n + N := le_trans (le_max_left _ _) (Nat.le_add_left _ _)
    have hfactor_bound' := hN₁ (n + N) hN₁le z hz
    have hfactor_bound :
        ‖W (n + N) z - 1‖ ≤ 3 * C ^ (2 : ℕ) / (((n + N) + 1 : ℝ) ^ (2 : ℕ)) :=
      by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hfactor_bound'
    have hN₂le : N₂ ≤ n + N := le_trans (le_max_right _ _) (Nat.le_add_left _ _)
    have hlarge : 6 * C ^ (2 : ℕ) ≤ (((n + N) + 1 : ℕ) : ℝ) := by
      calc
        6 * C ^ (2 : ℕ) ≤ (N₂ : ℝ) := by
          exact Nat.le_ceil (6 * C ^ (2 : ℕ))
        _ ≤ n + N := by exact_mod_cast hN₂le
        _ ≤ (((n + N) + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ (n + N)
    have hhalf :
        3 * C ^ (2 : ℕ) / (((n + N) + 1 : ℝ) ^ (2 : ℕ)) ≤ 1 / 2 := by
      have hlarge' : 6 * C ^ (2 : ℕ) ≤ ((n + N) + 1 : ℝ) := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hlarge
      have hbase_sq : ((n + N) + 1 : ℝ) ≤ (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
        have hone_le : (1 : ℝ) ≤ ((n + N) + 1 : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n + N))
        nlinarith
      have hsq_large : 6 * C ^ (2 : ℕ) ≤ (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
        exact le_trans hlarge' hbase_sq
      have haux :
          3 * C ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
        nlinarith
      have hden_pos : (0 : ℝ) < (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
        have hbase_pos : (0 : ℝ) < ((n + N) + 1 : ℝ) := by positivity
        nlinarith
      exact (div_le_iff₀ hden_pos).2 haux
    have hlt_one : ‖W (n + N) z - 1‖ < 1 := by
      exact lt_of_le_of_lt (hfactor_bound.trans hhalf) (by norm_num)
    simpa [sub_eq_add_neg, add_assoc] using
      Complex.mem_slitPlane_of_norm_lt_one (z := W (n + N) z - 1) hlt_one
  · -- The same inverse-square bound controls `‖log (W (n + N) z)‖` on the compact set.
    refine ⟨fun n ↦ ⟨(9 / 2) * C ^ (2 : ℕ) / (((n + N) + 1 : ℝ) ^ (2 : ℕ)), by positivity⟩, ?_, ?_⟩
    · have hsummable_inv_sq :
          Summable (fun n : ℕ ↦ ((((n + N) + 1 : ℕ) : ℝ) ^ (2 : ℕ))⁻¹) := by
        simpa [Nat.add_assoc] using
          ((summable_nat_add_iff (N + 1)).2
            (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hsummable_inv_sq.mul_left ((9 / 2) * C ^ (2 : ℕ))
    · intro n z hz
      have hN₁le : N₁ ≤ n + N := le_trans (le_max_left _ _) (Nat.le_add_left _ _)
      have hfactor_bound' := hN₁ (n + N) hN₁le z hz
      have hfactor_bound :
          ‖W (n + N) z - 1‖ ≤ 3 * C ^ (2 : ℕ) / (((n + N) + 1 : ℝ) ^ (2 : ℕ)) :=
        by
          simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hfactor_bound'
      have hN₂le : N₂ ≤ n + N := le_trans (le_max_right _ _) (Nat.le_add_left _ _)
      have hlarge : 6 * C ^ (2 : ℕ) ≤ (((n + N) + 1 : ℕ) : ℝ) := by
        calc
          6 * C ^ (2 : ℕ) ≤ (N₂ : ℝ) := by
            exact Nat.le_ceil (6 * C ^ (2 : ℕ))
          _ ≤ n + N := by exact_mod_cast hN₂le
          _ ≤ (((n + N) + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ (n + N)
      have hhalf :
          3 * C ^ (2 : ℕ) / (((n + N) + 1 : ℝ) ^ (2 : ℕ)) ≤ 1 / 2 := by
        have hlarge' : 6 * C ^ (2 : ℕ) ≤ ((n + N) + 1 : ℝ) := by
          simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hlarge
        have hbase_sq : ((n + N) + 1 : ℝ) ≤ (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
          have hone_le : (1 : ℝ) ≤ ((n + N) + 1 : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n + N))
          nlinarith
        have hsq_large : 6 * C ^ (2 : ℕ) ≤ (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
          exact le_trans hlarge' hbase_sq
        have haux :
            3 * C ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
          nlinarith
        have hden_pos : (0 : ℝ) < (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
          have hbase_pos : (0 : ℝ) < ((n + N) + 1 : ℝ) := by positivity
          nlinarith
        exact (div_le_iff₀ hden_pos).2 haux
      -- Rewrite the factor as `1 + (W - 1)` and apply the half-ball logarithm estimate.
      calc
        ‖Complex.log (W (n + N) z)‖
            = ‖Complex.log (1 + (W (n + N) z - 1))‖ := by
                congr 2
                ring
        _ ≤ (3 / 2 : ℝ) * ‖W (n + N) z - 1‖ :=
              Complex.norm_log_one_add_half_le_self (hfactor_bound.trans hhalf)
        _ ≤ (3 / 2 : ℝ) *
              (3 * C ^ (2 : ℕ) / (((n + N) + 1 : ℝ) ^ (2 : ℕ))) := by
                gcongr
        _ = (9 / 2) * C ^ (2 : ℕ) / (((n + N) + 1 : ℝ) ^ (2 : ℕ)) := by
              ring

/-- Helper for Remark V.3-extra-5: the Weierstrass Gamma factors form a compact-normally
multipliable product away from the non-positive integers. -/
lemma weierstrass_gamma_factors_normallyMultipliableOnCompacta_except_nonpos_integers :
    NormallyMultipliableOnCompacta W D := by
  -- Route correction: the missing owner datum is the fixed-compact slit/log tail for `W`, not a
  -- new generic convergence abstraction. We package that tail directly and apply the chapter iff.
  have honeadd : NormallyMultipliableOnCompacta (fun n z ↦ 1 + (W n z - 1)) D := by
    refine normallyMultipliableOnCompacta_one_add_iff.mpr ?_
    refine ⟨isOpen_weierstrass_domain, ?_, ?_⟩
    · intro n
      -- Each perturbation `W n z - 1` is continuous on the pole-free domain.
      fun_prop
    · intro K hK hKD
      simpa [sub_eq_add_neg, add_assoc] using weierstrass_log_tail_on_compact hK hKD
  simpa [sub_eq_add_neg, add_assoc] using honeadd

/-- Helper for Remark V.3-extra-5: the logarithmic derivative of one Weierstrass Gamma factor has
the expected elementary rational form. -/
lemma logDeriv_weierstrass_gamma_factor (n : ℕ) {z : ℂ}
    (hz : z ≠ -(n + 1 : ℂ)) :
    logDeriv (W n) z = 1 / (z + (n + 1 : ℂ)) - 1 / (n + 1 : ℂ) := by
  let a : ℂ := n + 1
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast Nat.succ_ne_zero n
  have hz' : z + a ≠ 0 := by
    intro h
    apply hz
    rw [eq_neg_iff_add_eq_zero]
    simpa [a] using h
  have hleft_nonzero : 1 + z / a ≠ 0 := by
    have hEq : 1 + z / a = (z + a) / a := by
      field_simp [ha]
      ring
    rw [hEq]
    exact div_ne_zero hz' ha
  have hleft_diff : DifferentiableAt ℂ (fun w : ℂ ↦ 1 + w / a) z := by
    fun_prop
  have hright_diff : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.exp (-w / a)) z := by
    fun_prop
  have hleft :
      logDeriv (fun w : ℂ ↦ 1 + w / a) z = 1 / (z + a) := by
    have hEq : (fun w : ℂ ↦ 1 + w / a) = fun w : ℂ ↦ a⁻¹ * (w + a) := by
      funext w
      field_simp [ha]
      ring
    rw [hEq, logDeriv_const_mul z a⁻¹ (inv_ne_zero ha)]
    simp [logDeriv_apply]
  have hright :
      logDeriv (fun w : ℂ ↦ Complex.exp (-w / a)) z = -1 / a := by
    rw [show (fun w : ℂ ↦ Complex.exp (-w / a)) = Complex.exp ∘ fun w : ℂ ↦ -w / a by rfl]
    rw [logDeriv_comp Complex.differentiableAt_exp (by fun_prop)]
    simp [logDeriv_apply]
  -- Split the logarithmic derivative across the product and simplify the elementary pieces.
  calc
    logDeriv (W n) z
        = logDeriv (fun w : ℂ ↦ 1 + w / a) z +
            logDeriv (fun w : ℂ ↦ Complex.exp (-w / a)) z := by
              refine logDeriv_mul z hleft_nonzero (Complex.exp_ne_zero _) hleft_diff hright_diff
    _ = 1 / (z + a) - 1 / a := by
          rw [hleft, hright]
          ring
    _ = 1 / (z + (n + 1 : ℂ)) - 1 / (n + 1 : ℂ) := by
          simp [a]

/-- Helper for Remark V.3-extra-5: at a pole-free point, the finite Weierstrass products with the
harmonic correction converge to the textbook infinite product. -/
lemma weierstrass_partial_tendsto_product_at_domain_point {z : ℂ} (hz : z ∈ D) :
      Filter.Tendsto
      (fun n : ℕ ↦
        z * (Finset.range (n + 1)).prod (fun k ↦ W k z) *
          Complex.exp ((((harmonic (n + 1) : ℚ) : ℂ) - Real.log (n + 1)) * z))
      Filter.atTop
      (𝓝 (z * Complex.exp ((γ : ℂ) * z) * ∏' k : ℕ, W k z)) := by
  have hshift : Filter.Tendsto (fun n : ℕ ↦ n + 1) Filter.atTop Filter.atTop := by
    simpa using Filter.tendsto_atTop_mono Nat.le_succ Filter.tendsto_id
  have hprod :
      Filter.Tendsto (fun n : ℕ ↦ (Finset.range (n + 1)).prod (fun k ↦ W k z))
        Filter.atTop (𝓝 (∏' k : ℕ, W k z)) := by
    -- The compact-normal product owner supplies the pointwise product limit on the pole-free domain.
    have hhasProd :
        HasProd (fun k : ℕ ↦ W k z) (∏' k : ℕ, W k z) :=
      weierstrass_gamma_factors_normallyMultipliableOnCompacta_except_nonpos_integers.hasProd hz
    have hprod_base :
        Filter.Tendsto (fun n : ℕ ↦ (Finset.range n).prod (fun k ↦ W k z))
          Filter.atTop (𝓝 (∏' k : ℕ, W k z)) :=
      hhasProd.tendsto_prod_nat
    simpa [Function.comp] using hprod_base.comp hshift
  have hharmonic_real :
      Filter.Tendsto
        (fun n : ℕ ↦ ((harmonic (n + 1) : ℚ) : ℝ) - Real.log (n + 1))
        Filter.atTop (𝓝 γ) := by
    -- This is exactly the Euler-Mascheroni convergence from the source formula.
    have hmain :
        Filter.Tendsto
          (fun n : ℕ ↦ ((harmonic n : ℚ) : ℝ) - Real.log (n + 1))
          Filter.atTop (𝓝 γ) :=
      Real.tendsto_harmonic_sub_log_add_one
    have hinv :
        Filter.Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) Filter.atTop (𝓝 0) :=
      by simpa [Nat.cast_add] using
        (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
          (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (𝓝 0))
    simpa [harmonic_succ, Rat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hmain.add hinv
  have hharmonic :
      Filter.Tendsto
        (fun n : ℕ ↦ (((harmonic (n + 1) : ℚ) : ℂ) - Real.log (n + 1)) * z)
        Filter.atTop (𝓝 ((γ : ℂ) * z)) := by
    have hcast :
        Filter.Tendsto
          (fun n : ℕ ↦ (((harmonic (n + 1) : ℚ) : ℝ) - Real.log (n + 1) : ℝ))
          Filter.atTop (𝓝 γ) := hharmonic_real
    have hcast_complex :
        Filter.Tendsto
          (fun n : ℕ ↦ ((((harmonic (n + 1) : ℚ) : ℝ) - Real.log (n + 1) : ℝ) : ℂ))
          Filter.atTop (𝓝 ((γ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hcast
    -- Multiply the scalar correction by the fixed point `z` before applying `exp`.
    simpa using hcast_complex.mul tendsto_const_nhds
  have hexp :
      Filter.Tendsto
        (fun n : ℕ ↦ Complex.exp ((((harmonic (n + 1) : ℚ) : ℂ) - Real.log (n + 1)) * z))
        Filter.atTop (𝓝 (Complex.exp ((γ : ℂ) * z))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp hharmonic
  -- Combine the product limit with the exponential correction and the front factor `z`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    tendsto_const_nhds.mul (hprod.mul hexp)

/-- Helper for Remark V.3-extra-5: at a negative successor integer, the perturbation norms
`‖W n z - 1‖` are summable. -/
lemma weierstrass_factor_sub_one_norm_summable_at_neg_succ (m : ℕ) :
    Summable (fun n : ℕ => ‖W n (-(m + 1 : ℂ)) - 1‖) := by
  let z : ℂ := -(m + 1 : ℂ)
  let f : ℕ → ℝ := fun n ↦ ‖W n z - 1‖
  obtain ⟨C, _hC_nonneg, hbound⟩ :=
    weierstrass_gamma_factor_sub_one_eventually_norm_le_on_compact
      (K := ({z} : Set ℂ)) isCompact_singleton
  rw [Filter.eventually_atTop] at hbound
  rcases hbound with ⟨N, hN⟩
  have hsummable_majorant :
      Summable (fun n : ℕ => 3 * C ^ (2 : ℕ) / (((n + N) + 1 : ℝ) ^ (2 : ℕ))) := by
    -- Shift the standard inverse-square series so it matches the eventual bound's index.
    have hsummable_inv_sq :
        Summable (fun n : ℕ => ((((n + N) + 1 : ℕ) : ℝ) ^ (2 : ℕ))⁻¹) := by
      simpa [Nat.add_assoc] using
        ((summable_nat_add_iff (N + 1)).2
          (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hsummable_inv_sq.mul_left (3 * C ^ (2 : ℕ))
  have htail : Summable (fun n : ℕ => f (n + N)) := by
    -- Compare the singleton tail directly with the inverse-square majorant.
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_ hsummable_majorant
    intro n
    have hbound_n := hN (n + N) (Nat.le_add_left N n) z (by simp [z])
    simpa [f, z, Nat.cast_add, add_assoc, add_left_comm, add_comm] using hbound_n
  -- Remove the finite prefix to recover the full summable series.
  simpa [f, z, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (summable_nat_add_iff N).1 htail

/-- Helper for Remark V.3-extra-5: after the vanishing factor, the remaining Weierstrass tail is
multipliable at the negative successor integer. -/
lemma weierstrass_tail_multipliable_at_neg_succ (m : ℕ) :
    Multipliable (fun n : ℕ => W (n + (m + 1)) (-(m + 1 : ℂ))) := by
  let z : ℂ := -(m + 1 : ℂ)
  let f : ℕ → ℂ := fun n ↦ W (n + (m + 1)) z - 1
  have hsummable :
      Summable (fun n : ℕ => ‖f n‖) := by
    -- Shift the summable perturbation series so it starts exactly at the tail index.
    simpa [f, z, Nat.add_assoc] using
      (summable_nat_add_iff (m + 1)).2
        (weierstrass_factor_sub_one_norm_summable_at_neg_succ m)
  -- Rewrite the tail as `1 + (W - 1)` and invoke the standard infinite-product criterion.
  simpa [f, z, sub_eq_add_neg, add_assoc] using
    (multipliable_one_add_of_summable (f := f) hsummable)

/-- Helper for Remark V.3-extra-5: at each negative integer `-(m + 1)`, one Weierstrass factor
vanishes, so the full infinite product vanishes as well. -/
lemma weierstrass_tprod_eq_zero_at_neg_succ (m : ℕ) :
    ∏' k : ℕ, W k (-(m + 1 : ℂ)) = 0 := by
  have htail : Multipliable (fun n : ℕ => W (n + (m + 1)) (-(m + 1 : ℂ))) :=
    weierstrass_tail_multipliable_at_neg_succ m
  have hfactor_zero : W m (-(m + 1 : ℂ)) = 0 := by
    -- The factor with index `m` contributes the explicit zero `1 - 1`.
    have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    have hm1' : ((m : ℂ) + 1) ≠ 0 := by
      simpa using hm1
    have hdiv' : ((m : ℂ) + 1) / ((m : ℂ) + 1) = (1 : ℂ) := div_self hm1'
    have hdiv : (-(m + 1 : ℂ)) / (m + 1 : ℂ) = (-1 : ℂ) := by
      rw [neg_div, hdiv']
    calc
      W m (-(m + 1 : ℂ))
          = (1 + (-(m + 1 : ℂ)) / (m + 1 : ℂ)) *
              Complex.exp (-(-(m + 1 : ℂ)) / (m + 1 : ℂ)) := by rfl
      _ = (1 + (-(m + 1 : ℂ)) / (m + 1 : ℂ)) * Complex.exp ((m + 1 : ℂ) / (m + 1 : ℂ)) := by
            simp
      _ = (1 + (-1 : ℂ)) * Complex.exp (1 : ℂ) := by rw [hdiv, hdiv']
      _ = 0 := by simp
  have hprefix_zero :
      (∏ i ∈ Finset.range (m + 1), W i (-(m + 1 : ℂ))) = 0 := by
    -- The finite prefix already vanishes because it contains the zero factor at `i = m`.
    refine Finset.prod_eq_zero (by simp) hfactor_zero
  -- Route correction: outside `D`, split the unrestricted `tprod` at the explicit zero factor.
  calc
    ∏' k : ℕ, W k (-(m + 1 : ℂ))
        = ((∏ i ∈ Finset.range (m + 1), W i (-(m + 1 : ℂ))) *
            ∏' i : ℕ, W (i + (m + 1)) (-(m + 1 : ℂ))) := by
              simpa using
                (htail.prod_mul_tprod_nat_mul' (f := fun k : ℕ => W k (-(m + 1 : ℂ)))
                  (k := m + 1)).symm
    _ = 0 := by rw [hprefix_zero, zero_mul]

/-- Helper for Remark V.3-extra-5: away from the poles, the reciprocal Gamma function agrees with
the Weierstrass product by limit identification. -/
lemma complex_gamma_reciprocal_eq_weierstrass_product_of_mem_domain {z : ℂ} (hz : z ∈ D) :
    1 / Complex.Gamma z =
      z * Complex.exp ((γ : ℂ) * z) *
        ∏' k : ℕ, ((1 + z / (k + 1 : ℂ)) * Complex.exp (-z / (k + 1 : ℂ))) := by
  have hGamma_ne : Complex.Gamma z ≠ 0 := by
    -- On the pole-free domain, Gamma stays away from `0`.
    exact Complex.Gamma_ne_zero ((mem_weierstrass_domain_iff z).1 hz)
  have hshift : Filter.Tendsto (fun n : ℕ ↦ n + 1) Filter.atTop Filter.atTop := by
    simpa using Filter.tendsto_atTop_mono Nat.le_succ Filter.tendsto_id
  have hgamma_inv :
      Filter.Tendsto (fun n : ℕ ↦ ((Complex.GammaSeq z (n + 1)) : ℂ)⁻¹)
        Filter.atTop (𝓝 (1 / Complex.Gamma z)) := by
    -- Compare the Gamma-sequence limit with the exact finite Weierstrass product identity.
    simpa [one_div] using
      ((Complex.GammaSeq_tendsto_Gamma z).comp hshift).inv₀ hGamma_ne
  have hweierstrass_partial :
      Filter.Tendsto
        (fun n : ℕ ↦
          z * (Finset.range (n + 1)).prod (fun k ↦ W k z) *
            Complex.exp ((((harmonic (n + 1) : ℚ) : ℂ) - Real.log (n + 1)) * z))
        Filter.atTop (𝓝 (1 / Complex.Gamma z)) := by
    -- Replace each finite Gamma approximant with the textbook finite Weierstrass product.
    simpa [one_div_gammaSeq_eq_weierstrass_partial] using hgamma_inv
  -- The finite expressions converge both to the Gamma limit and to the Weierstrass product.
  exact tendsto_nhds_unique hweierstrass_partial
    (weierstrass_partial_tendsto_product_at_domain_point hz)

/-- Remark V.3-extra-5 (1): the reciprocal of the complex Gamma function admits the Weierstrass
infinite product expansion. -/
theorem complex_gamma_reciprocal_eq_weierstrass_product (z : ℂ) :
    1 / Complex.Gamma z =
      z * Complex.exp ((γ : ℂ) * z) *
        ∏' k : ℕ, ((1 + z / (k + 1 : ℂ)) * Complex.exp (-z / (k + 1 : ℂ))) := by
  by_cases hz : z ∈ D
  · exact complex_gamma_reciprocal_eq_weierstrass_product_of_mem_domain hz
  · rcases (show z ∈ Set.range (fun n : ℕ ↦ -(n : ℂ)) by simpa using hz) with ⟨n, rfl⟩
    cases n with
    | zero =>
        -- At `z = 0`, both sides vanish from the front factor / Gamma pole.
        have hzero :
            1 / Complex.Gamma (0 : ℂ) =
              (0 : ℂ) * Complex.exp ((γ : ℂ) * 0) *
                ∏' k : ℕ,
                  ((1 + (0 : ℂ) / (k + 1 : ℂ)) * Complex.exp (-(0 : ℂ) / (k + 1 : ℂ))) := by
          simp [Complex.Gamma_zero]
        simpa using hzero
    | succ m =>
        -- At `z = -(m + 1)`, Gamma vanishes and the Weierstrass product has the matching zero.
        have htprod : ∏' k : ℕ, W k (-(m + 1 : ℂ)) = 0 :=
          weierstrass_tprod_eq_zero_at_neg_succ m
        have hGamma : Complex.Gamma (-(m + 1 : ℂ)) = 0 := by
          simpa using Complex.Gamma_neg_nat_eq_zero (m + 1)
        have htprod' :
            ∏' k : ℕ,
                ((1 + (-(m + 1 : ℂ)) / (k + 1 : ℂ)) *
                  Complex.exp (-(-(m + 1 : ℂ)) / (k + 1 : ℂ))) = 0 := by
          simpa using htprod
        have hmain :
            1 / Complex.Gamma (-(m + 1 : ℂ)) =
              (-(m + 1 : ℂ)) * Complex.exp ((γ : ℂ) * (-(m + 1 : ℂ))) *
                ∏' k : ℕ,
                  ((1 + (-(m + 1 : ℂ)) / (k + 1 : ℂ)) *
                    Complex.exp (-(-(m + 1 : ℂ)) / (k + 1 : ℂ))) := by
          calc
            1 / Complex.Gamma (-(m + 1 : ℂ)) = 1 / 0 := by rw [hGamma]
            _ = 0 := by simp
            _ = (-(m + 1 : ℂ)) * Complex.exp ((γ : ℂ) * (-(m + 1 : ℂ))) * 0 := by simp
            _ =
                (-(m + 1 : ℂ)) * Complex.exp ((γ : ℂ) * (-(m + 1 : ℂ))) *
                  ∏' k : ℕ,
                    ((1 + (-(m + 1 : ℂ)) / (k + 1 : ℂ)) *
                      Complex.exp (-(-(m + 1 : ℂ)) / (k + 1 : ℂ))) := by rw [htprod']
        simpa using hmain

/-- Remark V.3-extra-5 (2): the Weierstrass factors for the reciprocal Gamma product are
normally convergent on each compact subset of the complex plane. -/
theorem multipliableUniformlyOn_weierstrass_gamma_factor_on_compact {K : Set ℂ}
    (hK : IsCompact K) :
    MultipliableUniformlyOn
      (fun n : ℕ ↦ fun z ↦ (1 + z / (n + 1 : ℂ)) * Complex.exp (-z / (n + 1 : ℂ))) K := by
  let u : ℕ → ℂ → ℂ := fun n z ↦
    ((1 + z / (n + 1 : ℂ)) * Complex.exp (-z / (n + 1 : ℂ))) - 1
  obtain ⟨C, _hC_nonneg, hbound⟩ :=
    weierstrass_gamma_factor_sub_one_eventually_norm_le_on_compact hK
  have hsummable_inv_sq : Summable (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))⁻¹) := by
    simpa using
      ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.mpr (by norm_num : 1 < (2 : ℝ))))
  have hsummable : Summable (fun n : ℕ ↦ 3 * C ^ (2 : ℕ) / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hsummable_inv_sq.mul_left (3 * C ^ (2 : ℕ))
  have hu_cont : ∀ n, ContinuousOn (u n) K := by
    intro n
    -- Each perturbation is built from elementary holomorphic operations.
    fun_prop
  have hmul :
      MultipliableUniformlyOn (fun n z ↦ 1 + u n z) K :=
    Summable.multipliableUniformlyOn_nat_one_add hK hsummable hbound hu_cont
  -- Reassemble the factors from the `1 + u_n` perturbation form.
  simpa [u] using hmul

/-- Remark V.3-extra-5 (3): away from the poles of `Γ`, its logarithmic derivative is given by
the Euler-Mascheroni series. -/
theorem complex_digamma_eq_euler_mascheroni_series (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    Complex.digamma z =
      -(1 / z) - γ +
        ∑' n : ℕ, ((1 / (n + 1 : ℂ)) - 1 / (z + (n + 1 : ℂ)) ) := by
  -- TODO: apply the logarithmic-derivative product theorem from `0004_Theorem_2` to the
  -- Weierstrass product and rewrite each factor's logarithmic derivative explicitly.
  sorry

/-- Remark V.3-extra-5 (4): after removing the simple pole at the origin from the digamma
function, the punctured limit is minus Euler's constant. -/
theorem tendsto_complex_digamma_add_inv_nhdsWithin_zero :
    Filter.Tendsto (fun z : ℂ ↦ Complex.digamma z + 1 / z) (𝓝[≠] 0)
      (𝓝 (-(γ : ℂ))) := by
  -- TODO: use the digamma series on a small punctured ball around `0` and show the tail tends
  -- uniformly to `0`, leaving only the constant term `-γ`.
  sorry

/-- Remark V.3-extra-5 (5): away from the poles of `Γ`, the derivative of the digamma function
is the series of inverse squares. -/
theorem deriv_complex_digamma_eq_inverse_square_series (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    deriv Complex.digamma z = ∑' n : ℕ, 1 / ((z + n : ℂ) ^ (2 : ℕ)) := by
  -- TODO: differentiate the digamma series term-by-term on a pole-free neighborhood and combine
  -- the derivative of `-(1 / z)` with the shifted inverse-square tail.
  sorry

/- Remark V.3-extra-5 (6): the real function `x ↦ log (Γ x)` is convex on the positive reals. -/
recall Real.convexOn_log_Gamma
