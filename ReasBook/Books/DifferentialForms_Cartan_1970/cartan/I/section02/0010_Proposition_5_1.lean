import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.RingTheory.PowerSeries.Substitution
import DifferentialForms_Cartan_1970.cartan.I.section02.«0004_Definition_I_2_extra_3»
import DifferentialForms_Cartan_1970.cartan.I.section02.«0008_Proposition_4_1»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open PowerSeries
open Filter
open scoped BigOperators PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {S T : 𝕜⟦X⟧} {r : NNReal}

-- Source/core/bridge triage:
-- * source-facing: the present scalar-series composition bounds and evaluation identity from
--   Proposition 5.1;
-- * core/canonical: the local `PowerSeries.radius` / `PowerSeries.sum` owner together with
--   Mathlib's `FormalMultilinearSeries.comp_summable_nnreal`,
--   `FormalMultilinearSeries.le_comp_radius_of_summable`, and `HasFPowerSeriesAt.comp`;
-- * bridge/view: this file specializes those analytic owners to ordinary scalar power series.
--
-- Semantic recall note: the owner/API choice was checked directly against Mathlib's
-- dotted `PowerSeries.subst` surface together with `PowerSeries.constantCoeff`,
-- the local `PowerSeries.radius`/`PowerSeries.sum` owner,
-- `FormalMultilinearSeries.le_comp_radius_of_summable`, and `HasFPowerSeriesAt.comp`.

/-- Helper for Proposition 5.1: the standard shrinking factor used in the scalar majorant argument
is positive and at most one half. -/
lemma scalar_composition_factor_pos_le_half {σ C : NNReal} (hσ : 0 < σ) (hC : 0 < C) :
    let a : NNReal := min (1 / 2) (σ / (4 * C))
    0 < a ∧ a ≤ 1 / 2 := by
  let a : NNReal := min (1 / 2) (σ / (4 * C))
  constructor
  · -- The factor is positive because both candidate bounds are positive.
    dsimp [a]
    rw [lt_min_iff]
    constructor
    · norm_num
    · exact div_pos hσ (by positivity)
  · -- The shrinking factor is capped by `1 / 2` by construction.
    exact min_le_left _ _

/-- Helper for Proposition 5.1: the standard shrinking factor forces the prefactor `C * a`
below `σ / 4`. -/
lemma mul_scalar_composition_factor_le_quarter {σ C : NNReal} (hC : 0 < C) :
    let a : NNReal := min (1 / 2) (σ / (4 * C))
    C * a ≤ σ / 4 := by
  let a : NNReal := min (1 / 2) (σ / (4 * C))
  have hamin : a ≤ σ / (4 * C) := min_le_right _ _
  rw [← NNReal.coe_le_coe] at hamin ⊢
  push_cast
  have hmul : (a : ℝ) * (4 * C) ≤ σ := by
    exact (le_div_iff₀ (show (0 : ℝ) < 4 * C by positivity)).1 hamin
  refine (le_div_iff₀ (show (0 : ℝ) < 4 by positivity)).2 ?_
  simpa [a, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Proposition 5.1 (1): if scalar power series `S` and `T` have nonzero convergence radius and
`T` has vanishing constant coefficient, then one can choose `r > 0` with
`∑ ‖bₙ‖ rⁿ < ρ(S)`. -/
theorem exists_radius_for_scalar_series_composition
    (hT0 : T.constantCoeff = 0)
    (hS : S.radius ≠ 0) (hT : T.radius ≠ 0) :
    ∃ r : NNReal, 0 < r ∧
      Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n) ∧
      ENNReal.ofNNReal (∑' n : ℕ, ‖coeff n T‖₊ * r ^ n) < S.radius := by
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 fun n ↦ coeff n T
  have hSpos : 0 < S.radius := pos_iff_ne_zero.2 hS
  have hTpos : 0 < T.radius := pos_iff_ne_zero.2 hT
  -- Choose strict positive scalar bounds inside the two radii of convergence.
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hSpos with ⟨σ, hσ0, hσlt⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hTpos with ⟨ρ, hρ0, hρlt⟩
  have hσ0' : 0 < σ := ENNReal.coe_pos.1 hσ0
  have hρ0' : 0 < ρ := ENNReal.coe_pos.1 hρ0
  obtain ⟨C, hC0, hC⟩ := p.nnnorm_mul_pow_le_of_lt_radius (by
    simpa [p, PowerSeries.radius] using hρlt)
  let a : NNReal := min (1 / 2) (σ / (4 * C))
  let r : NNReal := ρ * a
  have hcoeff0 : coeff 0 T = 0 := by
    simpa using hT0
  have ha : 0 < a ∧ a ≤ 1 / 2 :=
    scalar_composition_factor_pos_le_half hσ0' hC0
  have hCa : C * a ≤ σ / 4 :=
    mul_scalar_composition_factor_le_quarter (σ := σ) hC0
  have hr_pos : 0 < r := mul_pos hρ0' ha.1
  have hcoeff_mul_pow_le : ∀ n : ℕ, ‖coeff n T‖₊ * ρ ^ n ≤ C := by
    intro n
    have hpcoeff : p.coeff n = coeff n T := by
      simpa [p] using
        (FormalMultilinearSeries.coeff_ofScalars (𝕜 := 𝕜) (p := fun m ↦ coeff m T) (n := n))
    have hpnorm : ‖p.coeff n‖ ≤ ‖p n‖ := by
      -- The coefficient is the value of the multilinear map at the all-ones vector.
      change ‖p n 1‖ ≤ ‖p n‖
      simpa using (p n).le_opNorm (1 : Fin n → 𝕜)
    have hcoeff_le : ‖coeff n T‖ ≤ ‖p n‖ := by
      -- Evaluate the scalar multilinear map on the all-ones vector to recover the coefficient.
      calc
        ‖coeff n T‖ = ‖p.coeff n‖ := by rw [hpcoeff]
        _ ≤ ‖p n‖ := hpnorm
    have hbound_real : ‖coeff n T‖ * (ρ : ℝ) ^ n ≤ C := by
      calc
        ‖coeff n T‖ * (ρ : ℝ) ^ n ≤ ‖p n‖ * (ρ : ℝ) ^ n := by
          exact mul_le_mul_of_nonneg_right hcoeff_le (by positivity)
        _ ≤ C := by
          exact_mod_cast hC n
    exact_mod_cast hbound_real
  have hterm_bound : ∀ n : ℕ, ‖coeff n T‖₊ * r ^ n ≤ C * a ^ n := by
    intro n
    -- Pull out the chosen factor `a` from `r = ρ * a`.
    calc
      ‖coeff n T‖₊ * r ^ n = (‖coeff n T‖₊ * ρ ^ n) * a ^ n := by
        simp [r, mul_assoc, mul_left_comm, mul_comm, mul_pow]
      _ ≤ C * a ^ n := by
        exact mul_le_mul' (hcoeff_mul_pow_le n) le_rfl
  have htail_bound : ∀ n : ℕ, ‖coeff (n + 1) T‖₊ * r ^ (n + 1) ≤ (C * a) * (1 / 2) ^ n := by
    intro n
    -- On the tail, the extra factor `a` is controlled by `a ≤ 1 / 2`.
    calc
      ‖coeff (n + 1) T‖₊ * r ^ (n + 1) ≤ C * a ^ (n + 1) := hterm_bound (n + 1)
      _ = (C * a) * a ^ n := by
        rw [pow_succ]
        ring
      _ ≤ (C * a) * (1 / 2) ^ n := by
        gcongr
        exact ha.2
  have htail_summable :
      Summable (fun n : ℕ => ‖coeff (n + 1) T‖₊ * r ^ (n + 1)) := by
    -- The tail is dominated by a geometric series.
    exact NNReal.summable_of_le htail_bound
      ((NNReal.summable_geometric (by norm_num : ((1 / 2 : NNReal) < 1))).mul_left (C * a))
  have hsum :
      Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n) := by
    -- The constant term vanishes, so summability reduces to the tail.
    exact (NNReal.summable_nat_add_iff 1).mp htail_summable
  have hzero : ‖coeff 0 T‖₊ * r ^ 0 = 0 := by
    simp [hcoeff0]
  have htail_tsum_le : ∑' n : ℕ, ‖coeff (n + 1) T‖₊ * r ^ (n + 1) ≤ (C * a) * 2 := by
    -- Sum the same geometric majorant on the tail.
    have hmajorant_summable :
        Summable (fun n : ℕ => (C * a) * (1 / 2 : NNReal) ^ n) :=
      (NNReal.summable_geometric (by norm_num : ((1 / 2 : NNReal) < 1))).mul_left (C * a)
    have hgeom : ∑' n : ℕ, ((1 / 2 : NNReal) ^ n) = 2 := by
      calc
        ∑' n : ℕ, ((1 / 2 : NNReal) ^ n) = (1 - (1 / 2 : NNReal))⁻¹ := by
          simpa using NNReal.tsum_geometric (by norm_num : ((1 / 2 : NNReal) < 1))
        _ = 2 := by
          have hhalf : (1 - (1 / 2 : NNReal)) = 1 / 2 := by
            apply NNReal.coe_injective
            rw [NNReal.coe_sub (by norm_num : ((1 / 2 : NNReal) ≤ 1))]
            norm_num [one_div]
          rw [hhalf]
          norm_num [one_div]
    calc
      ∑' n : ℕ, ‖coeff (n + 1) T‖₊ * r ^ (n + 1)
          ≤ ∑' n : ℕ, (C * a) * (1 / 2 : NNReal) ^ n := by
            exact htail_summable.tsum_le_tsum htail_bound hmajorant_summable
      _ = (C * a) * 2 := by
            rw [NNReal.tsum_mul_left, hgeom]
  have htsum_le_sigma : ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n ≤ σ := by
    have hshift : ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n =
        ‖coeff 0 T‖₊ * r ^ 0 + ∑' n : ℕ, ‖coeff (n + 1) T‖₊ * r ^ (n + 1) := by
      simpa using NNReal.sum_add_tsum_nat_add 1 hsum
    calc
      ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n
          = ‖coeff 0 T‖₊ * r ^ 0 + ∑' n : ℕ, ‖coeff (n + 1) T‖₊ * r ^ (n + 1) := hshift
      _ ≤ (C * a) * 2 := by
        rw [hzero, zero_add]
        exact htail_tsum_le
      _ ≤ σ / 2 := by
        have hdouble : (C * a) * 2 ≤ (σ / 4) * 2 := by
          exact mul_le_mul' hCa le_rfl
        calc
          (C * a) * 2 ≤ (σ / 4) * 2 := hdouble
          _ = σ / 2 := by ring
      _ ≤ σ := by
        have : σ / 2 ≤ σ := by
          nlinarith [show (0 : ℝ) ≤ σ by exact_mod_cast hσ0'.le]
        exact this
  refine ⟨r, hr_pos, hsum, ?_⟩
  -- The majorant sum lies below the chosen scalar bound `σ`, itself strictly inside `S.radius`.
  exact lt_of_le_of_lt (by exact_mod_cast htsum_le_sigma) hσlt

/-- Helper for Proposition 5.1: every power `T ^ d` is controlled by the scalar majorant
`∑ ‖coeff n T‖ r^n`. -/
lemma weighted_coeff_pow_summable_le_majorant_pow
    (T : 𝕜⟦X⟧) (r : NNReal)
    (hsum : Summable (fun n : ℕ => ‖coeff n T‖ * (r : ℝ) ^ n)) :
    ∀ d : ℕ,
      Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ∧
        ∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤
          (∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n) ^ d := by
  intro d
  induction d with
  | zero =>
      have hone_tail :
          Summable (fun n : ℕ => ‖coeff (n + 1) (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ (n + 1)) := by
        simpa [PowerSeries.coeff_one] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
      have hone :
          Summable (fun n : ℕ => ‖coeff n (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ n) := by
        rw [← _root_.summable_nat_add_iff
          (f := fun n : ℕ => ‖coeff n (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ n) 1]
        exact hone_tail
      refine ⟨by simpa using hone, ?_⟩
      have hone_split :
          ∑' n : ℕ, ‖coeff n (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ n =
            ‖coeff 0 (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ 0 +
              ∑' n : ℕ, ‖coeff (n + 1) (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ (n + 1) := by
        simpa using (Summable.sum_add_tsum_nat_add 1 hone).symm
      calc
        ∑' n : ℕ, ‖coeff n (T ^ 0)‖ * (r : ℝ) ^ n
            = ∑' n : ℕ, ‖coeff n (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ n := by simp
        _ = ‖coeff 0 (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ 0 +
              ∑' n : ℕ, ‖coeff (n + 1) (1 : 𝕜⟦X⟧)‖ * (r : ℝ) ^ (n + 1) := hone_split
        _ = 1 := by simp [PowerSeries.coeff_one]
        _ ≤ (∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n) ^ 0 := by simp
  | succ d ih =>
      have hr_nonneg : 0 ≤ (r : ℝ) := by
        exact_mod_cast r.2
      obtain ⟨hd_sum, hd_le⟩ := ih
      have hd_norm :
          Summable (fun n : ℕ => ‖‖coeff n (T ^ d)‖ * (r : ℝ) ^ n‖) := by
        -- The induction hypothesis already gives a nonnegative real summable sequence.
        refine Summable.of_nonneg_of_le ?_ ?_ hd_sum
        · intro n
          exact norm_nonneg _
        · intro n
          have hnonneg : 0 ≤ ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n :=
            mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hT_norm :
          Summable (fun n : ℕ => ‖‖coeff n T‖ * (r : ℝ) ^ n‖) := by
        -- The same positivity reduction applies to the original series.
        refine Summable.of_nonneg_of_le ?_ ?_ hsum
        · intro n
          exact norm_nonneg _
        · intro n
          have hnonneg : 0 ≤ ‖coeff n T‖ * (r : ℝ) ^ n :=
            mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      have hmajorant_summable :
          Summable
            (fun n : ℕ =>
              ∑ k ∈ Finset.range (n + 1),
                (‖coeff k (T ^ d)‖ * (r : ℝ) ^ k) *
                  (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k))) :=
        summable_sum_mul_range_of_summable_norm'
          (f := fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n)
          (g := fun n : ℕ => ‖coeff n T‖ * (r : ℝ) ^ n)
          hd_norm hd_sum hT_norm hsum
      have hprod_sum :
          Summable (fun n : ℕ => ‖coeff n ((T ^ d) * T)‖ * (r : ℝ) ^ n) := by
        -- Proposition 4.1 gives the weighted Cauchy-product majorant for the next power.
        refine Summable.of_nonneg_of_le ?_ ?_ hmajorant_summable
        · intro n
          exact mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
        · intro n
          exact coeff_mul_mul_pow_le_cauchy_majorant (T ^ d) T r n
      have hprod_le :
          ∑' n : ℕ, ‖coeff n ((T ^ d) * T)‖ * (r : ℝ) ^ n ≤
            (∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) *
              ∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n := by
        calc
          ∑' n : ℕ, ‖coeff n ((T ^ d) * T)‖ * (r : ℝ) ^ n
              ≤ ∑' n : ℕ,
                  ∑ k ∈ Finset.range (n + 1),
                    (‖coeff k (T ^ d)‖ * (r : ℝ) ^ k) *
                      (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k)) := by
                    exact hprod_sum.tsum_le_tsum
                      (fun n ↦ coeff_mul_mul_pow_le_cauchy_majorant (T ^ d) T r n)
                      hmajorant_summable
          _ =
              (∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) *
                ∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n := by
                  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
                    (f := fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n)
                    (g := fun n : ℕ => ‖coeff n T‖ * (r : ℝ) ^ n)
                    hd_norm hT_norm]
      refine ⟨by simpa [pow_succ] using hprod_sum, ?_⟩
      have htsum_nonneg : 0 ≤ ∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n := by
        exact tsum_nonneg fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)
      calc
        ∑' n : ℕ, ‖coeff n (T ^ (d + 1))‖ * (r : ℝ) ^ n
            = ∑' n : ℕ, ‖coeff n ((T ^ d) * T)‖ * (r : ℝ) ^ n := by simp [pow_succ]
        _ ≤ (∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) *
              ∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n := hprod_le
        _ ≤ (∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n) ^ d *
              ∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n := by
              exact mul_le_mul_of_nonneg_right hd_le htsum_nonneg
        _ = (∑' n : ℕ, ‖coeff n T‖ * (r : ℝ) ^ n) ^ (d + 1) := by
              rw [pow_succ, mul_comm]

/-- Helper for Proposition 5.1: if the inner series has zero constant coefficient, then only
outer degrees at most `n` contribute to the `n`th coefficient of the substitution. -/
lemma coeff_subst_eq_sum_range_of_constantCoeff_zero
    {A T : 𝕜⟦X⟧}
    (hT0 : T.constantCoeff = 0)
    (n : ℕ) :
    coeff n (A.subst T) = ∑ d ∈ Finset.range (n + 1), coeff d A * coeff n (T ^ d) := by
  have hT : HasSubst T := HasSubst.of_constantCoeff_zero' hT0
  -- Replace the `finsum` formula by a finite sum using the order bound on powers of `T`.
  rw [coeff_subst' hT, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    rw [Function.mem_support] at hd
    by_contra hdn
    have hdn' : ¬ d < n + 1 := by
      simpa [Finset.mem_range] using hdn
    have hnd : n < d := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.not_lt.mp hdn')
    have hzero : coeff n (T ^ d) = 0 := by
      -- The power `T ^ d` has order at least `d`, so its `n`th coefficient vanishes for `n < d`.
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast hnd) (le_order_pow_of_constantCoeff_eq_zero d hT0)
    exact hd <| by simp [hzero]

/-- Helper for Proposition 5.1: each substituted coefficient is dominated by the rectangular
majorant obtained by fixing the target degree `n` and summing over the outer degree `d`. -/
lemma subst_weighted_coeff_le_tsum_row_majorant
    (A T : 𝕜⟦X⟧) (r : NNReal) (B : ℝ)
    (hT0 : T.constantCoeff = 0)
    (hpow : ∀ d : ℕ,
      Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ∧
        ∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤ B ^ d)
    (hA : Summable (fun d : ℕ => ‖coeff d A‖ * B ^ d))
    (n : ℕ) :
    ‖coeff n (A.subst T)‖ * (r : ℝ) ^ n ≤
      ∑' d : ℕ, ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) := by
  have hB_nonneg : 0 ≤ B := by
    -- The source majorant is nonnegative because the `d = 1` weighted power sum is nonnegative.
    have hpow_nonneg :
        0 ≤ ∑' n : ℕ, ‖coeff n (T ^ 1)‖ * (r : ℝ) ^ n := by
      exact tsum_nonneg fun m ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)
    simpa using hpow_nonneg.trans (hpow 1).2
  have hcolumn_summable :
      Summable (fun d : ℕ => ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n)) := by
    -- Compare the fixed-`n` column with the outer scalar majorant `‖coeff d A‖ * B^d`.
    refine Summable.of_nonneg_of_le ?_ ?_ hA
    · intro d
      exact mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
    · intro d
      have hsingle_le :
          ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤
            ∑' m : ℕ, ‖coeff m (T ^ d)‖ * (r : ℝ) ^ m := by
        simpa using
          (hpow d).1.sum_le_tsum ({n} : Finset ℕ)
            (fun m _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
      calc
        ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n)
            ≤ ‖coeff d A‖ * ∑' m : ℕ, ‖coeff m (T ^ d)‖ * (r : ℝ) ^ m := by
              exact mul_le_mul_of_nonneg_left hsingle_le (norm_nonneg _)
        _ ≤ ‖coeff d A‖ * B ^ d := by
              exact mul_le_mul_of_nonneg_left (hpow d).2 (norm_nonneg _)
  -- Route correction: the source proof first fixes the target degree `n` and bounds the
  -- finite outer-degree sum by the full column tsum before any global sigma/Fubini step.
  calc
    ‖coeff n (A.subst T)‖ * (r : ℝ) ^ n =
        ‖∑ d ∈ Finset.range (n + 1), coeff d A * coeff n (T ^ d)‖ * (r : ℝ) ^ n := by
          rw [coeff_subst_eq_sum_range_of_constantCoeff_zero hT0]
    _ ≤ (∑ d ∈ Finset.range (n + 1), ‖coeff d A * coeff n (T ^ d)‖) * (r : ℝ) ^ n := by
          exact mul_le_mul_of_nonneg_right
            (norm_sum_le (Finset.range (n + 1)) fun d ↦ coeff d A * coeff n (T ^ d))
            (pow_nonneg (by positivity) _)
    _ = ∑ d ∈ Finset.range (n + 1), ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [norm_mul]
          ring
    _ ≤ ∑' d : ℕ, ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) := by
          exact hcolumn_summable.sum_le_tsum (Finset.range (n + 1))
            (fun d _ ↦
              mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
            )

/-- Helper for Proposition 5.1: the rectangular majorant indexed by outer degree and coefficient
degree is summable, and its total mass is controlled by the scalar majorant `∑ ‖coeff d A‖ B^d`.
-/
lemma subst_majorant_sigma_summable
    (A T : 𝕜⟦X⟧) (r : NNReal) (B : ℝ)
    (hpow : ∀ d : ℕ,
      Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ∧
        ∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤ B ^ d)
    (hA : Summable (fun d : ℕ => ‖coeff d A‖ * B ^ d)) :
    Summable (fun n : ℕ => ∑' d : ℕ, ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n)) ∧
      ∑' n : ℕ, ∑' d : ℕ, ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ≤
        ∑' d : ℕ, ‖coeff d A‖ * B ^ d := by
  let M : ℕ → ℕ → ℝ := fun d n ↦ ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n)
  have hB_nonneg : 0 ≤ B := by
    -- The `d = 1` control again forces the scalar majorant to be nonnegative.
    have hpow_nonneg :
        0 ≤ ∑' n : ℕ, ‖coeff n (T ^ 1)‖ * (r : ℝ) ^ n := by
      exact tsum_nonneg fun m ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)
    simpa using hpow_nonneg.trans (hpow 1).2
  have hrow_summable :
      ∀ d : ℕ, Summable (fun n : ℕ => M d n) := by
    intro d
    -- Each outer-degree row is just the weighted power estimate scaled by `‖coeff d A‖`.
    simpa [M, mul_assoc, mul_left_comm, mul_comm] using (hpow d).1.mul_left ‖coeff d A‖
  have hrow_tsum_le :
      ∀ d : ℕ, ∑' n : ℕ, M d n ≤ ‖coeff d A‖ * B ^ d := by
    intro d
    -- Sum each row first, then apply the scalar majorant `B^d`.
    calc
      ∑' n : ℕ, M d n
          = ‖coeff d A‖ * ∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n := by
              simp [M, tsum_mul_left]
      _ ≤ ‖coeff d A‖ * B ^ d := by
            exact mul_le_mul_of_nonneg_left (hpow d).2 (norm_nonneg _)
  have houter_summable :
      Summable (fun d : ℕ => ∑' n : ℕ, M d n) := by
    -- The source proof next sums the row masses against `‖coeff d A‖ * B^d`.
    refine Summable.of_nonneg_of_le ?_ ?_ hA
    · intro d
      exact tsum_nonneg fun n ↦
        mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
    · intro d
      exact hrow_tsum_le d
  have hrect :
      Summable (fun p : ℕ × ℕ => M p.1 p.2) := by
    -- This is the rectangular Fubini package requested by the source argument.
    exact (summable_prod_of_nonneg
      (fun p : ℕ × ℕ ↦
        mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
      )).2 ⟨hrow_summable, houter_summable⟩
  have hcolumn_summable :
      ∀ n : ℕ, Summable (fun d : ℕ => M d n) := by
    intro n
    -- For each fixed coefficient degree, compare the full column to the same outer majorant.
    refine Summable.of_nonneg_of_le ?_ ?_ hA
    · intro d
      exact mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
    · intro d
      have hsingle_le :
          ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤
            ∑' m : ℕ, ‖coeff m (T ^ d)‖ * (r : ℝ) ^ m := by
        simpa using
          (hpow d).1.sum_le_tsum ({n} : Finset ℕ)
            (fun m _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
      calc
        M d n ≤ ‖coeff d A‖ * ∑' m : ℕ, ‖coeff m (T ^ d)‖ * (r : ℝ) ^ m := by
          exact mul_le_mul_of_nonneg_left hsingle_le (norm_nonneg _)
        _ ≤ ‖coeff d A‖ * B ^ d := by
          exact mul_le_mul_of_nonneg_left (hpow d).2 (norm_nonneg _)
  have hcolumns_hasSum :
      HasSum (fun n : ℕ => ∑' d : ℕ, M d n) (∑' p : ℕ × ℕ, M p.2 p.1) := by
    -- Summing the swapped rectangular family fiberwise recovers the column tsums.
    exact HasSum.prod_fiberwise hrect.prod_symm.hasSum (fun n ↦ (hcolumn_summable n).hasSum)
  refine ⟨hcolumns_hasSum.summable, ?_⟩
  calc
    ∑' n : ℕ, ∑' d : ℕ, M d n = ∑' p : ℕ × ℕ, M p.2 p.1 := hcolumns_hasSum.tsum_eq
    _ = ∑' p : ℕ × ℕ, M p.1 p.2 := by
          simpa using (Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ ↦ M p.1 p.2)
    _ = ∑' d : ℕ, ∑' n : ℕ, M d n := hrect.tsum_prod' hrow_summable
    _ ≤ ∑' d : ℕ, ‖coeff d A‖ * B ^ d := by
          exact houter_summable.tsum_le_tsum hrow_tsum_le hA

lemma subst_weighted_coeff_tsum_le_majorant_series
    (A T : 𝕜⟦X⟧) (r : NNReal) (B : ℝ)
    (hT0 : T.constantCoeff = 0)
    (hpow : ∀ d : ℕ,
      Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ∧
        ∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤ B ^ d)
    (hA : Summable (fun d : ℕ => ‖coeff d A‖ * B ^ d)) :
    Summable (fun n : ℕ => ‖coeff n (A.subst T)‖ * (r : ℝ) ^ n) ∧
      ∑' n : ℕ, ‖coeff n (A.subst T)‖ * (r : ℝ) ^ n ≤
        ∑' d : ℕ, ‖coeff d A‖ * B ^ d := by
  have hmajorant :
      Summable (fun n : ℕ => ∑' d : ℕ, ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n)) ∧
        ∑' n : ℕ, ∑' d : ℕ, ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ≤
          ∑' d : ℕ, ‖coeff d A‖ * B ^ d :=
    subst_majorant_sigma_summable (A := A) (T := T) (r := r) (B := B) hpow hA
  have hsubst :
      Summable (fun n : ℕ => ‖coeff n (A.subst T)‖ * (r : ℝ) ^ n) := by
    -- Dominate each substituted coefficient by the summable rectangular majorant column sum.
    refine Summable.of_nonneg_of_le ?_ ?_ hmajorant.1
    · intro n
      exact mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)
    · intro n
      exact subst_weighted_coeff_le_tsum_row_majorant
        (A := A) (T := T) (r := r) (B := B) hT0 hpow hA n
  have hmajorantSum :
      Summable (fun n : ℕ => ∑' d : ℕ, ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n)) :=
    hmajorant.1
  refine ⟨?_, ?_⟩
  · exact hsubst
  · -- Summing the pointwise bound yields the desired global majorant for `A.subst T`.
    exact (Summable.tsum_le_tsum
      (f := fun n : ℕ => ‖coeff n (A.subst T)‖ * (r : ℝ) ^ n)
      (g := fun n : ℕ => ∑' d : ℕ, ‖coeff d A‖ * (‖coeff n (T ^ d)‖ * (r : ℝ) ^ n))
      (fun n ↦ subst_weighted_coeff_le_tsum_row_majorant
        (A := A) (T := T) (r := r) (B := B) hT0 hpow hA n)
      hsubst
      hmajorantSum).trans hmajorant.2

/-- Proposition 5.1 (2): if the scalar majorant `∑ ‖bₙ‖ rⁿ` converges and is less than `ρ(S)`,
then the scalar formal composition `U = S ∘ T` has convergence radius at least `r`. -/
theorem radius_ge_comp_of_scalar_series_bound
    (hT0 : T.constantCoeff = 0)
    (hsum : Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n))
    (hr : ENNReal.ofNNReal (∑' n : ℕ, ‖coeff n T‖₊ * r ^ n) < S.radius) :
    let U : 𝕜⟦X⟧ := S.subst T
    (r : ENNReal) ≤ U.radius := by
  let Bnn : NNReal := ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n
  have hsum_real : Summable (fun n : ℕ => ‖coeff n T‖ * (r : ℝ) ^ n) := by
    exact (NNReal.summable_coe).2 <| by
      simpa using hsum
  have hpow :
      ∀ d : ℕ,
        Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ∧
          ∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤ (Bnn : ℝ) ^ d := by
    -- The scalar majorant for `T` propagates uniformly to all powers `T ^ d`.
    have hpow' := weighted_coeff_pow_summable_le_majorant_pow T r hsum_real
    simpa [Bnn, NNReal.coe_tsum] using hpow'
  have hBlt : (Bnn : ENNReal) < S.radius := by
    simpa [Bnn] using hr
  have hSsum : Summable (fun d : ℕ => ‖coeff d S‖ * (Bnn : ℝ) ^ d) :=
    summable_norm_coeff_mul_pow_of_lt_radius S hBlt
  have hU :
      Summable (fun n : ℕ => ‖coeff n (S.subst T)‖ * (r : ℝ) ^ n) :=
    (subst_weighted_coeff_tsum_le_majorant_series
      (A := S) (T := T) (r := r) (B := (Bnn : ℝ)) hT0 hpow hSsum).1
  -- Translate the weighted summability estimate back to the convergence radius of the scalar
  -- formal series `S.subst T`.
  change (r : ENNReal) ≤ (ofScalars 𝕜 (fun n ↦ coeff n (S.subst T))).radius
  exact (ofScalars 𝕜 fun n ↦ coeff n (S.subst T)).le_radius_of_summable_norm (by
    simpa using hU)

section

variable [CompleteSpace 𝕜]
variable {z : 𝕜}

/-- Proposition 5.1 (3): for `‖z‖ ≤ r`, the value of `T(z)` lies strictly inside the convergence
disk of `S`. -/
-- TODO: compare `‖T.sum z‖₊` with the scalar majorant `∑ ‖coeff n T‖₊ r^n` on the closed disk
-- `‖z‖₊ ≤ r`, and then finish with `hr`.
theorem norm_sum_right_lt_radius_left
    (hsum : Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n))
    (hr : ENNReal.ofNNReal (∑' n : ℕ, ‖coeff n T‖₊ * r ^ n) < S.radius)
    (hz : ‖z‖₊ ≤ r) :
    (‖T.sum z‖₊ : ENNReal) < S.radius := by
  have hnorm_summable :
      Summable (fun n : ℕ => ‖coeff n T * z ^ n‖₊) := by
    -- Absolute convergence on the closed disk follows from the scalar majorant at radius `r`.
    refine NNReal.summable_of_le ?_ hsum
    intro n
    calc
      ‖coeff n T * z ^ n‖₊ = ‖coeff n T‖₊ * ‖z‖₊ ^ n := by
        rw [nnnorm_mul, nnnorm_pow]
      _ ≤ ‖coeff n T‖₊ * r ^ n := by
        gcongr
  have hsum_bound : ‖T.sum z‖₊ ≤ ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n := by
    -- Compare the summed value with the absolute scalar majorant termwise.
    calc
      ‖T.sum z‖₊ = ‖∑' n : ℕ, coeff n T * z ^ n‖₊ := by
        simp [PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul]
      _ ≤ ∑' n : ℕ, ‖coeff n T * z ^ n‖₊ := nnnorm_tsum_le hnorm_summable
      _ ≤ ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n := by
        refine hnorm_summable.tsum_le_tsum ?_ hsum
        intro n
        calc
          ‖coeff n T * z ^ n‖₊ = ‖coeff n T‖₊ * ‖z‖₊ ^ n := by
            rw [nnnorm_mul, nnnorm_pow]
          _ ≤ ‖coeff n T‖₊ * r ^ n := by
            gcongr
  exact lt_of_le_of_lt (by exact_mod_cast hsum_bound) hr

/-- Helper for Proposition 5.1: on the closed disk `‖z‖ ≤ r`, any scalar series whose weighted
coefficients are summable at radius `r` is absolutely summable at `z`. -/
lemma summable_norm_eval_of_weighted_coeff
    (A : 𝕜⟦X⟧)
    (hA : Summable (fun n : ℕ => ‖coeff n A‖ * (r : ℝ) ^ n))
    (hz : ‖z‖₊ ≤ r) :
    Summable (fun n : ℕ => ‖coeff n A * z ^ n‖) := by
  -- Compare the closed-disk evaluation termwise with the weighted coefficient majorant at `r`.
  refine Summable.of_nonneg_of_le ?_ ?_ hA
  · intro n
    exact norm_nonneg _
  · intro n
    calc
      ‖coeff n A * z ^ n‖ = ‖coeff n A‖ * ‖z‖ ^ n := by
        rw [norm_mul, norm_pow]
      _ ≤ ‖coeff n A‖ * (r : ℝ) ^ n := by
        gcongr
        exact_mod_cast hz

/-- Helper for Proposition 5.1: constant scalar series are summable at every point, and their sum
is the constant itself. -/
lemma constant_series_summable_and_sum (a z : 𝕜) :
    Summable (fun n : ℕ => ‖coeff n (PowerSeries.C a : 𝕜⟦X⟧) * z ^ n‖) ∧
      Summable (fun n : ℕ => coeff n (PowerSeries.C a : 𝕜⟦X⟧) * z ^ n) ∧
      (PowerSeries.C a : 𝕜⟦X⟧).sum z = a := by
  have hnorm_tail :
      Summable (fun n : ℕ => ‖coeff (n + 1) (PowerSeries.C a : 𝕜⟦X⟧) * z ^ (n + 1)‖) := by
    simpa [PowerSeries.coeff_succ_C] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hterm_tail :
      Summable (fun n : ℕ => coeff (n + 1) (PowerSeries.C a : 𝕜⟦X⟧) * z ^ (n + 1)) := by
    simpa [PowerSeries.coeff_succ_C] using (summable_zero : Summable (fun _ : ℕ => (0 : 𝕜)))
  have hnorm :
      Summable (fun n : ℕ => ‖coeff n (PowerSeries.C a : 𝕜⟦X⟧) * z ^ n‖) := by
    exact (_root_.summable_nat_add_iff
      (f := fun n : ℕ => ‖coeff n (PowerSeries.C a : 𝕜⟦X⟧) * z ^ n‖) 1).mp hnorm_tail
  have hterm :
      Summable (fun n : ℕ => coeff n (PowerSeries.C a : 𝕜⟦X⟧) * z ^ n) := by
    exact (_root_.summable_nat_add_iff
      (f := fun n : ℕ => coeff n (PowerSeries.C a : 𝕜⟦X⟧) * z ^ n) 1).mp hterm_tail
  refine ⟨hnorm, hterm, ?_⟩
  -- Only the constant coefficient survives in the series sum.
  rw [PowerSeries.sum, ofScalars_sum_eq, tsum_eq_sum (s := {0})]
  · simp [PowerSeries.coeff_C]
  · intro n hn
    have hn0 : n ≠ 0 := by
      simpa using hn
    simp [PowerSeries.coeff_C, hn0]

/-- Helper for Proposition 5.1: evaluating powers of `T` at `z` agrees with taking powers of the
evaluated value `T(z)`. -/
lemma pow_sum_eq_sum_pow
    (hpow : ∀ d : ℕ, Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n))
    (hz : ‖z‖₊ ≤ r) :
    ∀ d : ℕ, (T ^ d).sum z = (T.sum z) ^ d := by
  have hTz_norm :
      Summable (fun n : ℕ => ‖coeff n T * z ^ n‖) :=
    summable_norm_eval_of_weighted_coeff (A := T) (r := r) (z := z) (by simpa using hpow 1) hz
  have hTz :
      Summable (fun n : ℕ => coeff n T * z ^ n) := hTz_norm.of_norm
  intro d
  induction d with
  | zero =>
      -- The base case is the constant series `1`.
      simpa using (constant_series_summable_and_sum (a := (1 : 𝕜)) (z := z)).2.2
  | succ d ih =>
      have hTd_norm :
          Summable (fun n : ℕ => ‖coeff n (T ^ d) * z ^ n‖) :=
        summable_norm_eval_of_weighted_coeff (A := T ^ d) (r := r) (z := z) (hpow d) hz
      have hTd :
          Summable (fun n : ℕ => coeff n (T ^ d) * z ^ n) := hTd_norm.of_norm
      -- Multiplying the summable `T^d` and `T` series gives the next power.
      calc
        (T ^ (d + 1)).sum z = ((T ^ d) * T).sum z := by
          simp [pow_succ]
        _ = (T ^ d).sum z * T.sum z := by
          exact sum_mul_eq_mul_sum (T ^ d) T z hTd_norm hTd hTz_norm hTz
        _ = (T.sum z) ^ d * T.sum z := by
          rw [ih]
        _ = (T.sum z) ^ (d + 1) := by
          rw [pow_succ]

/-- Helper for Proposition 5.1: substituted polynomials in `T` are summable at `z`, and their
value is the ordinary polynomial evaluation at `T(z)`. -/
lemma subst_polynomial_summable_and_sum_eq_aeval
    (hT0 : T.constantCoeff = 0)
    (hpow : ∀ d : ℕ, Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n))
    (hpow_sum : ∀ d : ℕ, (T ^ d).sum z = (T.sum z) ^ d)
    (hz : ‖z‖₊ ≤ r) :
    ∀ p : Polynomial 𝕜,
      Summable (fun n : ℕ => ‖coeff n (PowerSeries.subst T (↑p : 𝕜⟦X⟧)) * z ^ n‖) ∧
        Summable (fun n : ℕ => coeff n (PowerSeries.subst T (↑p : 𝕜⟦X⟧)) * z ^ n) ∧
        PowerSeries.sum (PowerSeries.subst T (↑p : 𝕜⟦X⟧)) z = Polynomial.aeval (T.sum z) p := by
  let hsub : HasSubst T := HasSubst.of_constantCoeff_zero' hT0
  -- Route correction: keep the source proof at the polynomial-truncation level, and normalize each
  -- substituted monomial to `C a * T^d` before summing.
  intro p
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rcases hp with ⟨hp_norm, hp_term, hp_sum⟩
    rcases hq with ⟨hq_norm, hq_term, hq_sum⟩
    have hsubst_add :
        PowerSeries.subst T (↑(p + q) : 𝕜⟦X⟧) =
          PowerSeries.subst T (↑p : 𝕜⟦X⟧) + PowerSeries.subst T (↑q : 𝕜⟦X⟧) := by
      simpa using (PowerSeries.subst_add hsub (↑p : 𝕜⟦X⟧) (↑q : 𝕜⟦X⟧))
    refine ⟨?_, ?_, ?_⟩
    · -- Absolute convergence is controlled by the sum of the two monomial blocks.
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_ (hp_norm.add hq_norm)
      intro n
      rw [hsubst_add, map_add, add_mul]
      exact norm_add_le _ _
    · -- Ordinary convergence follows by additivity after rewriting the substituted sum.
      rw [hsubst_add]
      simpa [map_add, add_mul] using hp_term.add hq_term
    · -- Evaluation commutes with substitution on finite polynomial sums.
      rw [hsubst_add, sum_add_eq _ _ _ hp_term hq_term, hp_sum, hq_sum,
        Polynomial.aeval_add]
  · intro d a
    have hconst := constant_series_summable_and_sum (a := a) (z := z)
    have hTd_norm :
        Summable (fun n : ℕ => ‖coeff n (T ^ d) * z ^ n‖) :=
      summable_norm_eval_of_weighted_coeff (A := T ^ d) (r := r) (z := z) (hpow d) hz
    have hTd : Summable (fun n : ℕ => coeff n (T ^ d) * z ^ n) := hTd_norm.of_norm
    refine ⟨?_, ?_, ?_⟩
    · -- After rewriting the substituted monomial to `C a * T^d`, each evaluation term is a fixed
      -- scalar multiple of the `T^d` evaluation term.
      have hmul :
          Summable (fun n : ℕ => ‖a‖ * ‖coeff n (T ^ d) * z ^ n‖) :=
        hTd_norm.mul_left ‖a‖
      refine hmul.congr ?_
      intro n
      rw [PowerSeries.subst_coe hsub, Polynomial.aeval_monomial]
      simp [PowerSeries.coeff_C_mul, norm_mul, mul_assoc, mul_left_comm, mul_comm]
    · -- The same coefficient rewrite gives the ordinary series as a scalar multiple.
      have hmul : Summable (fun n : ℕ => a * (coeff n (T ^ d) * z ^ n)) := hTd.mul_left a
      refine hmul.congr ?_
      intro n
      rw [PowerSeries.subst_coe hsub, Polynomial.aeval_monomial]
      simp [PowerSeries.coeff_C_mul, mul_assoc, mul_left_comm, mul_comm]
    · -- Evaluate `C a * T^d` by Proposition 4.1, then replace `(T^d).sum z` with `(T.sum z)^d`.
      rw [PowerSeries.subst_coe hsub, Polynomial.aeval_monomial]
      calc
        PowerSeries.sum (PowerSeries.C a * T ^ d) z
            = (PowerSeries.C a).sum z * (T ^ d).sum z := by
                exact sum_mul_eq_mul_sum (PowerSeries.C a) (T ^ d) z hconst.1 hconst.2.1 hTd_norm hTd
        _ = a * (T.sum z) ^ d := by rw [hconst.2.2, hpow_sum d]
        _ = Polynomial.aeval (T.sum z) (Polynomial.monomial d a) := by
              simp [Polynomial.aeval_monomial, mul_comm]

/-- Helper for Proposition 5.1: the substituted truncation `U_N` evaluates to the `N`th partial
sum of `S` at `T(z)`. -/
lemma trunc_subst_sum_eq_sum_range
    (hT0 : T.constantCoeff = 0)
    (hsum : Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n))
    (hz : ‖z‖₊ ≤ r)
    (N : ℕ) :
    PowerSeries.sum (PowerSeries.subst T (↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z =
      Finset.sum (Finset.range N) (fun i ↦ coeff i S * (T.sum z) ^ i) := by
  have hsum_real : Summable (fun n : ℕ => ‖coeff n T‖ * (r : ℝ) ^ n) := by
    exact (NNReal.summable_coe).2 <| by simpa using hsum
  have hpow :
      ∀ d : ℕ, Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) :=
    fun d ↦ (weighted_coeff_pow_summable_le_majorant_pow T r hsum_real d).1
  have hpow_sum :
      ∀ d : ℕ, (T ^ d).sum z = (T.sum z) ^ d :=
    pow_sum_eq_sum_pow (T := T) (r := r) (z := z) hpow hz
  have htrunc :=
    (subst_polynomial_summable_and_sum_eq_aeval
      (T := T) (r := r) (z := z) hT0 hpow hpow_sum hz (PowerSeries.trunc N S)).2.2
  -- The source truncation `S_N` evaluates at `T.sum z` as the explicit finite sum of coefficients.
  calc
    PowerSeries.sum (PowerSeries.subst T (↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z
        = Polynomial.aeval (T.sum z) (PowerSeries.trunc N S) := htrunc
    _ = Finset.sum (Finset.range N) (fun i ↦ coeff i S * (T.sum z) ^ i) := by
          simpa [Polynomial.aeval_def] using
            (PowerSeries.eval₂_trunc_eq_sum_range
              (s := T.sum z) (G := Algebra.algebraMap 𝕜 𝕜) N S)

/-- Helper for Proposition 5.1: coefficientwise, `S - trunc N S` keeps precisely the tail of `S`
starting at degree `N`. -/
lemma coeff_sub_trunc_eq_ite_tail
    (N d : ℕ) :
    coeff d (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧) = if d < N then 0 else coeff d S := by
  -- Normalize the truncation coefficient first, then split on whether `d` lies below the cut.
  by_cases hd : d < N
  · rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hd, sub_self]
    simp [hd]
  · rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_neg hd, sub_zero]
    simp [hd]

/-- Helper for Proposition 5.1: deleting the degree-`< N` truncation leaves exactly the scalar
`nat_add` tail of the outer majorant series. -/
lemma tail_majorant_eq_nat_add_tail
    (N : ℕ) (B : ℝ) (hB_nonneg : 0 ≤ B)
    (hS : Summable (fun d : ℕ => ‖coeff d S‖ * B ^ d)) :
    ∑' d : ℕ, ‖coeff d (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)‖ * B ^ d =
      (∑' m : ℕ, ‖coeff (N + m) S‖ * B ^ (N + m)) := by
  let f : ℕ → ℝ := fun d ↦ ‖coeff d (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)‖ * B ^ d
  have hf : Summable f := by
    -- The tail majorant is termwise bounded by the original scalar majorant for `S`.
    refine Summable.of_nonneg_of_le (fun d ↦ ?_) (fun d ↦ ?_) hS
    · exact mul_nonneg (norm_nonneg _) (pow_nonneg hB_nonneg _)
    · by_cases hd : d < N
      · have hnonneg : 0 ≤ ‖coeff d S‖ * B ^ d :=
          mul_nonneg (norm_nonneg _) (pow_nonneg hB_nonneg _)
        simpa [f, coeff_sub_trunc_eq_ite_tail, hd] using hnonneg
      · simp [f, coeff_sub_trunc_eq_ite_tail, hd]
  have hprefix :
      Finset.sum (Finset.range N) f = 0 := by
    -- Every term below `N` vanishes because the truncation removes those coefficients.
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    have hdlt : d < N := Finset.mem_range.mp hd
    simp [f, coeff_sub_trunc_eq_ite_tail, hdlt]
  have htail :
      (∑' m : ℕ, f (m + N)) = (∑' m : ℕ, ‖coeff (N + m) S‖ * B ^ (N + m)) := by
    -- On the shifted tail, the `if`-branch is always in the surviving case.
    refine tsum_congr fun m ↦ ?_
    have hnotlt : ¬ (m + N < N) := Nat.not_lt.mpr (Nat.le_add_left N m)
    simp [f, coeff_sub_trunc_eq_ite_tail, hnotlt, add_comm, add_left_comm, add_assoc]
  -- Split the scalar series at `N`, kill the zero prefix, and read the remainder as the `Nat.add`
  -- tail from the source proof.
  calc
    ∑' d : ℕ, f d = Finset.sum (Finset.range N) f + ∑' m : ℕ, f (m + N) := by
      simpa [f, add_comm, add_left_comm, add_assoc] using (hf.sum_add_tsum_nat_add N).symm
    _ = ∑' m : ℕ, f (m + N) := by simp [hprefix]
    _ = ∑' m : ℕ, ‖coeff (N + m) S‖ * B ^ (N + m) := htail

/-- Helper for Proposition 5.1: evaluating a scalar series on the closed disk is controlled by the
same weighted majorant that controls its coefficients at radius `r`. -/
lemma norm_sum_le_weighted_tsum
    (A : 𝕜⟦X⟧)
    (hA : Summable (fun n : ℕ => ‖coeff n A‖ * (r : ℝ) ^ n))
    (hz : ‖z‖₊ ≤ r) :
    ‖A.sum z‖ ≤ ∑' n : ℕ, ‖coeff n A‖ * (r : ℝ) ^ n := by
  have hnorm :
      Summable (fun n : ℕ => ‖coeff n A * z ^ n‖) :=
    summable_norm_eval_of_weighted_coeff (A := A) (r := r) (z := z) hA hz
  -- Compare the actual sum to the termwise norm tsum, then to the closed-disk majorant.
  calc
    ‖A.sum z‖ = ‖∑' n : ℕ, coeff n A * z ^ n‖ := by
      simp [PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul]
    _ ≤ ∑' n : ℕ, ‖coeff n A * z ^ n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖coeff n A‖ * (r : ℝ) ^ n := by
          refine hnorm.tsum_le_tsum ?_ hA
          intro n
          calc
            ‖coeff n A * z ^ n‖ = ‖coeff n A‖ * ‖z‖ ^ n := by
              rw [norm_mul, norm_pow]
            _ ≤ ‖coeff n A‖ * (r : ℝ) ^ n := by
              gcongr
              exact_mod_cast hz

/-- Helper for Proposition 5.1: the substituted tail remains absolutely summable on the closed
disk `‖z‖ ≤ r`. -/
lemma subst_tail_eval_summable
    (hT0 : T.constantCoeff = 0)
    (hsum : Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n))
    (hr : ENNReal.ofNNReal (∑' n : ℕ, ‖coeff n T‖₊ * r ^ n) < S.radius)
    (hz : ‖z‖₊ ≤ r)
    (N : ℕ) :
    Summable (fun n : ℕ =>
      ‖coeff n (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) * z ^ n‖) ∧
      Summable (fun n : ℕ =>
        coeff n (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) * z ^ n) := by
  let A : 𝕜⟦X⟧ := S - ↑(PowerSeries.trunc N S)
  let U : 𝕜⟦X⟧ := PowerSeries.subst T A
  let Bnn : NNReal := ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n
  have hsum_real : Summable (fun n : ℕ => ‖coeff n T‖ * (r : ℝ) ^ n) := by
    exact (NNReal.summable_coe).2 <| by simpa using hsum
  have hpow :
      ∀ d : ℕ,
        Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ∧
          ∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤ (Bnn : ℝ) ^ d := by
    have hpow' := weighted_coeff_pow_summable_le_majorant_pow T r hsum_real
    simpa [Bnn, NNReal.coe_tsum] using hpow'
  have hBlt : (Bnn : ENNReal) < S.radius := by
    simpa [Bnn] using hr
  have htail_majorant :
      Summable
        (fun d : ℕ => ‖coeff d A‖ * ((Bnn : ℝ) ^ d)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ (summable_norm_coeff_mul_pow_of_lt_radius S hBlt)
    · intro d
      exact mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)
    · intro d
      by_cases hd : d < N
      · -- Below the truncation order, the tail coefficient vanishes.
        dsimp [A]
        rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hd]
        have hnonneg : 0 ≤ ‖coeff d S‖ * (Bnn : ℝ) ^ d :=
          mul_nonneg (norm_nonneg _) (pow_nonneg (by exact_mod_cast Bnn.2) _)
        simpa using hnonneg
      · -- Above the truncation order, the truncation contributes no coefficient.
        dsimp [A]
        rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_neg hd]
        simp
  have hsubst :
      Summable (fun n : ℕ => ‖coeff n U‖ * (r : ℝ) ^ n) := by
    dsimp [U]
    exact (subst_weighted_coeff_tsum_le_majorant_series
      (A := A)
      (T := T) (r := r) (B := (Bnn : ℝ)) hT0 hpow htail_majorant).1
  -- Pass from the weighted bound at radius `r` to absolute convergence on the closed disk.
  have hnorm : Summable (fun n : ℕ => ‖coeff n U * z ^ n‖) :=
    summable_norm_eval_of_weighted_coeff (A := U) (r := r) (z := z) hsubst hz
  have hterm : Summable (fun n : ℕ => coeff n U * z ^ n) := hnorm.of_norm
  simpa [A, U] using And.intro hnorm hterm

/-- Helper for Proposition 5.1: the norm of the substituted tail is controlled by the scalar tail
of `∑ ‖coeff d S‖ B^d`, where `B = ∑ ‖coeff n T‖ r^n`. -/
lemma subst_tail_norm_le_scalar_tail
    (hT0 : T.constantCoeff = 0)
    (hsum : Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n))
    (hr : ENNReal.ofNNReal (∑' n : ℕ, ‖coeff n T‖₊ * r ^ n) < S.radius)
    (hz : ‖z‖₊ ≤ r)
    (N : ℕ) :
    ‖PowerSeries.sum (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z‖ ≤
      (∑' m : ℕ,
        ‖coeff (N + m) S‖ *
          (((∑' n : ℕ, ‖coeff n T‖₊ * r ^ n : NNReal) : ℝ)) ^ (N + m)) := by
  let A : 𝕜⟦X⟧ := S - ↑(PowerSeries.trunc N S)
  let U : 𝕜⟦X⟧ := PowerSeries.subst T A
  let Bnn : NNReal := ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n
  have hsum_real : Summable (fun n : ℕ => ‖coeff n T‖ * (r : ℝ) ^ n) := by
    exact (NNReal.summable_coe).2 <| by simpa using hsum
  have hpow :
      ∀ d : ℕ,
        Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) ∧
          ∑' n : ℕ, ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n ≤ (Bnn : ℝ) ^ d := by
    -- Reuse the established majorant for the powers `T ^ d`.
    have hpow' := weighted_coeff_pow_summable_le_majorant_pow T r hsum_real
    simpa [Bnn, NNReal.coe_tsum] using hpow'
  have hBlt : (Bnn : ENNReal) < S.radius := by
    simpa [Bnn] using hr
  have hSmajorant : Summable (fun d : ℕ => ‖coeff d S‖ * (Bnn : ℝ) ^ d) :=
    summable_norm_coeff_mul_pow_of_lt_radius S hBlt
  have hAmajorant : Summable (fun d : ℕ => ‖coeff d A‖ * (Bnn : ℝ) ^ d) := by
    -- The truncated tail is dominated coefficientwise by the original outer majorant.
    refine Summable.of_nonneg_of_le (fun d ↦ ?_) (fun d ↦ ?_) hSmajorant
    · exact mul_nonneg (norm_nonneg _) (pow_nonneg (by exact_mod_cast Bnn.2) _)
    · by_cases hd : d < N
      · have hnonneg : 0 ≤ ‖coeff d S‖ * (Bnn : ℝ) ^ d :=
          mul_nonneg (norm_nonneg _) (pow_nonneg (by exact_mod_cast Bnn.2) _)
        simpa [A, coeff_sub_trunc_eq_ite_tail, hd, Bnn] using hnonneg
      · simp [A, coeff_sub_trunc_eq_ite_tail, hd, Bnn]
  have hUmajorant :
      Summable (fun n : ℕ => ‖coeff n U‖ * (r : ℝ) ^ n) ∧
        ∑' n : ℕ, ‖coeff n U‖ * (r : ℝ) ^ n ≤
          ∑' d : ℕ, ‖coeff d A‖ * (Bnn : ℝ) ^ d := by
    -- The substitution bound reduces the tail estimate to the outer scalar majorant.
    dsimp [U]
    exact subst_weighted_coeff_tsum_le_majorant_series
      (A := A) (T := T) (r := r) (B := (Bnn : ℝ)) hT0 hpow hAmajorant
  -- Route correction: instead of unfolding `subst` directly, first bound the substituted tail by
  -- `norm_sum_le_weighted_tsum`, then rewrite its outer scalar majorant to the `Nat.add` tail.
  calc
    ‖PowerSeries.sum (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z‖
        = ‖U.sum z‖ := by simp [A, U]
    _ ≤ ∑' n : ℕ, ‖coeff n U‖ * (r : ℝ) ^ n := norm_sum_le_weighted_tsum U hUmajorant.1 hz
    _ ≤ ∑' d : ℕ, ‖coeff d A‖ * (Bnn : ℝ) ^ d := hUmajorant.2
    _ = ∑' m : ℕ, ‖coeff (N + m) S‖ * (Bnn : ℝ) ^ (N + m) := by
          simpa [A, Bnn] using
            tail_majorant_eq_nat_add_tail
              (S := S) (N := N) (B := (Bnn : ℝ)) (by exact_mod_cast Bnn.2) hSmajorant

/-- Helper for Proposition 5.1: the substituted tails converge to zero on the closed disk, exactly
as in the source truncation-and-tail argument. -/
lemma subst_tail_tendsto_zero_of_majorant_tail
    (hT0 : T.constantCoeff = 0)
    (hsum : Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n))
    (hr : ENNReal.ofNNReal (∑' n : ℕ, ‖coeff n T‖₊ * r ^ n) < S.radius)
    (hz : ‖z‖₊ ≤ r) :
    Filter.Tendsto (fun N : ℕ => PowerSeries.sum (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z)
      atTop (nhds 0) := by
  let Bnn : NNReal := ∑' n : ℕ, ‖coeff n T‖₊ * r ^ n
  let a : ℕ → ℝ := fun d ↦ ‖coeff d S‖ * (Bnn : ℝ) ^ d
  have htail :
      Filter.Tendsto (fun N : ℕ => ∑' m : ℕ, a (N + m)) atTop (nhds 0) := by
    -- The scalar majorant tail tends to zero exactly as in the source proof.
    simpa [a, add_comm, add_left_comm, add_assoc] using (_root_.tendsto_sum_nat_add a)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun N ↦ norm_nonneg _) (fun N ↦ ?_) htail
  -- The substituted tail is pointwise controlled by the same shifted scalar tail.
  simpa [a, Bnn] using subst_tail_norm_le_scalar_tail
    (S := S) (T := T) (r := r) (z := z) hT0 hsum hr hz N

/-- Proposition 5.1 (4): for `‖z‖ ≤ r`, evaluating the composite series agrees with composing the
evaluations: `S(T(z)) = U(z)` for `U = S ∘ T`. -/
-- TODO: identify polynomial truncations after substitution with polynomial evaluation at `T.sum z`,
-- then pass to the limit using the same scalar majorant tail as in Proposition 5.1 (2).
theorem sum_comp_eq_comp_sum
    (hT0 : T.constantCoeff = 0)
    (hsum : Summable (fun n : ℕ => ‖coeff n T‖₊ * r ^ n))
    (hr : ENNReal.ofNNReal (∑' n : ℕ, ‖coeff n T‖₊ * r ^ n) < S.radius)
    (hz : ‖z‖₊ ≤ r) :
    let U : 𝕜⟦X⟧ := S.subst T
    S.sum (T.sum z) = U.sum z := by
  let U : 𝕜⟦X⟧ := S.subst T
  change S.sum (T.sum z) = U.sum z
  let hsub : HasSubst T := HasSubst.of_constantCoeff_zero' hT0
  have hsum_real : Summable (fun n : ℕ => ‖coeff n T‖ * (r : ℝ) ^ n) := by
    exact (NNReal.summable_coe).2 <| by simpa using hsum
  have hpow :
      ∀ d : ℕ, Summable (fun n : ℕ => ‖coeff n (T ^ d)‖ * (r : ℝ) ^ n) :=
    fun d ↦ (weighted_coeff_pow_summable_le_majorant_pow T r hsum_real d).1
  have hpow_sum :
      ∀ d : ℕ, (T ^ d).sum z = (T.sum z) ^ d :=
    pow_sum_eq_sum_pow (T := T) (r := r) (z := z) hpow hz
  have hTz_lt : (‖T.sum z‖₊ : ENNReal) < S.radius :=
    norm_sum_right_lt_radius_left (S := S) (T := T) (r := r) (z := z) hsum hr hz
  have houter_norm :
      Summable (fun n : ℕ => ‖coeff n S * (T.sum z) ^ n‖) :=
    summable_norm_eval_of_weighted_coeff
      (A := S) (r := ‖T.sum z‖₊) (z := T.sum z)
      (summable_norm_coeff_mul_pow_of_lt_radius S hTz_lt) le_rfl
  have houter :
      Summable (fun n : ℕ => coeff n S * (T.sum z) ^ n) := houter_norm.of_norm
  have htrunc_to_left :
      Filter.Tendsto
        (fun N : ℕ =>
          PowerSeries.sum (PowerSeries.subst T (↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z)
        atTop (nhds (S.sum (T.sum z))) := by
    let v : ℕ → 𝕜 := fun N ↦ Finset.sum (Finset.range N) (fun i ↦ coeff i S * (T.sum z) ^ i)
    have hv : Filter.Tendsto v atTop (nhds (S.sum (T.sum z))) := by
      simpa [v, PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul] using houter.hasSum.tendsto_sum_nat
    have hseq :
        (fun N : ℕ => PowerSeries.sum (PowerSeries.subst T (↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z) = v := by
      funext N
      exact trunc_subst_sum_eq_sum_range (S := S) (T := T) (r := r) (z := z) hT0 hsum hz N
    -- The substituted truncations are exactly the partial sums of `S` evaluated at `T.sum z`.
    simpa [hseq] using hv
  have htail_zero :
      Filter.Tendsto
        (fun N : ℕ =>
          PowerSeries.sum (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z)
        atTop (nhds 0) :=
    subst_tail_tendsto_zero_of_majorant_tail
      (S := S) (T := T) (r := r) (z := z) hT0 hsum hr hz
  have hsplit_sum :
      ∀ N : ℕ,
        U.sum z =
          PowerSeries.sum (PowerSeries.subst T (↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z +
            PowerSeries.sum (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z := by
    intro N
    let P : 𝕜⟦X⟧ := PowerSeries.subst T (↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)
    let R : 𝕜⟦X⟧ := PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)
    have hP_term :
        Summable (fun n : ℕ => coeff n P * z ^ n) := by
      -- The truncation piece is a polynomial in `T`, so its evaluation is a finite-source sum.
      simpa [P] using
        (subst_polynomial_summable_and_sum_eq_aeval
          (T := T) (r := r) (z := z) hT0 hpow hpow_sum hz (PowerSeries.trunc N S)).2.1
    have hR_term :
        Summable (fun n : ℕ => coeff n R * z ^ n) := by
      -- The tail piece inherits summability from the substitution majorant estimate.
      simpa [R] using
        (subst_tail_eval_summable
          (S := S) (T := T) (r := r) (z := z) hT0 hsum hr hz N).2
    have hsubst_split :
        P + R = U := by
      -- Route correction: decompose `S` as `trunc N S + (S - trunc N S)` before substituting.
      dsimp [P, R, U]
      rw [← PowerSeries.subst_add hsub]
      simp
    simpa [hsubst_split] using (sum_add_eq P R z hP_term hR_term)
  have htrunc_to_right :
      Filter.Tendsto
        (fun N : ℕ =>
          PowerSeries.sum (PowerSeries.subst T (↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z)
        atTop (nhds (U.sum z)) := by
    have hsub_tail :
        Filter.Tendsto
          (fun N : ℕ =>
            U.sum z -
              PowerSeries.sum (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z)
          atTop (nhds (U.sum z - 0)) :=
      Filter.Tendsto.sub tendsto_const_nhds htail_zero
    let w : ℕ → 𝕜 := fun N ↦
      U.sum z - PowerSeries.sum (PowerSeries.subst T (S - ↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z
    have hw : Filter.Tendsto w atTop (nhds (U.sum z)) := by
      simpa [w] using hsub_tail
    have hseq :
        (fun N : ℕ => PowerSeries.sum (PowerSeries.subst T (↑(PowerSeries.trunc N S) : 𝕜⟦X⟧)) z) = w := by
      funext N
      exact (eq_sub_iff_add_eq).2 (hsplit_sum N).symm
    simpa [hseq] using hw
  -- The common truncation sequence has the two target limits, so uniqueness gives the identity.
  exact tendsto_nhds_unique htrunc_to_left htrunc_to_right

end
