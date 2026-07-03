import Mathlib
import cartan.I.section02.«0004_Definition_I_2_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open PowerSeries
open scoped PowerSeries
universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the owner/API
-- choice was checked against the local `PowerSeries.radius`/`PowerSeries.sum` owner together with
-- Mathlib's `PowerSeries.coeff_mul`, `FormalMultilinearSeries.ofScalars_add`, and
-- `FormalMultilinearSeries.min_radius_le_radius_add`.

/-- Proposition 4.1 (1): if two scalar power series both have radius of convergence at least `ρ`,
then their sum also has radius of convergence at least `ρ`. -/
theorem radius_ge_add
    (S T : 𝕜⟦X⟧) (ρ : NNReal)
    (hS : (ρ : ENNReal) ≤ S.radius)
    (hT : (ρ : ENNReal) ≤ T.radius) :
    (ρ : ENNReal) ≤ (S + T).radius := by
  calc
    (ρ : ENNReal) ≤ min S.radius T.radius := le_min hS hT
    _ ≤ ((ofScalars 𝕜 (fun n ↦ coeff n S)) + (ofScalars 𝕜 fun n ↦ coeff n T)).radius := by
      simpa [PowerSeries.radius] using
        min_radius_le_radius_add (ofScalars 𝕜 fun n ↦ coeff n S)
          (ofScalars 𝕜 fun n ↦ coeff n T)
    _ = (S + T).radius := by
      have hcoeff :
          (fun n ↦ coeff n (S + T)) = (fun n ↦ coeff n S) + fun n ↦ coeff n T := by
        ext n
        simp
      rw [PowerSeries.radius, hcoeff, ofScalars_add]

/-- Helper for Proposition 4.1: a scalar power series is absolutely summable on every closed ball
strictly inside its radius of convergence. -/
lemma summable_norm_coeff_mul_pow_of_lt_radius
    (U : 𝕜⟦X⟧) {r : NNReal} (hr : (r : ENNReal) < U.radius) :
    Summable (fun n : ℕ ↦ ‖coeff n U‖ * (r : ℝ) ^ n) := by
  -- Rewrite the scalar power series radius through its multilinear owner.
  simpa [PowerSeries.radius] using
    (FormalMultilinearSeries.summable_norm_mul_pow
      (ofScalars 𝕜 fun n ↦ coeff n U) hr)

/-- Helper for Proposition 4.1: the weighted coefficient of a product is dominated by the
corresponding weighted Cauchy-product majorant. -/
lemma coeff_mul_mul_pow_le_cauchy_majorant
    (S T : 𝕜⟦X⟧) (r : NNReal) (n : ℕ) :
    ‖coeff n (S * T)‖ * (r : ℝ) ^ n ≤
      ∑ k ∈ Finset.range (n + 1),
        (‖coeff k S‖ * (r : ℝ) ^ k) * (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k)) := by
  have hr_nonneg : 0 ≤ (r : ℝ) := by
    exact_mod_cast r.2
  -- Rewrite the coefficient using the finite Cauchy-product formula.
  calc
    ‖coeff n (S * T)‖ * (r : ℝ) ^ n
        = ‖∑ k ∈ Finset.range (n + 1), coeff k S * coeff (n - k) T‖ * (r : ℝ) ^ n := by
            rw [PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun k l ↦ coeff k S * coeff l T) n]
    _ ≤ (∑ k ∈ Finset.range (n + 1), ‖coeff k S * coeff (n - k) T‖) * (r : ℝ) ^ n := by
          exact mul_le_mul_of_nonneg_right
            (norm_sum_le (Finset.range (n + 1)) fun k ↦ coeff k S * coeff (n - k) T)
            (pow_nonneg hr_nonneg n)
    _ = ∑ k ∈ Finset.range (n + 1), ‖coeff k S * coeff (n - k) T‖ * (r : ℝ) ^ n := by
          rw [Finset.sum_mul]
    _ = ∑ k ∈ Finset.range (n + 1),
          (‖coeff k S‖ * (r : ℝ) ^ k) * (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [norm_mul]
          calc
            (‖coeff k S‖ * ‖coeff (n - k) T‖) * (r : ℝ) ^ n
                = (‖coeff k S‖ * ‖coeff (n - k) T‖) *
                    ((r : ℝ) ^ k * (r : ℝ) ^ (n - k)) := by
                      rw [← pow_add, Nat.add_sub_of_le hk']
            _ = (‖coeff k S‖ * (r : ℝ) ^ k) *
                  (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k)) := by
                    ac_rfl

/-- Helper for Proposition 4.1: the weighted Cauchy majorant of two scalar power series is
summable whenever both radii dominate the chosen scalar `r`. -/
lemma summable_cauchy_majorant_of_lt_radius
    (S T : 𝕜⟦X⟧) (r : NNReal)
    (hS : (r : ENNReal) < S.radius) (hT : (r : ENNReal) < T.radius) :
    Summable (fun n ↦ ∑ k ∈ Finset.range (n + 1),
      (‖coeff k S‖ * (r : ℝ) ^ k) * (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k))) := by
  have hr_nonneg : 0 ≤ (r : ℝ) := by
    exact_mod_cast r.2
  have hS_sum :
      Summable (fun n : ℕ ↦ ‖coeff n S‖ * (r : ℝ) ^ n) :=
    summable_norm_coeff_mul_pow_of_lt_radius S hS
  have hT_sum :
      Summable (fun n : ℕ ↦ ‖coeff n T‖ * (r : ℝ) ^ n) :=
    summable_norm_coeff_mul_pow_of_lt_radius T hT
  have hS_norm :
      Summable (fun n : ℕ ↦ ‖‖coeff n S‖ * (r : ℝ) ^ n‖) := by
    -- The weighted scalar coefficients are nonnegative reals, so taking norms changes nothing.
    refine Summable.of_nonneg_of_le ?_ ?_ hS_sum
    · intro n
      exact norm_nonneg _
    · intro n
      have hnonneg : 0 ≤ ‖coeff n S‖ * (r : ℝ) ^ n :=
        mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hT_norm :
      Summable (fun n : ℕ ↦ ‖‖coeff n T‖ * (r : ℝ) ^ n‖) := by
    -- The same positivity argument applies to the second series.
    refine Summable.of_nonneg_of_le ?_ ?_ hT_sum
    · intro n
      exact norm_nonneg _
    · intro n
      have hnonneg : 0 ≤ ‖coeff n T‖ * (r : ℝ) ^ n :=
        mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  -- Apply the standard Cauchy-product summability theorem to the weighted norm sequences.
  exact (hasSum_sum_range_mul_of_summable_norm hS_norm hT_norm).summable

/-- Proposition 4.1 (2): if two scalar power series both have radius of convergence at least `ρ`,
then their product also has radius of convergence at least `ρ`. -/
theorem radius_ge_mul
    (S T : 𝕜⟦X⟧) (ρ : NNReal)
    (hS : (ρ : ENNReal) ≤ S.radius)
    (hT : (ρ : ENNReal) ≤ T.radius) :
    (ρ : ENNReal) ≤ (S * T).radius := by
  -- Follow the source proof: fix `r < ρ`, prove absolute convergence for the weighted product
  -- coefficients, and then turn that convergence estimate into a radius lower bound.
  refine ENNReal.le_of_forall_nnreal_lt ?_
  intro r hr
  have hrrho : (r : ENNReal) < (ρ : ENNReal) := by
    exact_mod_cast hr
  have hrS : (r : ENNReal) < S.radius :=
    lt_of_lt_of_le hrrho hS
  have hrT : (r : ENNReal) < T.radius :=
    lt_of_lt_of_le hrrho hT
  have hr_nonneg : 0 ≤ (r : ℝ) := by
    exact_mod_cast r.2
  have hmajorant :
      Summable (fun n ↦ ∑ k ∈ Finset.range (n + 1),
        (‖coeff k S‖ * (r : ℝ) ^ k) * (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k))) :=
    summable_cauchy_majorant_of_lt_radius S T r hrS hrT
  have hproduct :
      Summable (fun n : ℕ ↦ ‖coeff n (S * T)‖ * (r : ℝ) ^ n) := by
    -- Dominate the weighted product coefficients by the summable Cauchy majorant.
    refine Summable.of_nonneg_of_le ?_ ?_ hmajorant
    · intro n
      exact mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
    · intro n
      exact coeff_mul_mul_pow_le_cauchy_majorant S T r n
  have hproduct_owner :
      Summable (fun n : ℕ ↦ ‖ofScalars 𝕜 (fun m ↦ coeff m (S * T)) n‖ * (r : ℝ) ^ n) := by
    -- Re-express the coefficient estimate for the multilinear owner of the scalar series.
    simpa using hproduct
  -- Translate the weighted absolute convergence estimate back to the convergence radius.
  change (r : ENNReal) ≤ (ofScalars 𝕜 fun n ↦ coeff n (S * T)).radius
  exact (ofScalars 𝕜 fun n ↦ coeff n (S * T)).le_radius_of_summable_norm hproduct_owner

/-- Proposition 4.1 (3): evaluating two summable scalar power series at a common point commutes
with addition. -/
theorem sum_add_eq
    (S T : 𝕜⟦X⟧) (z : 𝕜)
    (hS : Summable (fun n ↦ coeff n S * z ^ n))
    (hT : Summable (fun n ↦ coeff n T * z ^ n)) :
    (S + T).sum z = S.sum z + T.sum z := by
  simpa [PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul, add_mul] using
    (Summable.tsum_add hS hT)

/-- Proposition 4.1 (4): evaluating two absolutely summable scalar power series at a common point
commutes with multiplication. -/
theorem sum_mul_eq_mul_sum
    (S T : 𝕜⟦X⟧) (z : 𝕜)
    (hS_norm : Summable (fun n ↦ ‖coeff n S * z ^ n‖))
    (hS : Summable (fun n ↦ coeff n S * z ^ n))
    (hT_norm : Summable (fun n ↦ ‖coeff n T * z ^ n‖))
    (hT : Summable (fun n ↦ coeff n T * z ^ n)) :
    (S * T).sum z = S.sum z * T.sum z := by
  have hterm :
      ∀ n,
        (∑ k ∈ Finset.range (n + 1), (coeff k S * z ^ k) * (coeff (n - k) T * z ^ (n - k))) =
          coeff n (S * T) * z ^ n := by
    intro n
    calc
      ∑ k ∈ Finset.range (n + 1), (coeff k S * z ^ k) * (coeff (n - k) T * z ^ (n - k))
          = ∑ k ∈ Finset.range (n + 1), (coeff k S * coeff (n - k) T) * z ^ n := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            calc
              (coeff k S * z ^ k) * (coeff (n - k) T * z ^ (n - k))
                  = z ^ k * (z ^ (n - k) * (coeff k S * coeff (n - k) T)) := by
                      ac_rfl
              _ = z ^ n * (coeff k S * coeff (n - k) T) := by
                      calc
                        z ^ k * (z ^ (n - k) * (coeff k S * coeff (n - k) T))
                            = (z ^ k * z ^ (n - k)) * (coeff k S * coeff (n - k) T) := by
                                ac_rfl
                        _ = z ^ n * (coeff k S * coeff (n - k) T) := by
                                rw [← pow_add, Nat.add_sub_of_le hk']
              _ = (coeff k S * coeff (n - k) T) * z ^ n := by
                      ac_rfl
      _ = (∑ k ∈ Finset.range (n + 1), coeff k S * coeff (n - k) T) * z ^ n := by
            rw [Finset.sum_mul]
      _ = coeff n (S * T) * z ^ n := by
            have hsum :
                ∑ k ∈ Finset.range (n + 1), coeff k S * coeff (n - k) T =
                  ∑ p ∈ Finset.antidiagonal n, coeff p.1 S * coeff p.2 T :=
              (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun k l ↦ coeff k S * coeff l T) n).symm
            rw [hsum, PowerSeries.coeff_mul]
  calc
    (S * T).sum z = ∑' n, coeff n (S * T) * z ^ n := by
      simp [PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul]
    _ = ∑' n,
        ∑ k ∈ Finset.range (n + 1), (coeff k S * z ^ k) * (coeff (n - k) T * z ^ (n - k)) := by
      refine tsum_congr ?_
      intro n
      symm
      exact hterm n
    _ = (∑' n, coeff n S * z ^ n) * ∑' n, coeff n T * z ^ n := by
      exact (hasSum_sum_range_mul_of_summable_norm' hS_norm hS hT_norm hT).tsum_eq
    _ = S.sum z * T.sum z := by
      simp [PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul]
