import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section02.«frozen_0004_Definition_I_2_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open PowerSeries
open scoped BigOperators NNReal ENNReal PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Proof sketch: specialize `FormalMultilinearSeries.min_radius_le_radius_add` to the analytic
-- series attached to `S` and `T`, then compare the common lower bound `ρ` with the minimum of
-- the two radii.
/-- Proposition 4.1 (1): if two scalar power series have radius of convergence at least `ρ`, then
their coefficientwise sum also has radius of convergence at least `ρ`. -/
theorem scalar_series_sum_radius_ge
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius) :
    (ρ : ℝ≥0∞) ≤ (S + T).radius := by
  calc
    (ρ : ℝ≥0∞) ≤ min S.radius T.radius := le_min hS hT
    _ ≤ ((ofScalars 𝕜 (fun n ↦ coeff n S)) + (ofScalars 𝕜 (fun n ↦ coeff n T))).radius := by
      simpa [PowerSeries.radius] using
        min_radius_le_radius_add (ofScalars 𝕜 (fun n ↦ coeff n S))
          (ofScalars 𝕜 (fun n ↦ coeff n T))
    _ = (S + T).radius := by
      have hcoeff :
          (fun n ↦ coeff n (S + T)) = (fun n ↦ coeff n S) + fun n ↦ coeff n T := by
        ext n
        simp
      rw [PowerSeries.radius, hcoeff, ofScalars_add]

/-- Helper for Cartan section02 frozen_0008_Proposition_4_1: every scalar power series is
absolutely summable on closed balls strictly inside its radius of convergence. -/
lemma summable_norm_coeff_mul_pow_of_lt_radius
    (U : 𝕜⟦X⟧) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < U.radius) :
    Summable (fun n : ℕ ↦ ‖coeff n U‖ * (r : ℝ) ^ n) := by
  -- Rewrite the scalar series radius through the formal multilinear series owner.
  simpa [PowerSeries.radius] using
    (FormalMultilinearSeries.summable_norm_mul_pow
      (ofScalars 𝕜 fun n ↦ coeff n U) hr)

/-- Helper for Cartan section02 frozen_0008_Proposition_4_1: the weighted coefficient of a product
is bounded by its finite Cauchy majorant. -/
lemma coeff_mul_mul_pow_le_cauchy_majorant
    (S T : 𝕜⟦X⟧) (r : ℝ≥0) (n : ℕ) :
    ‖coeff n (S * T)‖ * (r : ℝ) ^ n ≤
      ∑ k ∈ Finset.range (n + 1),
        (‖coeff k S‖ * (r : ℝ) ^ k) * (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k)) := by
  have hr_nonneg : 0 ≤ (r : ℝ) := by
    exact_mod_cast r.2
  -- Expand the coefficient of the product into the finite Cauchy product.
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

/-- Helper for Cartan section02 frozen_0008_Proposition_4_1: the weighted Cauchy majorant is
summable whenever the chosen radius lies strictly inside both convergence radii. -/
lemma summable_cauchy_majorant_of_lt_radius
    (S T : 𝕜⟦X⟧) (r : ℝ≥0)
    (hS : (r : ℝ≥0∞) < S.radius) (hT : (r : ℝ≥0∞) < T.radius) :
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
    -- These weighted coefficients are nonnegative reals, so the norm leaves them unchanged.
    refine Summable.of_nonneg_of_le ?_ ?_ hS_sum
    · intro n
      exact norm_nonneg _
    · intro n
      have hnonneg : 0 ≤ ‖coeff n S‖ * (r : ℝ) ^ n :=
        mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hT_norm :
      Summable (fun n : ℕ ↦ ‖‖coeff n T‖ * (r : ℝ) ^ n‖) := by
    -- The same positivity argument applies to the second weighted series.
    refine Summable.of_nonneg_of_le ?_ ?_ hT_sum
    · intro n
      exact norm_nonneg _
    · intro n
      have hnonneg : 0 ≤ ‖coeff n T‖ * (r : ℝ) ^ n :=
        mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  -- Invoke the standard Cauchy-product summability theorem on the weighted norm sequences.
  exact (hasSum_sum_range_mul_of_summable_norm hS_norm hT_norm).summable

-- Proof sketch: for every `r < ρ`, the absolute-value coefficient series for `a` and `b` are
-- summable; apply the Cauchy-product summability theorem to the coefficient sequence of `S * T`,
-- then use
-- `le_radius_of_summable` to deduce the same lower bound for the product radius.
/-- Proposition 4.1 (2): if two scalar power series have radius of convergence at least `ρ`, then
their Cauchy product also has radius of convergence at least `ρ`. -/
theorem scalar_series_cauchy_product_radius_ge
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius) :
    (ρ : ℝ≥0∞) ≤ (S * T).radius := by
  -- Follow the source proof: control the weighted product coefficients by the Cauchy majorant.
  refine ENNReal.le_of_forall_nnreal_lt ?_
  intro r hr
  have hrrho : (r : ℝ≥0∞) < (ρ : ℝ≥0∞) := by
    exact_mod_cast hr
  have hrS : (r : ℝ≥0∞) < S.radius :=
    lt_of_lt_of_le hrrho hS
  have hrT : (r : ℝ≥0∞) < T.radius :=
    lt_of_lt_of_le hrrho hT
  have hr_nonneg : 0 ≤ (r : ℝ) := by
    exact_mod_cast r.2
  have hmajorant :
      Summable (fun n ↦ ∑ k ∈ Finset.range (n + 1),
        (‖coeff k S‖ * (r : ℝ) ^ k) * (‖coeff (n - k) T‖ * (r : ℝ) ^ (n - k))) :=
    summable_cauchy_majorant_of_lt_radius S T r hrS hrT
  have hproduct :
      Summable (fun n : ℕ ↦ ‖coeff n (S * T)‖ * (r : ℝ) ^ n) := by
    -- The pointwise Cauchy-majorant estimate turns the product coefficients into a summable series.
    refine Summable.of_nonneg_of_le ?_ ?_ hmajorant
    · intro n
      exact mul_nonneg (norm_nonneg _) (pow_nonneg hr_nonneg n)
    · intro n
      exact coeff_mul_mul_pow_le_cauchy_majorant S T r n
  have hproduct_owner :
      Summable (fun n : ℕ ↦ ‖ofScalars 𝕜 (fun m ↦ coeff m (S * T)) n‖ * (r : ℝ) ^ n) := by
    -- Rephrase the scalar estimate for the multilinear owner appearing in `PowerSeries.radius`.
    simpa using hproduct
  -- Translate weighted summability back into the radius lower bound.
  change (r : ℝ≥0∞) ≤ (ofScalars 𝕜 fun n ↦ coeff n (S * T)).radius
  exact (ofScalars 𝕜 fun n ↦ coeff n (S * T)).le_radius_of_summable_norm hproduct_owner

/-- Helper for Cartan section02 frozen_0008_Proposition_4_1: on a closed disk `‖z‖ ≤ r`,
weighted coefficient summability implies absolute summability of the evaluated scalar series. -/
lemma summable_norm_eval_of_weighted_coeff
    (A : 𝕜⟦X⟧) (r : ℝ≥0) (z : 𝕜)
    (hA : Summable (fun n : ℕ => ‖coeff n A‖ * (r : ℝ) ^ n))
    (hz : ‖z‖₊ ≤ r) :
    Summable (fun n : ℕ => ‖coeff n A * z ^ n‖) := by
  -- Compare the evaluation termwise with the weighted majorant on the closed disk.
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

/-- Helper for Cartan section02 frozen_0008_Proposition_4_1: evaluating two summable scalar
power series at a common point commutes with addition. -/
theorem sum_add_eq
    (S T : 𝕜⟦X⟧) (z : 𝕜)
    (hS : Summable (fun n ↦ coeff n S * z ^ n))
    (hT : Summable (fun n ↦ coeff n T * z ^ n)) :
    (S + T).sum z = S.sum z + T.sum z := by
  -- Sum the coefficientwise identity termwise once both series are summable.
  simpa [PowerSeries.sum, ofScalars_sum_eq, smul_eq_mul, add_mul] using
    (Summable.tsum_add hS hT)

/-- Helper for Cartan section02 frozen_0008_Proposition_4_1: absolutely summable scalar power
series satisfy the Cauchy-product evaluation formula. -/
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
    -- Normalize the finite Cauchy product by collecting the powers of `z`.
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
  -- Evaluate the product series by the Cauchy-product theorem for absolutely summable series.
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

section Complete

variable [CompleteSpace 𝕜]

-- Proof sketch: inside the common convergence disk, both scalar series are summable absolutely, so
-- the series attached to `S + T` may be summed termwise and identified with the sum of the two
-- evaluated series.
/-- Proposition 4.1 (3): for `‖z‖ < ρ`, evaluating the coefficientwise sum series at `z` gives the
sum of the two scalar series evaluated at `z`. -/
theorem scalar_series_sum_eval_eq_add
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius)
    {z : 𝕜} (hz : ‖z‖₊ < ρ) :
    PowerSeries.sum (S + T) z = S.sum z + T.sum z := by
  have hzρ : ((‖z‖₊ : ℝ≥0) : ℝ≥0∞) < (ρ : ℝ≥0∞) := by
    exact_mod_cast hz
  have hzS : ((‖z‖₊ : ℝ≥0) : ℝ≥0∞) < S.radius :=
    lt_of_lt_of_le hzρ hS
  have hzT : ((‖z‖₊ : ℝ≥0) : ℝ≥0∞) < T.radius :=
    lt_of_lt_of_le hzρ hT
  have hS_norm :
      Summable (fun n : ℕ ↦ ‖coeff n S * z ^ n‖) :=
    summable_norm_eval_of_weighted_coeff S ‖z‖₊ z
      (summable_norm_coeff_mul_pow_of_lt_radius S hzS) le_rfl
  have hT_norm :
      Summable (fun n : ℕ ↦ ‖coeff n T * z ^ n‖) :=
    summable_norm_eval_of_weighted_coeff T ‖z‖₊ z
      (summable_norm_coeff_mul_pow_of_lt_radius T hzT) le_rfl
  have hS_term : Summable (fun n ↦ coeff n S * z ^ n) :=
    hS_norm.of_norm
  have hT_term : Summable (fun n ↦ coeff n T * z ^ n) :=
    hT_norm.of_norm
  -- Once both evaluation series are summable, sum termwise.
  simpa using sum_add_eq S T z hS_term hT_term

-- Proof sketch: for `‖z‖ < ρ`, the two scalar series are absolutely convergent; apply the Cauchy
-- product theorem to the coefficient sequence of `S * T` and then identify the resulting sum with
-- the value of `PowerSeries.sum`.
/-- Cartan section02 frozen_0008_Proposition_4_1. Proposition 4.1 (4): for `‖z‖ < ρ`, evaluating
the Cauchy-product series at `z` gives the product of the two scalar series evaluated at `z`. -/
theorem scalar_series_cauchy_product_eval_eq_mul
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius)
    {z : 𝕜} (hz : ‖z‖₊ < ρ) :
    PowerSeries.sum (S * T) z = S.sum z * T.sum z := by
  have hzρ : ((‖z‖₊ : ℝ≥0) : ℝ≥0∞) < (ρ : ℝ≥0∞) := by
    exact_mod_cast hz
  have hzS : ((‖z‖₊ : ℝ≥0) : ℝ≥0∞) < S.radius :=
    lt_of_lt_of_le hzρ hS
  have hzT : ((‖z‖₊ : ℝ≥0) : ℝ≥0∞) < T.radius :=
    lt_of_lt_of_le hzρ hT
  have hS_norm :
      Summable (fun n : ℕ ↦ ‖coeff n S * z ^ n‖) :=
    summable_norm_eval_of_weighted_coeff S ‖z‖₊ z
      (summable_norm_coeff_mul_pow_of_lt_radius S hzS) le_rfl
  have hT_norm :
      Summable (fun n : ℕ ↦ ‖coeff n T * z ^ n‖) :=
    summable_norm_eval_of_weighted_coeff T ‖z‖₊ z
      (summable_norm_coeff_mul_pow_of_lt_radius T hzT) le_rfl
  have hS_term : Summable (fun n ↦ coeff n S * z ^ n) :=
    hS_norm.of_norm
  have hT_term : Summable (fun n ↦ coeff n T * z ^ n) :=
    hT_norm.of_norm
  -- Apply the Cauchy-product theorem once both scalar evaluation series are absolutely summable.
  simpa using sum_mul_eq_mul_sum S T z hS_norm hS_term hT_norm hT_term

end Complete

section Complete

variable [CompleteSpace 𝕜]

/-- Helper for Cartan section02 frozen_0008_Proposition_4_1: package the four conclusions of
Proposition 4.1 into a single theorem. -/
theorem scalarSeriesAddMulRadiusAndEval
    (S T : 𝕜⟦X⟧) (ρ : ℝ≥0)
    (hS : (ρ : ℝ≥0∞) ≤ S.radius)
    (hT : (ρ : ℝ≥0∞) ≤ T.radius) :
    (ρ : ℝ≥0∞) ≤ (S + T).radius ∧
      (ρ : ℝ≥0∞) ≤ (S * T).radius ∧
      (∀ ⦃z : 𝕜⦄, ‖z‖₊ < ρ → PowerSeries.sum (S + T) z = S.sum z + T.sum z) ∧
      ∀ ⦃z : 𝕜⦄, ‖z‖₊ < ρ → PowerSeries.sum (S * T) z = S.sum z * T.sum z := by
  -- Package the four local statements into the single item-level theorem expected by the pipeline.
  refine
    ⟨scalar_series_sum_radius_ge S T ρ hS hT,
      scalar_series_cauchy_product_radius_ge S T ρ hS hT, ?_, ?_⟩
  · intro z hz
    exact scalar_series_sum_eval_eq_add S T ρ hS hT hz
  · intro z hz
    exact scalar_series_cauchy_product_eval_eq_mul S T ρ hS hT hz

end Complete
