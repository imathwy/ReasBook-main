import DifferentialForms_Cartan_1970.cartan.IV.section13.«0007_Proposition_3_I»
import DifferentialForms_Cartan_1970.cartan.IV.section13.«0008_Definition_IV_1_extra_5»
import DifferentialForms_Cartan_1970.cartan.I.section02.«0013_Proposition_7_1»

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling:
-- * primary domain: analytic statements about two-variable formal power series
-- * source-facing owners reused here: `formalSeriesConvergenceDomain`, `coeffXY`, `sumXY`
-- * core/canonical owners underneath: `MvPowerSeries`, `MvPowerSeries.aeval`,
--   `MvPowerSeries.partialDerivative`
-- * layer for this file: source-facing theorem statements built directly from the chapter bridges,
--   with no parallel wrapper around the derivative owner
--
-- This proposition reuses the chapter owners
-- `formalSeriesConvergenceDomain`, `MvPowerSeries.sumXY`, `MvPowerSeries.coeffXY`,
-- and the source-facing partial-derivative operator `MvPowerSeries.partialDerivative`
-- through the notation `∂X`.

universe u

open MvPowerSeries
open FormalMultilinearSeries
open scoped MvPowerSeries ENNReal

section SliceHelpers

variable {𝕜 : Type u} [RCLike 𝕜]
variable (S : 𝕜⟦X,Y⟧)

/-- Helper for Proposition 3.2: the fixed-`Y` scalar slice coefficients of a two-variable formal
power series. -/
noncomputable def x_slice_coeff (z₂ : 𝕜) (p : ℕ) : 𝕜 :=
  ∑' q, coeffXY S p q * z₂ ^ q

/-- Helper for Proposition 3.2: the fixed-`Y` normal-majorant coefficients used to control the
slice series in the `X`-direction. -/
noncomputable def x_majorant_coeff (R₂ : ℝ) (p : ℕ) : ℝ :=
  ∑' q, ‖coeffXY S p q‖ * R₂ ^ q

/-- Helper for Proposition 3.2: differentiating with respect to `X` shifts the `X`-coefficient
index in the source-facing `coeffXY` notation. -/
lemma coeffXY_partialDerivativeX (p q : ℕ) :
    coeffXY (∂X S) p q = ((p + 1 : ℕ) : 𝕜) * coeffXY S (p + 1) q := by
  -- Rewrite the source-facing coefficient in terms of the canonical finitely supported index.
  simp [coeffXY, MvPowerSeries.partialDerivative, coeff_apply, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 3.2: positive `X`-radius in the two-variable convergence locus gives
summability of each fixed-`X` normal-majorant slice in the `Y`-direction. -/
lemma summable_y_majorant_slice_of_mem_formalSeriesConvergenceLocus
    {R₁ R₂ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY S))
    (hR₁ : 0 < R₁) :
    ∀ p, Summable (fun q ↦ ‖coeffXY S p q‖ * R₂ ^ q) := by
  -- Split the nonnegative double series into its fiberwise `Y`-slices and divide out the fixed
  -- positive factor `R₁ ^ p`.
  rcases (mem_formalSeriesConvergenceLocus_iff (coeffXY S) (R₁, R₂)).1 hR with
    ⟨hR₁_nonneg, hR₂_nonneg, hsum⟩
  have hnonneg :
      0 ≤ fun n : ℕ × ℕ ↦ ‖coeffXY S n.1 n.2‖ * R₁ ^ n.1 * R₂ ^ n.2 := by
    intro n
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (pow_nonneg hR₁_nonneg _))
      (pow_nonneg hR₂_nonneg _)
  have hsplits := (summable_prod_of_nonneg hnonneg).1 hsum
  intro p
  have hp :
      Summable (fun q ↦ ‖coeffXY S p q‖ * R₁ ^ p * R₂ ^ q) := hsplits.1 p
  have hp' :
      Summable (fun q ↦ (‖coeffXY S p q‖ * R₂ ^ q) * R₁ ^ p) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hp
  exact (summable_mul_right_iff (pow_ne_zero _ hR₁.ne')).1 hp'

/-- Helper for Proposition 3.2: positive `X`-radius in the two-variable convergence locus makes
the scalar `X`-majorant series summable at that radius. -/
lemma summable_x_majorant_mul_pow_of_mem_formalSeriesConvergenceLocus
    {R₁ R₂ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY S))
    (hR₁ : 0 < R₁) :
    Summable (fun p ↦ x_majorant_coeff S R₂ p * R₁ ^ p) := by
  -- First decompose the double majorant into fiberwise sums, then rewrite each fiber as the
  -- scalar coefficient `x_majorant_coeff`.
  rcases (mem_formalSeriesConvergenceLocus_iff (coeffXY S) (R₁, R₂)).1 hR with
    ⟨hR₁_nonneg, hR₂_nonneg, hsum⟩
  have hnonneg :
      0 ≤ fun n : ℕ × ℕ ↦ ‖coeffXY S n.1 n.2‖ * R₁ ^ n.1 * R₂ ^ n.2 := by
    intro n
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (pow_nonneg hR₁_nonneg _))
      (pow_nonneg hR₂_nonneg _)
  have hsplits := (summable_prod_of_nonneg hnonneg).1 hsum
  have hslice := summable_y_majorant_slice_of_mem_formalSeriesConvergenceLocus (S := S) hR hR₁
  refine hsplits.2.congr ?_
  intro p
  calc
    (∑' q, ‖coeffXY S p q‖ * R₁ ^ p * R₂ ^ q)
        = ∑' q, (‖coeffXY S p q‖ * R₂ ^ q) * R₁ ^ p := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ = x_majorant_coeff S R₂ p * R₁ ^ p := by
          simpa [x_majorant_coeff] using (hslice p).tsum_mul_right (R₁ ^ p)

/-- Helper for Proposition 3.2: every `Y`-majorant coefficient is nonnegative. -/
lemma x_majorant_coeff_nonneg {R₂ : ℝ} (hR₂ : 0 ≤ R₂) (p : ℕ) :
    0 ≤ x_majorant_coeff S R₂ p := by
  -- The majorant is the sum of nonnegative real terms.
  exact tsum_nonneg fun q ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hR₂ _)

/-- Helper for Proposition 3.2: along a fixed `Y`-slice inside the convergence locus, the
coefficient series in the `Y`-direction converges absolutely. -/
lemma summable_x_slice_row_of_mem_formalSeriesConvergenceLocus
    {R₁ R₂ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY S))
    (hR₁ : 0 < R₁)
    {z₂ : 𝕜}
    (hz₂ : ‖z₂‖ < R₂)
    (p : ℕ) :
    Summable (fun q ↦ coeffXY S p q * z₂ ^ q) := by
  -- Dominate the slice by the corresponding nonnegative `Y`-majorant row.
  have hmajorant :=
    summable_y_majorant_slice_of_mem_formalSeriesConvergenceLocus (S := S) hR hR₁ p
  have habs : Summable (fun q ↦ ‖coeffXY S p q * z₂ ^ q‖) := by
    refine Summable.of_nonneg_of_le (fun q ↦ norm_nonneg _) ?_ hmajorant
    intro q
    have hpow : ‖z₂‖ ^ q ≤ R₂ ^ q :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hz₂) q
    calc
      ‖coeffXY S p q * z₂ ^ q‖ = ‖coeffXY S p q‖ * ‖z₂‖ ^ q := by
        simp [norm_mul, norm_pow]
      _ ≤ ‖coeffXY S p q‖ * R₂ ^ q := by
        exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  simpa using habs.of_norm

/-- Helper for Proposition 3.2: the fixed-`Y` slice coefficients are bounded by the corresponding
`Y`-majorant coefficients. -/
lemma norm_x_slice_coeff_le_x_majorant_coeff_of_mem_formalSeriesConvergenceLocus
    {R₁ R₂ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY S))
    (hR₁ : 0 < R₁)
    {z₂ : 𝕜}
    (hz₂ : ‖z₂‖ < R₂)
    (p : ℕ) :
    ‖x_slice_coeff S z₂ p‖ ≤ x_majorant_coeff S R₂ p := by
  -- Sum the absolute values termwise and compare with the normal majorant row.
  have hslice :=
    summable_x_slice_row_of_mem_formalSeriesConvergenceLocus (S := S) hR hR₁ hz₂ p
  have hmajorant :=
    summable_y_majorant_slice_of_mem_formalSeriesConvergenceLocus (S := S) hR hR₁ p
  calc
    ‖x_slice_coeff S z₂ p‖ = ‖∑' q, coeffXY S p q * z₂ ^ q‖ := by
      simp [x_slice_coeff]
    _ ≤ ∑' q, ‖coeffXY S p q * z₂ ^ q‖ := by
      exact norm_tsum_le_tsum_norm hslice.norm
    _ ≤ ∑' q, ‖coeffXY S p q‖ * R₂ ^ q := by
      exact hslice.norm.tsum_le_tsum
        (fun q ↦ by
          have hpow : ‖z₂‖ ^ q ≤ R₂ ^ q :=
            pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hz₂) q
          calc
            ‖coeffXY S p q * z₂ ^ q‖ = ‖coeffXY S p q‖ * ‖z₂‖ ^ q := by
              simp [norm_mul, norm_pow]
            _ ≤ ‖coeffXY S p q‖ * R₂ ^ q := by
              exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _))
        hmajorant
    _ = x_majorant_coeff S R₂ p := by
      simp [x_majorant_coeff]

/-- Helper for Proposition 3.2: the fixed-`R₂` majorant coefficients of `∂X S` are the scalar
derived coefficients of the fixed-`R₂` majorant sequence of `S`. -/
lemma x_majorant_coeff_partialDerivativeX_eq_ofScalarsDerivCoeff
    (R₂ : ℝ)
    (p : ℕ) :
    x_majorant_coeff (∂X S) R₂ p = ofScalarsDerivCoeff (x_majorant_coeff S R₂) p := by
  -- Pull the constant derivative factor through the `Y`-majorant sum.
  calc
    x_majorant_coeff (∂X S) R₂ p
        = ∑' q, ((p + 1 : ℕ) : ℝ) * (‖coeffXY S (p + 1) q‖ * R₂ ^ q) := by
            rw [x_majorant_coeff]
            refine tsum_congr fun q ↦ ?_
            calc
              ‖coeffXY (∂X S) p q‖ * R₂ ^ q
                  = ‖((p + 1 : ℕ) : 𝕜) * coeffXY S (p + 1) q‖ * R₂ ^ q := by
                      rw [coeffXY_partialDerivativeX]
              _ = (((p + 1 : ℕ) : ℝ) * ‖coeffXY S (p + 1) q‖) * R₂ ^ q := by
                    have hnorm :
                        ‖((p + 1 : ℕ) : 𝕜) * coeffXY S (p + 1) q‖ =
                          ((p + 1 : ℕ) : ℝ) * ‖coeffXY S (p + 1) q‖ := by
                      rw [norm_mul, RCLike.norm_natCast]
                    rw [hnorm]
              _ = ((p + 1 : ℕ) : ℝ) * (‖coeffXY S (p + 1) q‖ * R₂ ^ q) := by
                    ring
    _ = ((p + 1 : ℕ) : ℝ) * x_majorant_coeff S R₂ (p + 1) := by
          rw [tsum_mul_left]
          simp [x_majorant_coeff]
    _ = ofScalarsDerivCoeff (x_majorant_coeff S R₂) p := by
          simp [ofScalarsDerivCoeff]

/-- Helper for Proposition 3.2: every fixed `Y`-slice inside the convergence locus has scalar
radius at least the `X`-radius of that locus point. -/
lemma x_slice_radius_ge_of_mem_formalSeriesConvergenceLocus
    {R₁ R₂ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY S))
    {z₂ : 𝕜}
    (hz₂ : ‖z₂‖ < R₂) :
    ENNReal.ofReal R₁ ≤ (ofScalars 𝕜 (x_slice_coeff S z₂)).radius := by
  -- Reduce the radius bound to summability of the slice coefficients against `R₁ ^ p`.
  rcases (mem_formalSeriesConvergenceLocus_iff (coeffXY S) (R₁, R₂)).1 hR with
    ⟨hR₁_nonneg, hR₂_nonneg, -⟩
  by_cases hR₁ : 0 < R₁
  · have hmajorant :=
        summable_x_majorant_mul_pow_of_mem_formalSeriesConvergenceLocus (S := S) hR hR₁
    have hslice :
        Summable (fun p ↦ ‖x_slice_coeff S z₂ p‖ * R₁ ^ p) := by
      refine Summable.of_nonneg_of_le
        (fun p ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hR₁.le _)) ?_ hmajorant
      intro p
      exact mul_le_mul_of_nonneg_right
        (norm_x_slice_coeff_le_x_majorant_coeff_of_mem_formalSeriesConvergenceLocus
          (S := S) hR hR₁ hz₂ p)
        (pow_nonneg hR₁.le _)
    -- The scalar slice now falls under the one-variable Cauchy-Hadamard radius bound.
    have howner :
        Summable
          (fun p ↦ ‖(ofScalars 𝕜 (x_slice_coeff S z₂)) p‖ * R₁ ^ p) := by
      simpa [FormalMultilinearSeries.ofScalars_norm] using hslice
    let r₁ : NNReal := ⟨R₁, hR₁.le⟩
    have hradius :
        (r₁ : ENNReal) ≤ (ofScalars 𝕜 (x_slice_coeff S z₂)).radius :=
      (ofScalars 𝕜 (x_slice_coeff S z₂)).le_radius_of_summable_norm
        (r := r₁) howner
    have hr₁_cast : ENNReal.ofReal R₁ = (r₁ : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hR₁.le]
      rfl
    exact hr₁_cast.symm ▸ hradius
  · have hR₁_eq : R₁ = 0 := le_antisymm (le_of_not_gt hR₁) hR₁_nonneg
    -- If the locus `X`-radius is zero, the radius inequality is tautological.
    simp [hR₁_eq]

/-- Helper for Proposition 3.2: shrinking only the `X`-radius inside a convergence-locus point of
`S` produces a convergence-locus point for `∂X S`. -/
lemma formalSeriesConvergenceLocus_partialDerivativeX_of_mem
    {R₁ R₂ ρ₁ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY S))
    (hρ₁_pos : 0 < ρ₁)
    (hρ₁_lt : ρ₁ < R₁) :
    (ρ₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY (∂X S)) := by
  -- Apply Proposition 7.1 to the fixed-`R₂` majorant sequence and then rebuild the double series.
  rcases (mem_formalSeriesConvergenceLocus_iff (coeffXY S) (R₁, R₂)).1 hR with
    ⟨hR₁_nonneg, hR₂_nonneg, -⟩
  have hR₁_pos : 0 < R₁ := lt_trans hρ₁_pos hρ₁_lt
  have hbase_sum :=
    summable_x_majorant_mul_pow_of_mem_formalSeriesConvergenceLocus (S := S) hR hR₁_pos
  have hbase_radius :
      ENNReal.ofReal R₁ ≤ (ofScalars ℝ (x_majorant_coeff S R₂)).radius := by
    -- The original majorant sequence converges at `R₁`, so its scalar radius is at least `R₁`.
    have hbase_sum_norm :
        Summable (fun p ↦ ‖x_majorant_coeff S R₂ p‖ * R₁ ^ p) := by
      refine hbase_sum.congr ?_
      intro p
      rw [Real.norm_eq_abs, abs_of_nonneg (x_majorant_coeff_nonneg (S := S) hR₂_nonneg p)]
    have howner :
        Summable
          (fun p ↦ ‖(ofScalars ℝ (x_majorant_coeff S R₂)) p‖ * R₁ ^ p) := by
      simpa [FormalMultilinearSeries.ofScalars_norm] using hbase_sum_norm
    let r₁ : NNReal := ⟨R₁, hR₁_pos.le⟩
    have hradius :
        (r₁ : ENNReal) ≤ (ofScalars ℝ (x_majorant_coeff S R₂)).radius :=
      (ofScalars ℝ (x_majorant_coeff S R₂)).le_radius_of_summable_norm
        (r := r₁) howner
    have hr₁_cast : ENNReal.ofReal R₁ = (r₁ : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hR₁_pos.le]
      rfl
    exact hr₁_cast.symm ▸ hradius
  have hderiv_radius :
      ENNReal.ofReal R₁ ≤
        (ofScalars ℝ (ofScalarsDerivCoeff (x_majorant_coeff S R₂))).radius := by
    rw [← ofScalars_radius_eq_radius_derivCoeff (𝕜 := ℝ) (a := x_majorant_coeff S R₂)]
    exact hbase_radius
  let r₁ : NNReal := ⟨R₁, hR₁_pos.le⟩
  let rρ : NNReal := ⟨ρ₁, hρ₁_pos.le⟩
  have hρ₁_lt_radius :
      (rρ : ENNReal) <
        (ofScalars ℝ (ofScalarsDerivCoeff (x_majorant_coeff S R₂))).radius := by
    have hρ_lt_r₁ : (rρ : ENNReal) < (r₁ : ENNReal) := by
      exact_mod_cast hρ₁_lt
    have hderiv_radius' :
        (r₁ : ENNReal) ≤
          (ofScalars ℝ (ofScalarsDerivCoeff (x_majorant_coeff S R₂))).radius := by
      have hr₁_cast : ENNReal.ofReal R₁ = (r₁ : ENNReal) := by
        rw [ENNReal.ofReal_eq_coe_nnreal hR₁_pos.le]
        rfl
      exact hr₁_cast ▸ hderiv_radius
    exact lt_of_lt_of_le hρ_lt_r₁ hderiv_radius'
  have houter :
      Summable (fun p ↦ x_majorant_coeff (∂X S) R₂ p * ρ₁ ^ p) := by
    -- Proposition 7.1 upgrades the original majorant radius to the derived one.
    have howner :
        Summable
          (fun p ↦
            ‖(ofScalars ℝ (ofScalarsDerivCoeff (x_majorant_coeff S R₂))) p‖ * ρ₁ ^ p) := by
      simpa using
        (ofScalars ℝ (ofScalarsDerivCoeff (x_majorant_coeff S R₂))).summable_norm_mul_pow
          (r := rρ) (by simpa [rρ, ENNReal.ofReal_eq_coe_nnreal] using hρ₁_lt_radius)
    refine howner.congr ?_
    intro p
    have hnonneg :
        0 ≤ x_majorant_coeff (∂X S) R₂ p :=
      x_majorant_coeff_nonneg (S := ∂X S) hR₂_nonneg p
    calc
      ‖(ofScalars ℝ (ofScalarsDerivCoeff (x_majorant_coeff S R₂))) p‖ * ρ₁ ^ p
          = ‖ofScalarsDerivCoeff (x_majorant_coeff S R₂) p‖ * ρ₁ ^ p := by
              simp
      _ = ‖x_majorant_coeff (∂X S) R₂ p‖ * ρ₁ ^ p := by
            rw [← x_majorant_coeff_partialDerivativeX_eq_ofScalarsDerivCoeff (S := S) R₂ p]
      _ = x_majorant_coeff (∂X S) R₂ p * ρ₁ ^ p := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hrows :
      ∀ p, Summable (fun q ↦ ‖coeffXY (∂X S) p q‖ * R₂ ^ q) := by
    intro p
    -- Each derived `Y`-row is a constant multiple of the corresponding original row.
    have hbase :=
      summable_y_majorant_slice_of_mem_formalSeriesConvergenceLocus (S := S) hR hR₁_pos (p + 1)
    simpa [coeffXY_partialDerivativeX, norm_mul, mul_assoc, mul_left_comm, mul_comm] using
      hbase.mul_left ‖((p + 1 : ℕ) : 𝕜)‖
  have hweighted_rows :
      ∀ p, Summable (fun q ↦ ‖coeffXY (∂X S) p q‖ * ρ₁ ^ p * R₂ ^ q) := by
    intro p
    -- Weight each convergent derived row by the fixed factor `ρ₁ ^ p`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hrows p).mul_right (ρ₁ ^ p)
  have hweighted_outer :
      Summable (fun p ↦ ∑' q, ‖coeffXY (∂X S) p q‖ * ρ₁ ^ p * R₂ ^ q) := by
    -- The weighted row sums are exactly the reconstructed derived majorant series.
    refine houter.congr ?_
    intro p
    symm
    calc
      (∑' q, ‖coeffXY (∂X S) p q‖ * ρ₁ ^ p * R₂ ^ q)
          = ∑' q, (‖coeffXY (∂X S) p q‖ * R₂ ^ q) * ρ₁ ^ p := by
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ = x_majorant_coeff (∂X S) R₂ p * ρ₁ ^ p := by
            simpa [x_majorant_coeff] using (hrows p).tsum_mul_right (ρ₁ ^ p)
  -- The nonnegative rectangular series now satisfies the locus definition for `∂X S`.
  rw [mem_formalSeriesConvergenceLocus_iff]
  refine ⟨hρ₁_pos.le, hR₂_nonneg, ?_⟩
  exact
    (summable_prod_of_nonneg
      (fun n : ℕ × ℕ ↦
        mul_nonneg
          (mul_nonneg (norm_nonneg _) (pow_nonneg hρ₁_pos.le _))
          (pow_nonneg hR₂_nonneg _))).2
      ⟨hweighted_rows, hweighted_outer⟩

/-- Helper for Proposition 3.2: the source-facing double sum agrees with the scalar slice sum once
the fixed `Y`-coordinate stays inside a convergence-locus witness. -/
lemma sumXY_eq_ofScalarsSum_x_slice_coeff_of_mem_formalSeriesConvergenceLocus
    {R₁ R₂ : ℝ}
    (hR : (R₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY S))
    {w z₂ : 𝕜}
    (hw : ‖w‖ < R₁)
    (hz₂ : ‖z₂‖ < R₂) :
    sumXY S (w, z₂) = ofScalarsSum (x_slice_coeff S z₂) w := by
  -- Compare the double sum with the iterated slice sum via absolute convergence and Fubini.
  rcases (mem_formalSeriesConvergenceLocus_iff (coeffXY S) (R₁, R₂)).1 hR with
    ⟨hR₁_nonneg, hR₂_nonneg, hsumR⟩
  have hR₁_pos : 0 < R₁ := lt_of_le_of_lt (norm_nonneg _) hw
  have hrect_norm :
      Summable (fun n : ℕ × ℕ ↦ ‖coeffXY S n.1 n.2 * w ^ n.1 * z₂ ^ n.2‖) := by
    refine hsumR.of_nonneg_of_le (fun n ↦ norm_nonneg _) ?_
    intro n
    have hpow₁ : ‖w‖ ^ n.1 ≤ R₁ ^ n.1 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hw) n.1
    have hpow₂ : ‖z₂‖ ^ n.2 ≤ R₂ ^ n.2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hz₂) n.2
    calc
      ‖coeffXY S n.1 n.2 * w ^ n.1 * z₂ ^ n.2‖
          = ‖coeffXY S n.1 n.2‖ * ‖w‖ ^ n.1 * ‖z₂‖ ^ n.2 := by
              simp [norm_mul, norm_pow, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ ‖coeffXY S n.1 n.2‖ * R₁ ^ n.1 * R₂ ^ n.2 := by
            gcongr
  have hrect :
      Summable (fun n : ℕ × ℕ ↦ coeffXY S n.1 n.2 * w ^ n.1 * z₂ ^ n.2) := by
    simpa using hrect_norm.of_norm
  have hrow_base :
      ∀ p, Summable (fun q ↦ coeffXY S p q * z₂ ^ q) := by
    intro p
    exact
      summable_x_slice_row_of_mem_formalSeriesConvergenceLocus (S := S) hR hR₁_pos hz₂ p
  have hrows :
      ∀ p, Summable (fun q ↦ coeffXY S p q * w ^ p * z₂ ^ q) := by
    intro p
    -- Each row of the rectangular family is a fixed scalar multiple of the slice row.
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hrow_base p).mul_right (w ^ p)
  calc
    sumXY S (w, z₂)
        = ∑' n : ℕ × ℕ, coeffXY S n.1 n.2 * w ^ n.1 * z₂ ^ n.2 := by
            rfl
    _ = ∑' p : ℕ, ∑' q : ℕ, coeffXY S p q * w ^ p * z₂ ^ q := by
          exact hrect.tsum_prod' hrows
    _ = ∑' p : ℕ, (∑' q : ℕ, coeffXY S p q * z₂ ^ q) * w ^ p := by
          refine tsum_congr fun p ↦ ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using (hrow_base p).tsum_mul_right (w ^ p)
    _ = ∑' p : ℕ, x_slice_coeff S z₂ p * w ^ p := by
          simp [x_slice_coeff]
    _ = ofScalarsSum (x_slice_coeff S z₂) w := by
          simp [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul]

/-- Helper for Proposition 3.2: the fixed-`Y` slice of `∂X S` is exactly the textbook-derived
scalar coefficient sequence of the fixed-`Y` slice of `S`. -/
lemma ofScalarsDerivCoeff_sliceCoeff_eq_sliceCoeff_partialDerivativeX
    (z₂ : 𝕜) :
    ofScalarsDerivCoeff (x_slice_coeff S z₂) = x_slice_coeff (∂X S) z₂ := by
  -- Rewrite both sides coefficientwise using the source-facing derivative coefficient formula.
  funext p
  calc
    ofScalarsDerivCoeff (x_slice_coeff S z₂) p
        = ((p + 1 : ℕ) : 𝕜) * x_slice_coeff S z₂ (p + 1) := by
            simp [ofScalarsDerivCoeff]
    _ = ((p + 1 : ℕ) : 𝕜) * ∑' q, coeffXY S (p + 1) q * z₂ ^ q := by
          rfl
    _ = ∑' q, (((p + 1 : ℕ) : 𝕜) * coeffXY S (p + 1) q) * z₂ ^ q := by
          rw [← tsum_mul_left]
          refine tsum_congr fun q ↦ ?_
          ring
    _ = x_slice_coeff (∂X S) z₂ p := by
          simp [x_slice_coeff, coeffXY_partialDerivativeX, mul_assoc]

/-- Helper for Proposition 3.2: a point of the convergence domain yields a larger point of the
convergence locus with positive `X`-radius. -/
lemma exists_gt_mem_formalSeriesConvergenceLocus_of_mem_domain
    {z₁ z₂ : 𝕜}
    (hz : (‖z₁‖, ‖z₂‖) ∈ formalSeriesConvergenceDomain (coeffXY S)) :
    ∃ R₁ > ‖z₁‖, ∃ R₂ > ‖z₂‖, (R₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY S) := by
  -- This is the standard interior-to-larger-locus conversion from Proposition 2.I.
  rcases
      (mem_formalSeriesConvergenceDomain_iff_exists_gt_mem_formalSeriesConvergenceLocus
        (coeffXY S) ‖z₁‖ ‖z₂‖).1 hz with
    ⟨-, -, R₁, hR₁, R₂, hR₂, hR⟩
  exact ⟨R₁, hR₁, R₂, hR₂, hR⟩

end SliceHelpers

section ConvergenceDomain

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Proposition 3.2 (1): over the real or complex scalar fields of the source text, differentiating
with respect to `X` preserves convergence on the original domain. The reverse inclusion is false
for series independent of `X`, so the source-faithful statement is this inclusion rather than
equality of domains. -/
theorem formalSeriesConvergenceDomain_partialDerivativeX_eq
    (S : 𝕜⟦X,Y⟧) :
    formalSeriesConvergenceDomain (coeffXY S) ⊆
      formalSeriesConvergenceDomain (coeffXY (∂X S)) := by
  intro r hr
  -- Move from the domain point to a larger locus point where the derivative majorant can be built.
  rcases
      (mem_formalSeriesConvergenceDomain_iff_exists_gt_mem_formalSeriesConvergenceLocus
        (coeffXY S) r.1 r.2).1 hr with
    ⟨hr₁_pos, hr₂_pos, R₁, hr₁_lt_R₁, R₂, hr₂_lt_R₂, hR⟩
  let ρ₁ : ℝ := (r.1 + R₁) / 2
  have hρ₁_pos : 0 < ρ₁ := by
    dsimp [ρ₁]
    linarith
  have hr₁_lt_ρ₁ : r.1 < ρ₁ := by
    dsimp [ρ₁]
    linarith
  have hρ₁_lt_R₁ : ρ₁ < R₁ := by
    dsimp [ρ₁]
    linarith
  have hR_deriv :
      (ρ₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY (∂X S)) :=
    formalSeriesConvergenceLocus_partialDerivativeX_of_mem (S := S) hR hρ₁_pos hρ₁_lt_R₁
  -- Re-enter the convergence domain of `∂X S` using Proposition 2.I with the shrunk `X`-radius.
  rw [mem_formalSeriesConvergenceDomain_iff_exists_gt_mem_formalSeriesConvergenceLocus]
  exact ⟨hr₁_pos, hr₂_pos, ρ₁, hr₁_lt_ρ₁, R₂, hr₂_lt_R₂, hR_deriv⟩

end ConvergenceDomain

section HasDerivAt

variable {𝕜 : Type u} [RCLike 𝕜]
variable (S : 𝕜⟦X,Y⟧)

/-- Proposition 3.2 (2): at every point whose coordinatewise absolute values lie in the domain of
convergence of `S`, the summed series of `∂S/∂X` is the partial derivative of the summed series
of `S` with respect to the real or complex variable `z₁`. -/
theorem hasDerivAt_double_power_series_sum_partialDerivativeX
    {z₁ z₂ : 𝕜}
    (hz : (‖z₁‖, ‖z₂‖) ∈ formalSeriesConvergenceDomain (coeffXY S)) :
    HasDerivAt
      (fun w ↦ sumXY S (w, z₂))
      (sumXY (∂X S) (z₁, z₂))
      z₁ := by
  -- Extract a larger convergence-locus box around `(z₁, z₂)` to control both slice sums.
  rcases exists_gt_mem_formalSeriesConvergenceLocus_of_mem_domain (S := S) hz with
    ⟨R₁, hz₁_lt_R₁, R₂, hz₂_lt_R₂, hR⟩
  have hslice_radius :
      ENNReal.ofReal R₁ ≤ (ofScalars 𝕜 (x_slice_coeff S z₂)).radius :=
    x_slice_radius_ge_of_mem_formalSeriesConvergenceLocus (S := S) hR hz₂_lt_R₂
  have hz₁_lt_slice_radius :
      ENNReal.ofReal ‖z₁‖ < (ofScalars 𝕜 (x_slice_coeff S z₂)).radius := by
    -- The fixed `Y`-slice is a scalar series whose radius contains the whole `X`-interval.
    let rz₁ : NNReal := ‖z₁‖₊
    let r₁ : NNReal := ⟨R₁, le_trans (norm_nonneg _) (le_of_lt hz₁_lt_R₁)⟩
    have hlt : (rz₁ : ENNReal) < (r₁ : ENNReal) := by
      exact_mod_cast hz₁_lt_R₁
    have hrz₁_cast : ENNReal.ofReal ‖z₁‖ = (rz₁ : ENNReal) := by
      change ENNReal.ofReal ‖z₁‖ = (‖z₁‖₊ : ENNReal)
      rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
      rfl
    have hr₁_cast : (r₁ : ENNReal) = ENNReal.ofReal R₁ := by
      rw [ENNReal.ofReal_eq_coe_nnreal (le_trans (norm_nonneg _) (le_of_lt hz₁_lt_R₁))]
      rfl
    calc
      ENNReal.ofReal ‖z₁‖ = (rz₁ : ENNReal) := hrz₁_cast
      _ < (r₁ : ENNReal) := hlt
      _ = ENNReal.ofReal R₁ := hr₁_cast
      _ ≤ (ofScalars 𝕜 (x_slice_coeff S z₂)).radius := hslice_radius
  have hslice_deriv :
      HasDerivAt (ofScalarsSum (x_slice_coeff S z₂))
        (ofScalarsSum (ofScalarsDerivCoeff (x_slice_coeff S z₂)) z₁) z₁ :=
    hasDerivAt_ofScalarsSum_eq_ofScalarsSum_derivCoeff
      (𝕜 := 𝕜) (x_slice_coeff S z₂) hz₁_lt_slice_radius
  have hnear :
      ∀ᶠ w in nhds z₁, ‖w‖ < R₁ := by
    -- A small neighborhood of `z₁` stays inside the same `X`-radius witness.
    have hδ : 0 < R₁ - ‖z₁‖ := by
      linarith
    filter_upwards [Metric.ball_mem_nhds z₁ hδ] with w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    calc
      ‖w‖ = ‖(w - z₁) + z₁‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z₁‖ + ‖z₁‖ := norm_add_le _ _
      _ < (R₁ - ‖z₁‖) + ‖z₁‖ := by
            simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_right hw ‖z₁‖
      _ = R₁ := by ring
  have hsum_eq :
      (fun w ↦ sumXY S (w, z₂)) =ᶠ[nhds z₁] fun w ↦ ofScalarsSum (x_slice_coeff S z₂) w := by
    -- Near `z₁`, the two-variable sum is exactly the scalar slice sum.
    filter_upwards [hnear] with w hw
    exact
      sumXY_eq_ofScalarsSum_x_slice_coeff_of_mem_formalSeriesConvergenceLocus
        (S := S) hR hw hz₂_lt_R₂
  let ρ₁ : ℝ := (‖z₁‖ + R₁) / 2
  have hρ₁_pos : 0 < ρ₁ := by
    dsimp [ρ₁]
    linarith [norm_nonneg z₁]
  have hz₁_lt_ρ₁ : ‖z₁‖ < ρ₁ := by
    dsimp [ρ₁]
    linarith
  have hρ₁_lt_R₁ : ρ₁ < R₁ := by
    dsimp [ρ₁]
    linarith
  have hR_deriv :
      (ρ₁, R₂) ∈ formalSeriesConvergenceLocus (coeffXY (∂X S)) :=
    formalSeriesConvergenceLocus_partialDerivativeX_of_mem (S := S) hR hρ₁_pos hρ₁_lt_R₁
  have hvalue :
      ofScalarsSum (ofScalarsDerivCoeff (x_slice_coeff S z₂)) z₁ =
        sumXY (∂X S) (z₁, z₂) := by
    -- Rewrite the derivative coefficients as the fixed-`Y` slice of `∂X S`.
    calc
      ofScalarsSum (ofScalarsDerivCoeff (x_slice_coeff S z₂)) z₁
          = ofScalarsSum (x_slice_coeff (∂X S) z₂) z₁ := by
              rw [ofScalarsDerivCoeff_sliceCoeff_eq_sliceCoeff_partialDerivativeX (S := S)]
      _ = sumXY (∂X S) (z₁, z₂) := by
            symm
            exact
              sumXY_eq_ofScalarsSum_x_slice_coeff_of_mem_formalSeriesConvergenceLocus
                (S := ∂X S) hR_deriv hz₁_lt_ρ₁ hz₂_lt_R₂
  have hmain :
      HasDerivAt (fun w ↦ sumXY S (w, z₂))
        (ofScalarsSum (ofScalarsDerivCoeff (x_slice_coeff S z₂)) z₁) z₁ := by
    -- Transport Proposition 7.1 back from the scalar slice to the source-facing two-variable sum.
    exact hslice_deriv.congr_of_eventuallyEq hsum_eq
  simpa [hvalue] using hmain

end HasDerivAt
