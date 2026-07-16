import DifferentialForms_Cartan_1970.cartan.IV.section13.«0003_Definition_IV_1_extra_3»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: this lemma uses the chapter owner declaration
-- `formalSeriesConvergenceLocus` from
-- `IV/section13/0003_Definition_IV_1_extra_3.lean`.

universe u

variable {𝕜 : Type u} [SeminormedAddCommGroup 𝕜]

/-- Helper for Lemma IV.1-extra-4: the ratio of a nonnegative radius to a strictly larger radius
lies in the interval `[0, 1)`. -/
lemma radius_ratio_nonneg_lt_one {r r' : ℝ} (hr_nonneg : 0 ≤ r) (hr : r < r') :
    0 ≤ r / r' ∧ r / r' < 1 := by
  -- The larger radius is positive, so division preserves both nonnegativity and the strict bound.
  have hr'_pos : 0 < r' := lt_of_le_of_lt hr_nonneg hr
  constructor
  · exact div_nonneg hr_nonneg hr'_pos.le
  · exact (div_lt_one hr'_pos).2 hr

/-- Helper for Lemma IV.1-extra-4: each weighted term at the smaller radii is dominated by the
corresponding coefficient bound times a double geometric factor. -/
lemma weighted_term_le_double_geometric_majorant
    (a : ℕ → ℕ → 𝕜) {M r₁ r₂ r₁' r₂' : ℝ}
    (hr₁_nonneg : 0 ≤ r₁) (hr₂_nonneg : 0 ≤ r₂)
    (hM : ∀ p q : ℕ, ‖a p q‖ * r₁' ^ p * r₂' ^ q ≤ M)
    (hr₁ : r₁ < r₁') (hr₂ : r₂ < r₂') (p q : ℕ) :
    ‖a p q‖ * r₁ ^ p * r₂ ^ q ≤ M * ((r₁ / r₁') ^ p * (r₂ / r₂') ^ q) := by
  -- The larger radii are positive because the smaller radii are assumed nonnegative.
  have hr₁'_pos : 0 < r₁' := lt_of_le_of_lt hr₁_nonneg hr₁
  have hr₂'_pos : 0 < r₂' := lt_of_le_of_lt hr₂_nonneg hr₂
  have hr₁_pow : r₁ ^ p = (r₁ / r₁') ^ p * r₁' ^ p := by
    -- First divide the `p`-th power by `r₁' ^ p`, then multiply back.
    calc
      r₁ ^ p = (r₁ ^ p / r₁' ^ p) * r₁' ^ p := by
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hr₁'_pos.ne')]
      _ = (r₁ / r₁') ^ p * r₁' ^ p := by rw [div_pow]
  have hr₂_pow : r₂ ^ q = (r₂ / r₂') ^ q * r₂' ^ q := by
    -- The same argument applies to the second radius.
    calc
      r₂ ^ q = (r₂ ^ q / r₂' ^ q) * r₂' ^ q := by
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hr₂'_pos.ne')]
      _ = (r₂ / r₂') ^ q * r₂' ^ q := by rw [div_pow]
  have hratio_nonneg : 0 ≤ (r₁ / r₁') ^ p * (r₂ / r₂') ^ q := by
    -- The geometric factor is nonnegative because each ratio is nonnegative.
    refine mul_nonneg ?_ ?_
    · exact pow_nonneg (div_nonneg hr₁_nonneg hr₁'_pos.le) _
    · exact pow_nonneg (div_nonneg hr₂_nonneg hr₂'_pos.le) _
  -- Multiply the large-radius bound by the nonnegative geometric factor and rewrite.
  calc
    ‖a p q‖ * r₁ ^ p * r₂ ^ q
        = (‖a p q‖ * r₁' ^ p * r₂' ^ q) * ((r₁ / r₁') ^ p * (r₂ / r₂') ^ q) := by
          rw [hr₁_pow, hr₂_pow]
          ac_rfl
    _ ≤ M * ((r₁ / r₁') ^ p * (r₂ / r₂') ^ q) :=
      mul_le_mul_of_nonneg_right (hM p q) hratio_nonneg

/-- Helper for Lemma IV.1-extra-4: the double geometric majorant attached to the radius ratios is
summable over `ℕ × ℕ`. -/
lemma summable_double_geometric_majorant {M r₁ r₂ r₁' r₂' : ℝ}
    (hr₁_nonneg : 0 ≤ r₁) (hr₂_nonneg : 0 ≤ r₂)
    (hr₁ : r₁ < r₁') (hr₂ : r₂ < r₂') :
    Summable (fun n : ℕ × ℕ ↦ M * ((r₁ / r₁') ^ n.1 * (r₂ / r₂') ^ n.2)) := by
  -- Each one-variable geometric series is summable because its ratio lies in `[0, 1)`.
  have hratio₁ : 0 ≤ r₁ / r₁' ∧ r₁ / r₁' < 1 := radius_ratio_nonneg_lt_one hr₁_nonneg hr₁
  have hratio₂ : 0 ≤ r₂ / r₂' ∧ r₂ / r₂' < 1 := radius_ratio_nonneg_lt_one hr₂_nonneg hr₂
  have hgeom₁ : Summable (fun n : ℕ ↦ (r₁ / r₁') ^ n) :=
    summable_geometric_of_lt_one hratio₁.1 hratio₁.2
  have hgeom₂ : Summable (fun n : ℕ ↦ (r₂ / r₂') ^ n) :=
    summable_geometric_of_lt_one hratio₂.1 hratio₂.2
  have hgeom : Summable (fun n : ℕ × ℕ ↦ (r₁ / r₁') ^ n.1 * (r₂ / r₂') ^ n.2) :=
    hgeom₁.mul_of_nonneg hgeom₂
      (fun n ↦ pow_nonneg hratio₁.1 _)
      (fun n ↦ pow_nonneg hratio₂.1 _)
  -- Scaling a summable family by the constant `M` preserves summability.
  exact hgeom.mul_left M

/-- Lemma IV.1-extra-4: if the coefficients satisfy a uniform bound after weighting by the larger
radii `r₁'`, `r₂'`, then the associated formal double series is normally convergent on the
smaller closed polydisc `‖z₁‖ ≤ r₁`, `‖z₂‖ ≤ r₂`; in the local API, this is recorded as
`(r₁, r₂)` belonging to the convergence locus. -/
theorem formalSeriesConvergenceLocus_of_bounded_coefficients
    (a : ℕ → ℕ → 𝕜) {M r₁ r₂ r₁' r₂' : ℝ}
    (hr₁_nonneg : 0 ≤ r₁) (hr₂_nonneg : 0 ≤ r₂)
    (hM : ∀ p q : ℕ, ‖a p q‖ * r₁' ^ p * r₂' ^ q ≤ M)
    (hr₁ : r₁ < r₁') (hr₂ : r₂ < r₂') :
    (r₁, r₂) ∈ formalSeriesConvergenceLocus a := by
  -- Unfold the convergence locus and reduce to summability of the defining positive-term series.
  rw [mem_formalSeriesConvergenceLocus_iff]
  refine ⟨hr₁_nonneg, hr₂_nonneg, ?_⟩
  have hmajorant :
      Summable (fun n : ℕ × ℕ ↦ M * ((r₁ / r₁') ^ n.1 * (r₂ / r₂') ^ n.2)) :=
    summable_double_geometric_majorant (M := M) hr₁_nonneg hr₂_nonneg hr₁ hr₂
  -- Apply the comparison test with the textbook double geometric progression.
  refine Summable.of_nonneg_of_le ?_ ?_ hmajorant
  · intro n
    -- Every weighted norm term is nonnegative.
    refine mul_nonneg ?_ (pow_nonneg hr₂_nonneg _)
    exact mul_nonneg (norm_nonneg _) (pow_nonneg hr₁_nonneg _)
  · intro n
    -- The pointwise majorization comes from the large-radius coefficient bound.
    exact weighted_term_le_double_geometric_majorant
      (a := a) hr₁_nonneg hr₂_nonneg hM hr₁ hr₂ n.1 n.2
