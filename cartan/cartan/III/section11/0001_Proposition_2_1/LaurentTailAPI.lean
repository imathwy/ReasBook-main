import Mathlib
import cartan.III.section10.«frozen_0003_Theorem_III_4_extra_3»

open Metric

noncomputable section

/-- Helper for Proposition 2.1: on the annulus, the nonnegative Laurent tail is pointwise
summable. -/
lemma laurent_nonneg_part_summable
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {z : ℂ} (hz : z ∈ complexOpenAnnulus ρ₂ ρ₁) :
    Summable (fun n : ℕ ↦ a (n : ℤ) * z ^ n) := by
  -- Restrict the annulus Laurent sum to the nonnegative indices.
  have hzsum : Summable (fun n : ℤ ↦ a n * z ^ n) := ha.summable hz
  simpa using hzsum.comp_injective Nat.cast_injective

/-- Helper for Proposition 2.1: on the annulus, the negative Laurent tail is pointwise
summable. -/
lemma laurent_neg_part_summable
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    {z : ℂ} (hz : z ∈ complexOpenAnnulus ρ₂ ρ₁) :
    Summable (fun n : ℕ ↦ a (Int.negSucc n) * z ^ (Int.negSucc n)) := by
  -- Restrict the annulus Laurent sum to the negative indices.
  have hzsum : Summable (fun n : ℤ ↦ a n * z ^ n) := ha.summable hz
  simpa using hzsum.comp_injective (@Int.negSucc.inj)

/-- Helper for Proposition 2.1: at a nonzero point, the negative Laurent tail rewrites as `z⁻¹`
times an ordinary power series in `z⁻¹`. -/
lemma laurent_neg_part_eq_inv_mul_powerSeries
    {a : ℤ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    (∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n)) =
      z⁻¹ * ∑' n : ℕ, a (Int.negSucc n) * (z⁻¹) ^ n := by
  -- Rewrite each negative Laurent monomial using `zpow_negSucc`, then factor out the common
  -- leading `z⁻¹`.
  calc
    (∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n))
      = ∑' n : ℕ, z⁻¹ * (a (Int.negSucc n) * (z⁻¹) ^ n) := by
          refine tsum_congr ?_
          intro n
          calc
            a (Int.negSucc n) * z ^ (Int.negSucc n)
                = a (Int.negSucc n) * ((z ^ (n + 1))⁻¹) := by
                    rw [zpow_negSucc]
            _ = a (Int.negSucc n) * ((z ^ n * z)⁻¹) := by
                  rw [pow_succ]
            _ = a (Int.negSucc n) * (z⁻¹ * (z ^ n)⁻¹) := by
                  rw [mul_inv_rev]
            _ = z⁻¹ * (a (Int.negSucc n) * (z ^ n)⁻¹) := by
                  ac_rfl
            _ = z⁻¹ * (a (Int.negSucc n) * (z⁻¹) ^ n) := by
                  rw [inv_pow]
    _ = z⁻¹ * ∑' n : ℕ, a (Int.negSucc n) * (z⁻¹) ^ n := by
          rw [tsum_mul_left]

/-- Helper for Proposition 2.1: every point of the smaller disc admits an intermediate circle
that still lies inside the original annulus. -/
lemma exists_intermediate_radius_for_ball_point
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ₁) :
    ∃ R : NNReal, max ρ₂ ‖z‖₊ < R ∧ R < ρ₁ := by
  -- The disc bound puts `‖z‖` below `ρ₁`, so there is room for an intermediate radius.
  have hzlt : ‖z‖₊ < ρ₁ := by
    exact_mod_cast (by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hz : ‖z‖ < (ρ₁ : ℝ))
  have hmax : max ρ₂ ‖z‖₊ < ρ₁ := max_lt_iff.mpr ⟨hρ, hzlt⟩
  exact exists_between hmax

/-- Helper for Proposition 2.1: every exterior point admits an intermediate inner radius strictly
between the boundary circle and the point norm. -/
lemma exists_intermediate_radius_for_exterior_point
    {ρ₂ : NNReal} {z : ℂ} (hz : z ∈ (closedBall (0 : ℂ) ρ₂)ᶜ) :
    ∃ r : NNReal, ρ₂ < r ∧ r < ‖z‖₊ := by
  -- The exterior condition is exactly the strict inequality `ρ₂ < ‖z‖`.
  have hzgt : ρ₂ < ‖z‖₊ := by
    have hznot : ¬ ‖z‖ ≤ (ρ₂ : ℝ) := by
      simpa [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    exact_mod_cast lt_of_not_ge hznot
  exact exists_between hzgt

/-- Helper for Proposition 2.1: for an exterior point one can choose an intermediate inner radius
that also stays below the outer annulus radius. -/
lemma exists_intermediate_radius_for_exterior_point_lt_upper
    {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) {z : ℂ} (hz : z ∈ (closedBall (0 : ℂ) ρ₂)ᶜ) :
    ∃ r : NNReal, ρ₂ < r ∧ r < ρ₁ ∧ r < ‖z‖₊ := by
  -- Choose `r` between `ρ₂` and the smaller of `ρ₁` and `‖z‖`.
  have hzgt : ρ₂ < ‖z‖₊ := by
    rcases exists_intermediate_radius_for_exterior_point (ρ₂ := ρ₂) hz with ⟨r, hρ₂r, hrz⟩
    exact lt_trans hρ₂r hrz
  rcases exists_between (lt_min hρ hzgt) with ⟨r, hρ₂r, hrmin⟩
  exact ⟨r, hρ₂r, lt_of_lt_of_le hrmin (min_le_left _ _), lt_of_lt_of_le hrmin (min_le_right _ _)⟩

/-- Helper for Proposition 2.1: on the annulus, the Laurent sum splits into its nonnegative and
negative tails. -/
lemma laurent_split_eqOn_annulus
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} {f : ℂ → ℂ}
    (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁)
    (hEq : Set.EqOn f (fun z ↦ ∑' n : ℤ, a n * z ^ n) (complexOpenAnnulus ρ₂ ρ₁)) :
    Set.EqOn f
      (fun z ↦ (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n))
      (complexOpenAnnulus ρ₂ ρ₁) := by
  intro z hz
  have hnonneg := laurent_nonneg_part_summable ha hz
  have hneg := laurent_neg_part_summable ha hz
  let fNat : ℕ → ℂ := fun n ↦ a (n : ℤ) * z ^ n
  let gNeg : ℕ → ℂ := fun n ↦ a (Int.negSucc n) * z ^ (Int.negSucc n)
  have hrec : (fun n : ℤ ↦ Int.rec fNat gNeg n) = fun n : ℤ ↦ a n * z ^ n := by
    -- `Int.rec` is exactly the partition of `ℤ` into nonnegative and negative indices.
    funext n
    cases n <;> rfl
  calc
    f z = ∑' n : ℤ, a n * z ^ n := hEq hz
    _ = ∑' n : ℤ, Int.rec fNat gNeg n := by simpa [hrec]
    _ = (∑' n : ℕ, fNat n) + ∑' n : ℕ, gNeg n := by
          exact tsum_int_rec hnonneg hneg
    _ = (∑' n : ℕ, a (n : ℤ) * z ^ n) + ∑' n : ℕ, a (Int.negSucc n) * z ^ (Int.negSucc n) := by
          rfl

/-- Helper for Proposition 2.1: the nonnegative Laurent tail is the disc-analytic branch from the
textbook Laurent decomposition. -/
lemma laurent_nonneg_part_analyticOnNhd
    {a : ℤ → ℂ} {ρ₂ ρ₁ : NNReal} (hρ : ρ₂ < ρ₁) (ha : IsLaurentSeriesOnAnnulus a ρ₂ ρ₁) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' n : ℕ, a (n : ℤ) * z ^ n) (ball (0 : ℂ) ρ₁) := by
  -- Route correction: this support file now exports the owner Laurent-tail API into the package
  -- namespace used by Proposition 2.1, but the Cauchy-power-series proof still needs to be moved
  -- over from the local section-10 owner file.
  -- TODO: copy the owner proof that chooses an intermediate circle, identifies the Cauchy power
  -- series with the nonnegative Laurent coefficients, and then transfers analyticity from that
  -- circle model to the whole smaller disc.
  sorry
