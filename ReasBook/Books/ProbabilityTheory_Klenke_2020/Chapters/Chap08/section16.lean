import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_8_16 (from Items/Chap08) -/
open Filter MeasureTheory
open scoped MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure[mΩ] Ω}

/-- An admissible increasing integrable approximation of `X` is an increasing sequence of
integrable functions bounded below by `-X⁻` that converges pointwise to `X`. -/
def is_admissible_increasing_integrable_approximation {m : MeasurableSpace Ω} (P : Measure[m] Ω)
    (X : Ω → ℝ) (Xn : ℕ → Ω → ℝ) : Prop :=
  (∀ n, Integrable (Xn n) P) ∧
    (∀ n ω, -(X ω)⁻ ≤ Xn n ω) ∧
    Monotone Xn ∧
    ∀ ω, Tendsto (fun n ↦ Xn n ω) atTop (nhds (X ω))

/-- The lower-integrable conditional expectation is the canonical `EReal`-valued extension of
`P[X | ℱ]`, obtained from the conditional Lebesgue expectations of the positive and negative
parts. For `X⁻ ∈ L¹(P)`, it takes values in `(-∞, ∞]` almost surely. -/
/-
`MeasureTheory.condLExp` is the owner abstraction for conditional Lebesgue expectation of
nonnegative functions. `lowerCondExp` is the source-facing signed bridge used in Remark 8.16.
-/
noncomputable def lowerCondExp {m : MeasurableSpace Ω} (P : Measure[m] Ω) (ℱ : MeasurableSpace Ω)
    (X : Ω → ℝ) : Ω → EReal :=
  fun ω ↦ (P⁻[fun ω ↦ ENNReal.ofReal (X ω) | ℱ] ω : EReal) -
    P⁻[fun ω ↦ ENNReal.ofReal (-X ω) | ℱ] ω

section Probability

variable [IsProbabilityMeasure P] {ℱ : MeasurableSpace Ω}

-- Proof sketch: `P⁻[fun ω ↦ ENNReal.ofReal (-X ω) | ℱ]` is finite almost surely when `X⁻` is
-- integrable, so the difference defining `lowerCondExp P ℱ X` cannot be `⊥` except on a
-- `P`-null set.
/-- If `X⁻` is integrable, then the lower conditional expectation takes values in `(-∞, ∞]`
almost surely. -/
theorem lowerCondExp_ne_bot_ae (hℱ : ℱ ≤ mΩ)
    {X : Ω → ℝ} (hXneg : Integrable (fun ω ↦ (X ω)⁻) P) :
    ∀ᵐ ω ∂P, lowerCondExp P ℱ X ω ≠ ⊥ := sorry

-- Proof sketch: apply monotone convergence to the nonnegative conditional expectations of the
-- shifted truncations `Xn + X⁻`, identify the limiting positive and negative parts via `condLExp`,
-- and then subtract the common `condLExp` term coming from `X⁻`.
/-- Remark 8.16: if `X⁻ ∈ L¹(P)`, then the lower conditional expectation of `X` with respect to
`ℱ` is the almost-sure monotone limit of the conditional expectations of any admissible increasing
integrable approximation of `X`. Consequently, this limit does not depend on the chosen
approximation sequence. -/
theorem ae_tendsto_condExp_of_admissible_increasing_integrable_approximation
    (hℱ : ℱ ≤ mΩ) {X : Ω → ℝ} (hXneg : Integrable (fun ω ↦ (X ω)⁻) P) {Xn : ℕ → Ω → ℝ}
    (hXn : is_admissible_increasing_integrable_approximation P X Xn) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (P[Xn n | ℱ] ω : EReal)) atTop
      (nhds (lowerCondExp P ℱ X ω)) := sorry

-- Proof sketch: decompose `X = X⁺ - X⁻`, identify the two pieces with `condLExp` through
-- `toReal_condLExp`, and use linearity of `condExp` on the integrable positive and negative parts.
/-- For integrable `X`, the lower-integrable extension agrees almost surely with the usual
conditional expectation from Definition 8.11. -/
theorem lowerCondExp_ae_eq_condExp (hℱ : ℱ ≤ mΩ) {X : Ω → ℝ} (hX : Integrable X P) :
    lowerCondExp P ℱ X =ᵐ[P] fun ω ↦ (P[X | ℱ] ω : EReal) := sorry

-- Proof sketch: if `X ≤ Y` almost surely and `X⁻ ∈ L¹(P)`, then also `Y⁻ ∈ L¹(P)`. Compare the
-- positive and negative `condLExp` terms using `condLExp_mono` and subtract the common finite
-- negative-part correction.
/-- The lower-integrable extension of conditional expectation is monotone with respect to
almost-sure order. -/
theorem lowerCondExp_mono (hℱ : ℱ ≤ mΩ)
    {X Y : Ω → ℝ} (hXneg : Integrable (fun ω ↦ (X ω)⁻) P) (hXY : X ≤ᵐ[P] Y) :
    lowerCondExp P ℱ X ≤ᵐ[P] lowerCondExp P ℱ Y := sorry

end Probability
