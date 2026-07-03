import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_16
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_17

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped MeasureTheory NNReal

noncomputable section

/-- The stable Lévy density with index `α` and one-sided coefficients `c⁻`, `c⁺`. -/
def stableLevyDensity (α cMinus cPlus : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then
    cMinus * (-x) ^ (-α - 1)
  else if 0 < x then
    cPlus * x ^ (-α - 1)
  else
    0

-- Proof sketch: this is the defining piecewise formula of `stableLevyDensity`.
/-- The stable Lévy density is the textbook power-law density on the negative and positive
half-lines, and it vanishes at `0`. -/
theorem stableLevyDensity_apply (α cMinus cPlus x : ℝ) :
    stableLevyDensity α cMinus cPlus x =
      if x < 0 then
        cMinus * (-x) ^ (-α - 1)
      else if 0 < x then
        cPlus * x ^ (-α - 1)
      else
        0 := rfl

/-- The stable Lévy measure with index `α` and one-sided coefficients `c⁻`, `c⁺`. -/
noncomputable def stableLevyMeasure (α cMinus cPlus : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (stableLevyDensity α cMinus cPlus x))

-- Proof sketch: unfold `stableLevyMeasure`; it is defined by weighting Lebesgue measure with
-- `stableLevyDensity`.
/-- The stable Lévy measure is Lebesgue measure with density `stableLevyDensity α c⁻ c⁺`. -/
theorem stableLevyMeasure_def (α cMinus cPlus : ℝ) :
    stableLevyMeasure α cMinus cPlus =
      volume.withDensity (fun x ↦ ENNReal.ofReal (stableLevyDensity α cMinus cPlus x)) := rfl

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: analyze the rescaling coefficients in the broad-stability relation, show that they
-- must be of the form `n^(1 / α)`, and then deduce `α ∈ (0, 2]` from the Lévy--Khintchine
-- representation.
/-- Theorem 16.22 (1): source clause (i). A broadly stable probability law has a stability index
`α ∈ (0, 2]`. -/
theorem stable_broad_exists_index
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ) :
    ∃ α : ℝ, IsStableInBroadSenseWithIndex μ α := sorry

-- Proof sketch: when the index is `2`, the Lévy measure vanishes, so the canonical
-- Lévy--Khintchine representation reduces to the Gaussian part.
/-- Theorem 16.22 (2): source clause (ii). Stability in the broad sense with index `2` forces the
law to be Gaussian. -/
theorem stable_broad_index_two_isGaussian
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSenseWithIndex μ 2) :
    IsGaussian (μ : Measure ℝ) := sorry

/-- Admissible one-sided coefficients for a nontrivial stable Lévy measure. -/
def StableLevyCoefficients (cMinus cPlus : ℝ) : Prop :=
  0 ≤ cMinus ∧ 0 ≤ cPlus ∧ 0 < cMinus + cPlus

-- Proof sketch: identify the Lévy tails from the scaling relation, show that they are power laws
-- on `(0, ∞)` and `(-∞, 0)`, and convert those tail identities into the explicit density of `ν`.
/-- Theorem 16.22 (3): source clause (iii). For index `α ∈ (0, 2)`, every canonical triple of a
broadly stable law has the power-law Lévy density `c⁻(-x)^(-α-1)` on `(-∞,0)` and
`c⁺x^(-α-1)` on `(0,∞)`. -/
theorem stable_broad_levyMeasure_eq_stableLevyMeasure
    {μ : ProbabilityMeasure ℝ} {α : ℝ} {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ α) (hα₂ : α < 2)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    ∃ cMinus cPlus : ℝ,
      StableLevyCoefficients cMinus cPlus ∧
        τ.ν = stableLevyMeasure α cMinus cPlus := sorry

-- Proof sketch: use the translation formula for characteristic functions to remove the centering
-- constants `dₙ`; for `α ≠ 1`, the resulting translated law satisfies the strict scaling relation.
/-- Theorem 16.22 (4): source clause (iv). If `α ≠ 1`, a suitable translation of a broadly stable
law with index `α` is strictly stable with the same index. -/
theorem stable_broad_translate_isStable_of_ne_one
    {μ : ProbabilityMeasure ℝ} {α : ℝ}
    (hμ : IsStableInBroadSenseWithIndex μ α) (hα : α ≠ 1) :
    ∃ b : ℝ, IsStableWithIndex (map μ (measurable_affineMap 1 (-b)).aemeasurable) α := sorry

-- Proof sketch: insert the explicit Lévy density from clause (iii) into the canonical
-- characteristic-function formula at `α = 1`, then compare the affine centering constants in the
-- broad-stability relation.
/-- Theorem 16.22 (5): source clause (v), first sentence. For index `α = 1`, the centering
sequence is `dₙ = (c⁺ - c⁻) n log n`. -/
theorem stable_broad_centering_eq_of_index_one
    {μ : ProbabilityMeasure ℝ} {d : ℕ+ → ℝ} {cMinus cPlus : ℝ}
    {τ : LevyKhinchinTriple}
    (hμ : ∀ n : ℕ+,
      μ ^ (n : ℕ) = map μ (measurable_affineMap (n : ℝ) (d n)).aemeasurable)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hν : τ.ν = stableLevyMeasure 1 cMinus cPlus) :
    ∀ n : ℕ+, d n = (cPlus - cMinus) * (n : ℝ) * Real.log n := sorry

-- Proof sketch: when `α = 1` and `c⁻ = c⁺`, the logarithmic centering term vanishes and the
-- canonical triple matches that of a translated Cauchy law, so the measure is Cauchy.
/-- Theorem 16.22 (6): source clause (v), second sentence. If `α = 1` and the positive and
negative Lévy-density coefficients agree, then the law is Cauchy. -/
theorem stable_broad_index_one_symmetric_isCauchy
    {μ : ProbabilityMeasure ℝ} {cMinus cPlus : ℝ}
    {τ : LevyKhinchinTriple}
    (hμ : IsStableInBroadSenseWithIndex μ 1)
    (hτ : HasLevyKhinchinRepresentation μ τ)
    (hν : τ.ν = stableLevyMeasure 1 cMinus cPlus) (hsymm : cMinus = cPlus) :
    ∃ x₀ : ℝ, ∃ γ : ℝ≥0, 0 < γ ∧ (μ : Measure ℝ) = cauchyMeasure x₀ γ := sorry

end MeasureTheory.ProbabilityMeasure
