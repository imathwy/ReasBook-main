import Mathlib
import ProbabilityTheory_Klenke_2020.Chap16.Definition_16_1
import ProbabilityTheory_Klenke_2020.Chap16.Definition_16_20
import ProbabilityTheory_Klenke_2020.Chap16.Theorem_16_17
import ProbabilityTheory_Klenke_2020.Chap16.Theorem_16_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

variable {μ : ProbabilityMeasure ℝ} {τ : LevyKhinchinTriple}
variable {a d : ℕ+ → ℝ} {α cMinus cPlus : ℝ}

section BroadStableScaling

variable (hτ : HasLevyKhinchinRepresentation μ τ)
variable (ha : ∀ n : ℕ+, 0 < a n)
variable (hscale : ∀ n : ℕ+,
  μ ^ (n : ℕ) = μ.map (measurable_affineMap (a n) (d n)).aemeasurable)

-- Proof sketch: compare the Gaussian coefficients in the Lévy--Khinchin triples of the `n`th
-- convolution power and of the affine image `aₙ X + dₙ`, and use uniqueness of the canonical
-- triple.
/-- Lemma 16.25 (1): for a broadly stable law whose `n`th convolution powers are realized by the
affine scalings `x ↦ aₙ x + dₙ`, the Gaussian coefficient in the Lévy--Khinchin triple satisfies
`((aₙ)^2 - n) σ² = 0`. -/
theorem stableBroad_canonicalTriple_gaussianScaling
    :
    ∀ n : ℕ+, ((a n) ^ (2 : ℕ) - (n : ℝ)) * τ.sigma2 = 0 := sorry

-- Proof sketch: compare the Lévy measures in the Lévy--Khinchin triples of the `n`th convolution
-- power and of the affine image `aₙ X + dₙ`, then use uniqueness of the canonical triple.
/-- Lemma 16.25 (2): under the same broad-stability scaling relation, the Lévy measure scales by
`n • ν = ν ∘ m_(aₙ)⁻¹`, written in Lean as a pushforward under `x ↦ aₙ x`. -/
theorem stableBroad_canonicalTriple_levyMeasureScaling
    :
    ∀ n : ℕ+, (n : ℕ) • τ.ν = Measure.map (fun x : ℝ ↦ a n * x) τ.ν := sorry

-- Proof sketch: if `τ.ν = 0`, the law is not a Dirac mass, so the canonical triple must have
-- positive Gaussian coefficient; combine this with part (1) to solve for `aₙ`.
/-- Lemma 16.25 (3): if the Lévy measure in the canonical triple vanishes, then the broad-stable
scaling factors are `aₙ = n^(1 / 2)`. -/
theorem stableBroad_zeroLevyMeasure_scale_eq
    (hnot_dirac : ∀ x : ℝ, μ ≠ diracProba x) (hν : τ.ν = 0) :
    ∀ n : ℕ+, a n = (n : ℝ) ^ (1 / (2 : ℝ)) := sorry

-- Proof sketch: with `τ.ν = 0`, the drift term in `map_affine_hasLevyKhinchinRepresentation`
-- simplifies to `aₙ b + dₙ`; compare it with the drift `n b` of the `n`-fold convolution power and
-- substitute the scale from part (3).
/-- Lemma 16.25 (4): if the Lévy measure in the canonical triple vanishes, then the centering
constants satisfy `dₙ = b (n - n^(1 / 2))`. -/
theorem stableBroad_zeroLevyMeasure_centering_eq
    (hnot_dirac : ∀ x : ℝ, μ ≠ diracProba x) (hν : τ.ν = 0) :
    ∀ n : ℕ+, d n = τ.b * ((n : ℝ) - (n : ℝ) ^ (1 / (2 : ℝ))) := sorry

end BroadStableScaling

section StableLevyCentering

variable (hτ : HasLevyKhinchinRepresentation μ τ)
variable (hscale : ∀ n : ℕ+,
  μ ^ (n : ℕ) =
    μ.map (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable)
variable (hcoeff : StableLevyCoefficients cMinus cPlus)
variable (hν : τ.ν = stableLevyMeasure α cMinus cPlus)

-- Proof sketch: use the explicit power-law form of the stable Lévy measure with admissible
-- coefficients to evaluate the drift correction term in
-- `map_affine_hasLevyKhinchinRepresentation`, then compare the resulting affine-law drift with the
-- drift of the `n`-fold convolution power.
/-- Lemma 16.25 (5): if `α ∈ (0, 2)`, the canonical broad-stability scaling relation holds, and
the Lévy measure is the stable Lévy measure with admissible coefficients `c⁻`, `c⁺`, then for
`α ≠ 1` the centering constants satisfy the explicit formula from `(16.25)`. -/
theorem stableBroad_stableLevy_centering_eq_of_ne_one
    (hα : α ∈ Set.Ioo (0 : ℝ) 2) (hα_ne : α ≠ 1) :
    ∀ n : ℕ+,
      d n =
        (τ.b + (cPlus - cMinus) / (α - 1)) * ((n : ℝ) - (n : ℝ) ^ (1 / α)) := sorry

-- Proof sketch: in the case `α = 1`, the same drift-correction integral becomes logarithmic;
-- inserting the explicit stable Lévy measure with admissible coefficients yields the factor
-- `(c⁺ - c⁻) n log n`.
/-- Lemma 16.25 (6): in the same admissible stable-Lévy-measure setting, if `α = 1` then the
centering constants satisfy `dₙ = (c⁺ - c⁻) n log n`. -/
theorem stableBroad_stableLevy_centering_eq_of_eq_one
    (hα_eq : α = 1) :
    ∀ n : ℕ+, d n = (cPlus - cMinus) * (n : ℝ) * Real.log (n : ℝ) := sorry

end StableLevyCentering

end MeasureTheory.ProbabilityMeasure
