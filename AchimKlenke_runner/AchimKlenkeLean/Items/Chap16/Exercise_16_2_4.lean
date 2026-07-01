import Mathlib
import AchimKlenkeLean.Items.Chap16.Corollary_16_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The stable index determined by two power-law contributions is the smaller tail index,
truncated above by the Gaussian value `2`. -/
def heavyTailStableIndex (α β : ℝ) : ℝ :=
  min (2 : ℝ) (min (-1 - α) (-1 - β))

/-- The stable index of the textbook piecewise power-tail law. When `ρ = 0`, only the right tail
survives; when `ρ = 1`, only the left tail survives; otherwise both tails contribute and the
smaller tail index dominates, truncated above by the Gaussian value `2`. -/
def piecewisePowerTailStableIndex (α β ρ : ℝ) : ℝ :=
  if ρ = 0 then
    min (2 : ℝ) (-1 - β)
  else if ρ = 1 then
    min (2 : ℝ) (-1 - α)
  else
    heavyTailStableIndex α β

/-- The textbook piecewise power-law density with left exponent `α`, right exponent `β`, and left
tail mass parameter `ρ`, normalized so that the left and right tails have masses `ρ` and
`1 - ρ`. -/
def piecewisePowerTailDensity (α β ρ : ℝ) : ℝ → ENNReal :=
  fun x ↦
    if x < -1 then
      ENNReal.ofReal (ρ * (-(1 + α)) * Real.rpow |x| α)
    else if 1 < x then
      ENNReal.ofReal ((1 - ρ) * (-(1 + β)) * Real.rpow x β)
    else
      0

/-- The textbook two-sided piecewise power-tail measure on `ℝ`. -/
def piecewisePowerTailMeasure (α β ρ : ℝ) : Measure ℝ :=
  volume.withDensity (piecewisePowerTailDensity α β ρ)

/-- For admissible exponents and mixing parameter, the textbook piecewise power-tail measure is a
probability measure. -/
theorem piecewisePowerTailMeasure_isProbabilityMeasure
    {α β ρ : ℝ} (hα : α < -1) (hβ : β < -1) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (piecewisePowerTailMeasure α β ρ) := sorry

/-- The textbook two-sided piecewise power-tail law on `ℝ`. -/
def piecewisePowerTailLaw (α β ρ : ℝ) (hα : α < -1) (hβ : β < -1)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : ProbabilityMeasure ℝ :=
  ⟨piecewisePowerTailMeasure α β ρ, piecewisePowerTailMeasure_isProbabilityMeasure hα hβ hρ⟩

/-- The normalization constant in the parity-dependent power-law distribution from the exercise.
-/
def oddEvenPowerNormConst (α β : ℝ) : ℝ :=
  (Real.rpow (2 : ℝ) α) * Complex.re (riemannZeta (-α)) +
    (1 - Real.rpow (2 : ℝ) β) * Complex.re (riemannZeta (-β))

/-- The parity-dependent power-law weights on `ℕ`, with even weights proportional to `n^α`, odd
weights proportional to `n^β`, and the exercise's normalization constant. -/
def oddEvenPowerWeight (α β : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then
    0
  else if Even n then
    (oddEvenPowerNormConst α β)⁻¹ * Real.rpow (n : ℝ) α
  else
    (oddEvenPowerNormConst α β)⁻¹ * Real.rpow (n : ℝ) β

/-- For admissible exponents, the parity-dependent power-law weights sum to `1` as an `ENNReal`
series. -/
theorem oddEvenPowerWeight_hasSum_ennreal
    {α β : ℝ} (hα : α < -1) (hβ : β < -1) :
    HasSum (fun n : ℕ ↦ ENNReal.ofReal (oddEvenPowerWeight α β n)) 1 := sorry

/-- The parity-dependent power-law distribution on `ℕ`, realized as a probability mass function.
-/
def oddEvenPowerPMF (α β : ℝ) (hα : α < -1) (hβ : β < -1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (oddEvenPowerWeight α β n),
    oddEvenPowerWeight_hasSum_ennreal hα hβ⟩

/-- The parity-dependent power-law distribution on `ℕ`, viewed as a law on `ℝ`. -/
def oddEvenPowerLaw (α β : ℝ) (hα : α < -1) (hβ : β < -1) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ⟨(oddEvenPowerPMF α β hα hβ).toMeasure, inferInstance⟩
    (measurable_of_countable fun n : ℕ ↦ (n : ℝ)).aemeasurable

-- Proof sketch: compute the left and right tails of the density, identify the dominating regularly
-- varying exponent `piecewisePowerTailStableIndex α β ρ`, and then apply the stable
-- domain-of-attraction criterion for one-dimensional laws.
/-- Exercise 16.2.4 (1): source clause (i). A real probability law with the textbook two-sided
piecewise power-law density belongs to the domain of attraction of a stable law with index
`piecewisePowerTailStableIndex α β ρ`. -/
theorem piecewisePowerTailLaw_mem_domainOfAttraction_stableWithIndex
    {α β ρ : ℝ} (hα : α < -1) (hβ : β < -1) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    IsInDomainOfAttractionOfStableWithIndex
      (piecewisePowerTailLaw α β ρ hα hβ hρ)
      (piecewisePowerTailStableIndex α β ρ) := sorry

-- Proof sketch: exponential laws have finite variance, so after centering and `√n` scaling their
-- i.i.d. sums converge to a Gaussian law; in the chapter API this means the law belongs to the
-- domain of attraction of a stable law with index `2`.
/-- Exercise 16.2.4 (2): source clause (ii). The exponential law with rate `θ > 0` belongs to the
domain of attraction of a stable law with parameter `2`. -/
theorem exponentialLaw_mem_domainOfAttraction_stableWithIndex_two {θ : ℝ} (hθ : 0 < θ) :
    IsInDomainOfAttractionOfStableWithIndex
      (⟨expMeasure θ, isProbabilityMeasure_expMeasure hθ⟩ : ProbabilityMeasure ℝ) 2 := sorry

-- Proof sketch: compare the parity-dependent tails with the corresponding regularly varying
-- sequences, identify the dominating exponent `heavyTailStableIndex α β`, and then apply the
-- one-dimensional stable domain-of-attraction criterion.
/-- Exercise 16.2.4 (3): source clause (iii). The parity-dependent power-law distribution on `ℕ`,
viewed as a law on `ℝ`, belongs to the domain of attraction of a stable law with index
`heavyTailStableIndex α β`. -/
theorem oddEvenPowerLaw_mem_domainOfAttraction_stableWithIndex
    {α β : ℝ} (hα : α < -1) (hβ : β < -1) :
    IsInDomainOfAttractionOfStableWithIndex
      (oddEvenPowerLaw α β hα hβ)
      (heavyTailStableIndex α β) := sorry

end MeasureTheory.ProbabilityMeasure
