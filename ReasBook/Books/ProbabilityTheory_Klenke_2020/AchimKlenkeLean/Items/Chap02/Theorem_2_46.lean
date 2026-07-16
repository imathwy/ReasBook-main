import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Definition_2_44
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Theorem_2_47

open MeasureTheory ProbabilityTheory
open scoped unitInterval
open unitInterval

universe u

local notation "half" => (⟨(1 / 2 : ℝ), by
  constructor <;> norm_num⟩ : unitInterval)

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable (measure : unitInterval → ProbabilityMeasure Ω)
variable (openEdges : unitInterval → Ω → Set (Sym2 (LatticePoint 2)))

-- Proof sketch: this is Kesten's theorem for Bernoulli bond percolation on `ℤ²`.
/-- Theorem 2.46: for Bernoulli bond percolation on `ℤ²`, modeled by a `p`-indexed family of
random open-edge sets with Bernoulli law on the nearest-neighbor edges of `latticeGraph 2`, one
has `p_c = 1 / 2` and `θ(p_c) = 0`. -/
theorem criticalValue_eq_half_and_originPercolationProbability_criticalValue_eq_zero
    (hber : ∀ p : unitInterval,
      IsSetBernoulli (openEdges p) (latticeGraph 2).edgeSet p (measure p : Measure Ω)) :
    let θ : unitInterval → NNReal := fun p ↦
      originPercolationProbability (measure p) (openCluster (bondConnectionEvent (openEdges p)))
    criticalPercolationValue θ = half ∧ θ (criticalPercolationValue θ) = 0 := sorry

/-- Theorem 2.46: for Bernoulli bond percolation on `ℤ²`, the critical value is `1 / 2`. -/
theorem criticalValue_eq_half
    (hber : ∀ p : unitInterval,
      IsSetBernoulli (openEdges p) (latticeGraph 2).edgeSet p (measure p : Measure Ω)) :
    let θ : unitInterval → NNReal := fun p ↦
      originPercolationProbability (measure p) (openCluster (bondConnectionEvent (openEdges p)))
    criticalPercolationValue θ = half := by
  simpa using
    (criticalValue_eq_half_and_originPercolationProbability_criticalValue_eq_zero
      measure openEdges hber).1

/-- Theorem 2.46: for Bernoulli bond percolation on `ℤ²`, the origin-percolation probability
vanishes at the critical value. -/
theorem originPercolationProbability_criticalValue_eq_zero
    (hber : ∀ p : unitInterval,
      IsSetBernoulli (openEdges p) (latticeGraph 2).edgeSet p (measure p : Measure Ω)) :
    let θ : unitInterval → NNReal := fun p ↦
      originPercolationProbability (measure p) (openCluster (bondConnectionEvent (openEdges p)))
    θ (criticalPercolationValue θ) = 0 := by
  simpa using
    (criticalValue_eq_half_and_originPercolationProbability_criticalValue_eq_zero
      measure openEdges hber).2

end
