import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- A Poisson point process on `E` with intensity `μ` is a random measure with independent
increments whose values on bounded measurable sets have the Poisson laws determined by `μ`. -/
class IsPoissonPointProcess (μ : Measure E) (P : ProbabilityMeasure Ω)
    (X : Ω → Measure E) : Prop where
  /-- The measure-valued map underlying a Poisson point process is measurable. -/
  measurable : Measurable X
  /-- A Poisson point process is locally finite almost surely. -/
  locallyFinite : ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω)
  /-- A Poisson point process has independent increments. -/
  indepIncrements :
    ∀ n, ∀ A : Fin n → Set E,
      (∀ i, MeasurableSet (A i)) →
      Pairwise (fun i j ↦ Disjoint (A i) (A j)) →
      iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω)
  /-- Counts on bounded measurable sets have the Poisson law with parameter `μ A`. -/
  poisson_bounded_eval :
    ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
      HasLaw (fun ω ↦ X ω A)
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure ((μ A).toNNReal)))
        (P : Measure Ω)

-- Proof sketch: use the Poisson-point-process law on bounded measurable sets together with the
-- atom-free hypothesis on `μ` to identify the void probabilities and rule out multiple points at a
-- singleton; conversely, deduce Bernoulli laws for fine partitions from the void probabilities,
-- approximate each bounded set by dyadic refinements, and recover the Poisson marginals and
-- independent increments exactly as in the textbook proof.
/-- Theorem 24.13: for an atom-free boundedly finite intensity measure `μ`, a counting-valued
random measure `X` is a Poisson point process with intensity `μ` if and only if it almost surely
has no double points and satisfies the void-probability identity
`P[X(A) = 0] = exp (-μ(A))` on every bounded measurable set `A`. -/
theorem isPoissonPointProcess_iff_ae_noDoublePoints_and_void_probabilities
    {P : ProbabilityMeasure Ω} {μ : Measure E} [NoAtoms μ] {X : Ω → Measure E}
    (hμ_finite :
      ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A → μ A < ∞)
    (hX_meas : Measurable X)
    (hX_locallyFinite : ∀ᵐ ω ∂(P : Measure Ω), IsLocallyFiniteMeasure (X ω))
    (hX_count :
      ∀ A : Set E, MeasurableSet A →
        ∀ᵐ ω ∂(P : Measure Ω),
          X ω A ∈ Set.range (fun n : ℕ ↦ (n : ℝ≥0∞)) ∪ ({∞} : Set ℝ≥0∞)) :
    IsPoissonPointProcess μ P X ↔
      (∀ᵐ ω ∂(P : Measure Ω), ∀ x : E, X ω ({x} : Set E) ≤ 1) ∧
        ∀ A : Set E, MeasurableSet A → Bornology.IsBounded A →
          (P : Measure Ω) {ω | X ω A = 0} =
            ENNReal.ofReal (Real.exp (-(μ A).toReal)) := sorry

end ProbabilityTheory
