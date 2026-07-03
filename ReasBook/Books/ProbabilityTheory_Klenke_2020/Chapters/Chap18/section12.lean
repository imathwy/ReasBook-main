import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_18_12 (from Items/Chap18) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- Any realization of the kernel powers `n ↦ discreteMatrixKernel p ^ n` forces
`discreteMatrixKernel p` itself to be a Markov kernel. -/
theorem discreteMatrixKernel_isMarkovKernel_of_markovProcessRealization
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsMarkovKernel (discreteMatrixKernel p) := by
  have hrealization :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hsemigroup : IsMarkovSemigroup (fun n : ℕ ↦ discreteMatrixKernel p ^ n) := by
    exact @isMarkovSemigroup_of_markovProcessRealization ℕ _ E ‹_› _ Ω ‹_›
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X hrealization
  simpa using hsemigroup.isMarkovKernel 1

/-- A successful coupling for `p` already implies that the owner kernel `discreteMatrixKernel p`
is Markov. -/
theorem discreteMatrixKernel_isMarkovKernel_of_hasSuccessfulCoupling
    {p : E → E → ℝ≥0∞} (hcoupling : HasSuccessfulCoupling p) :
    IsMarkovKernel (discreteMatrixKernel p) := by
  classical
  by_cases hE : IsEmpty E
  · letI : IsEmpty E := hE
    exact ⟨fun x ↦ isEmptyElim x⟩
  · let y : E := Classical.choice (not_isEmpty_iff.mp hE)
    rcases hcoupling.exists_successfulCoupling with ⟨Ω', mΩ', P, Z, hsuccess⟩
    letI : MeasurableSpace Ω' := mΩ'
    let P₁ : E → ProbabilityMeasure Ω' := fun x ↦ P (x, y)
    let X₁ : ℕ → Ω' → E := fun n ω ↦ (Z n ω).1
    have hrealization :
        IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P₁ X₁ := by
      simpa [P₁, X₁] using hsuccess.toIsMarkovCoupling.fst_realization y
    have hsemigroup : IsMarkovSemigroup (fun n : ℕ ↦ discreteMatrixKernel p ^ n) := by
      exact @isMarkovSemigroup_of_markovProcessRealization ℕ _ E ‹_› _ Ω' ‹_›
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P₁ X₁ hrealization
    simpa using hsemigroup.isMarkovKernel 1

/-- The owner condition `IsMarkovKernel (discreteMatrixKernel p)` is exactly the source-facing
statement that `p` is stochastic. -/
theorem isStochasticMatrix_of_discreteMatrixKernel_isMarkovKernel
    {p : E → E → ℝ≥0∞} (hmarkov : IsMarkovKernel (discreteMatrixKernel p)) :
    IsStochasticMatrix p := by
  intro x
  simpa [discreteMatrixKernel_univ] using (hmarkov.isProbabilityMeasure x).measure_univ

-- Proof sketch: choose a successful coupling of the chain from `HasSuccessfulCoupling p`, use it
-- at arbitrary initial states,
-- use the coupling inequality to bound the total variation distance of the two `n`-step laws by
-- the disagreement probability at time `n`, and then average over the initial coupling of `μ`
-- and `ν`.
/-- Theorem 18.12 (1): if the Markov chain with transition matrix `p` admits a successful
coupling, then the total variation distance between the `n`-step laws started from any two
initial distributions `μ` and `ν` tends to `0`. -/
theorem nStepTotalVariationDistance_tendsto_zero_of_hasSuccessfulCoupling
    {p : E → E → ℝ≥0∞}
    (hcoupling : HasSuccessfulCoupling p)
    (μ ν : ProbabilityMeasure E) :
    let _ : IsMarkovKernel (discreteMatrixKernel p) :=
      discreteMatrixKernel_isMarkovKernel_of_hasSuccessfulCoupling hcoupling
    Tendsto
      (fun n : ℕ ↦
        let κn : Kernel E E := discreteMatrixKernel p ^ n
        totalVariationDistance
          (⟨κn ∘ₘ (μ : Measure E), inferInstance⟩ :
            ProbabilityMeasure E)
          (⟨κn ∘ₘ (ν : Measure E), inferInstance⟩ :
            ProbabilityMeasure E))
      atTop (nhds 0) := sorry

-- Proof sketch: the realization owner identifies `discreteMatrixKernel p` as the one-step kernel.
-- The irreducibility hypothesis upgrades the invariant distribution `π` to positive recurrence by
-- Theorem 17.51, so `hπ` and `haperiodic` place the chain in the setting of Theorem 18.11, which
-- yields a successful coupling. Part (1) then gives convergence from `μ` to the invariant law
-- `π`.
/-- Theorem 18.12 (2): if `X` is irreducible and aperiodic and admits invariant distribution `π`,
then the total variation distance between the `n`-step law started from any initial distribution
`μ` and `π` tends to `0`. -/
theorem nStepTotalVariationDistance_tendsto_zero_to_invariantDistribution_of_irreducible_aperiodic_positiveRecurrent
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    (haperiodic : IsAperiodic (discreteMatrixKernel p))
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    (μ : ProbabilityMeasure E) :
    let _ : IsMarkovKernel (discreteMatrixKernel p) :=
      discreteMatrixKernel_isMarkovKernel_of_markovProcessRealization (p := p) (P := P) (X := X)
    Tendsto
      (fun n : ℕ ↦
        let κn : Kernel E E := discreteMatrixKernel p ^ n
        totalVariationDistance
          (⟨κn ∘ₘ (μ : Measure E), inferInstance⟩ :
            ProbabilityMeasure E)
          π)
      atTop (nhds 0) := sorry

end ProbabilityTheory
