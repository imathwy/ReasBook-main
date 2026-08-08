import ProbabilityTheory_Klenke_2020.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_43
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_8
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [mE : MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: use the one-step Markov property for the realization of `p` to identify the
-- conditional expectation of `f (X (n + 1))` given the past with the one-step averaging operator
-- `y ↦ ∫ z, f z ∂ discreteMatrixKernel p y`, evaluated at `X n`; the harmonicity hypothesis turns
-- this conditional expectation into `f (X n)`, and boundedness supplies the required
-- integrability.
/-- Lemma 17.45 (1): for a realization of the discrete chain with transition matrix `p`, if `f`
has bounded range and is harmonic for the owner kernel `discreteMatrixKernel p`, then the process
`(f (X_n))_n` is a martingale with respect to the natural filtration of `X`. -/
theorem harmonicFunction_comp_martingale
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) (x : E) :
    Martingale (fun n ω ↦ f (X n ω)) (processFiltration X) (P x : Measure Ω) := sorry

-- Proof sketch: the same one-step conditional-expectation computation gives
-- `f (X n) ≤ E[f (X (n + 1)) | 𝓕_n]` almost surely, because subharmonicity says the one-step
-- averaged value dominates `f`; boundedness gives integrability of every `f (X n)`.
/-- Lemma 17.45 (2): for a realization of the discrete chain with transition matrix `p`, if `f`
has bounded range and is subharmonic for the owner kernel `discreteMatrixKernel p`, then the
process
`(f (X_n))_n` is a submartingale with respect to the natural filtration of `X`. -/
theorem subharmonicFunction_comp_submartingale
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_subharmonic : IsSubharmonic (discreteMatrixKernel p) f) (x : E) :
    Submartingale (fun n ω ↦ f (X n ω)) (processFiltration X) (P x : Measure Ω) := sorry

-- Proof sketch: identify the conditional expectation of `f (X (n + 1))` given the past with the
-- one-step averaging operator applied at `X n`; the superharmonicity inequality shows this
-- conditional expectation is almost surely bounded above by `f (X n)`, and boundedness yields the
-- needed integrability.
/-- Lemma 17.45 (3): for a realization of the discrete chain with transition matrix `p`, if `f`
has bounded range and is superharmonic for the owner kernel `discreteMatrixKernel p`, then the
process
`(f (X_n))_n` is a supermartingale with respect to the natural filtration of `X`. -/
theorem superharmonicFunction_comp_supermartingale
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_superharmonic : IsSuperharmonic (discreteMatrixKernel p) f) (x : E) :
    Supermartingale (fun n ω ↦ f (X n ω)) (processFiltration X) (P x : Measure Ω) := sorry

end

end ProbabilityTheory
