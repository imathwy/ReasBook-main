import ProbabilityTheory_Klenke_2020.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_33
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_30
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_8
import ProbabilityTheory_Klenke_2020.Chap19.Definition_19_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

-- Proof sketch: if `a` is transient in the Chapter 17 owner sense, then the Green function is
-- finite at `a`, so the source-facing potential is the real-valued function
-- `x ↦ ((G[P, X]) x a).toReal`. Expand `G[P, X]` by
-- `greenFunction_eq_tsum_stateProbabilities`, rewrite the one-step average against
-- `discreteMatrixKernel p` using the Markov realization, and shift the visit-probability series.
-- Outside `{a}` the missing `n = 0` term is `0`, so the shifted series recovers `G(x, a)`,
-- yielding the Chapter 19 harmonicity predicate on `E \ {a}`.
/- Example 19.3 is `source-facing`: the distinguished state is assumed transient via the Chapter 17
owner predicate `IsTransientState P X a`. The chain-level notion `IsTransientMarkovChain p P X`
and the concrete condition `¬ IsAbsorbingState p a` remain only a `bridge/view` reformulation. -/
/-- Example 19.3: for a discrete-time Markov chain with transition matrix `p`, if `a` is
transient, then the real-valued Green potential
`x ↦ ((G[P, X]) x a).toReal` is harmonic on `E \ {a}`. -/
theorem greenFunction_harmonic_off_transient_state
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    {a : E} (ha : IsTransientState P X a) :
    IsHarmonicOutside (discreteMatrixKernel p) ({a} : Set E)
      (fun x ↦ ((G[P, X]) x a).toReal) :=
    sorry

-- Proof sketch: under `IsTransientMarkovChain p P X`, a nonabsorbing state cannot be recurrent;
-- since `F[P, X] a a` is a probability, this forces `F[P, X] a a < 1`, i.e. `a` is transient.
-- Apply the source-facing harmonicity theorem above.
/-- Bridge reformulation: in a transient chain, every nonabsorbing state has harmonic Green
potential off the singleton `{a}`. -/
theorem greenFunction_harmonic_off_nonabsorbing_state
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]
    (htransient : IsTransientMarkovChain p P X) {a : E}
    (ha : ¬ IsAbsorbingState p a) :
    IsHarmonicOutside (discreteMatrixKernel p) ({a} : Set E)
      (fun x ↦ ((G[P, X]) x a).toReal) :=
    sorry

end ProbabilityTheory
