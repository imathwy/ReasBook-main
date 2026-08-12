import ProbabilityTheory_Klenke_2020.Chap08.Example_8_27
import ProbabilityTheory_Klenke_2020.Chap17.Example_17_55
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_11
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_8
import ProbabilityTheory_Klenke_2020.Chap13.Exercise_13_2_2
import ProbabilityTheory_Klenke_2020.Chap07.Corollary_7_45
import ProbabilityTheory_Klenke_2020.Chap18.Definition_18_1
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

section

variable (κ : Kernel E E) [IsMarkovKernel κ]
variable [Kernel.IsIrreducible (Measure.count : Measure E) κ]
variable (π : ProbabilityMeasure E)

-- Proof sketch: irreducibility together with the invariant-distribution hypothesis implies
-- positive recurrence by Theorem 17.51, so Theorem 18.12 yields `(i) → (ii)`. The implications
-- `(ii) → (iii)` and `(iv) → (ii)` are immediate. For `(iii) → (i)`, argue by contraposition and
-- use the cyclic decomposition from Theorem 18.4 to show that a non-aperiodic chain stays a
-- positive total variation distance away from `π` along infinitely many times.
/-- Theorem 18.13: for an irreducible discrete-time Markov kernel with invariant distribution `π`
(equivalently, for an irreducible positive recurrent chain with invariant distribution `π`), the
following are equivalent: (i) the chain is aperiodic; (ii) for every
starting state `x`, equivalently for the evolved Dirac initial law `(κ ^ n) ∘ₘ δ_x`, the law at
time `n` converges to `π` in total variation; (iii) this total-variation convergence holds for
some starting state `x`; (iv) for every initial distribution `μ ∈ M_1(E)`, the evolved law
`(κ ^ n) ∘ₘ μ` converges to `π` in total variation. -/
theorem aperiodic_tfae_tendsto_totalVariation_invariantDistribution
    (hπ : Kernel.Invariant κ (π : Measure E)) :
    List.TFAE
      [ IsAperiodic κ,
        ∀ x : E,
          Tendsto
            (fun n : ℕ ↦
              totalVariationDistance
                (⟨(κ ^ n) ∘ₘ diracProba x, inferInstance⟩ :
                  ProbabilityMeasure E)
                π)
            atTop (𝓝 0),
        ∃ x : E,
          Tendsto
            (fun n : ℕ ↦
              totalVariationDistance
                (⟨(κ ^ n) ∘ₘ diracProba x, inferInstance⟩ :
                  ProbabilityMeasure E)
                π)
            atTop (𝓝 0),
        ∀ μ : ProbabilityMeasure E,
          Tendsto
            (fun n : ℕ ↦
              totalVariationDistance
                (⟨(κ ^ n) ∘ₘ μ, inferInstance⟩ :
                  ProbabilityMeasure E)
                π)
            atTop (𝓝 0) ] := sorry

end

end ProbabilityTheory
