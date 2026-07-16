import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_3
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_12
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_21
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_26
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open Filter Set Function
open scoped ProbabilityTheory ZeroAtInfty

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u}
variable [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
variable [LocallyCompactSpace E] [PolishSpace E]

/-- A realization of a Feller semigroup is a time-homogeneous Markov process whose path kernel has
the prescribed transition kernels, satisfies the strong Markov property, and has almost surely
càdlàg paths under every initial law. -/
class IsFellerProcessRealization {Ω : Type v} [MeasurableSpace Ω] (κ : NNReal → Kernel E E)
    [IsFellerSemigroup κ]
    (P : E → ProbabilityMeasure Ω) (X : NNReal → Ω → E)
    (pathKernel : Kernel E (NNReal → E)) : Prop
    extends IsTimeHomogeneousMarkovProcess X P pathKernel where
  /-- The realization satisfies the strong Markov property. -/
  strongMarkov : HasStrongMarkovProperty P X pathKernel
  /-- Under each initial law, almost every sample path is càdlàg. -/
  cadlag_paths : ∀ x : E, ∀ᵐ ω ∂(P x : Measure Ω), IsCadlag (fun t : NNReal ↦ X t ω)
  /-- The realized transition kernels agree with the given Feller semigroup. -/
  transition_eq : ∀ t : NNReal, transitionKernel pathKernel t = κ t

-- Proof sketch: use the standard Feller-process existence theorem on locally compact Polish state
-- spaces, construct a path-space realization of the semigroup, obtain an RCLL modification from
-- the Feller property, and identify the resulting transition kernels with the prescribed family.
/-- Theorem 21.27: every Feller semigroup on a locally compact Polish space admits a strong Markov
realization with càdlàg paths and the prescribed transition kernels; such a realization is called
a Feller process. -/
theorem exists_fellerProcessRealization (κ : NNReal → Kernel E E) [IsFellerSemigroup κ] :
    ∃ (Ω : Type v), ∃ _ : MeasurableSpace Ω, ∃ X : NNReal → Ω → E,
      ∃ P : E → ProbabilityMeasure Ω, ∃ pathKernel : Kernel E (NNReal → E),
        IsFellerProcessRealization κ P X pathKernel := sorry

end ProbabilityTheory
