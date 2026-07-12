import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap04.Definition_4_9

noncomputable section

open CategoryTheory

universe v

namespace Representation

section

variable {G : Type} [Group G] [TopologicalSpace G]

/-- An algebraic finite-dimensional complex representation of `G` admits a continuous realization if
it is isomorphic, as an `FDRep ℂ G`, to some finite-dimensional continuous complex representation
of `G`. -/
def FDRep.HasContinuousRealization (τ : FDRep ℂ G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (_ : TopologicalSpace V) (_ : IsTopologicalAddGroup V) (_ : ContinuousSMul ℂ V)
    (_ : T2Space V) (ρ : Representation ℂ G V),
    Representation.IsContinuous ρ ∧ Nonempty (FDRep.of ρ ≅ τ)

namespace FDRep

/-- The canonical `FDRep` attached to a continuous finite-dimensional representation admits that
representation as a continuous realization. -/
theorem hasContinuousRealization_of_representation
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] :
    HasContinuousRealization (FDRep.of ρ) :=
  ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ρ, inferInstance, ⟨Iso.refl _⟩⟩

end FDRep

/-- A family of algebraic finite-dimensional complex representations of `G` is complete for
continuous irreducibles if each member is irreducible and every irreducible `FDRep ℂ G` admitting
a continuous realization occurs in the family up to isomorphism. This is the source-facing
Chapter 4 owner for the completeness hypothesis used in Theorems 4-29 and 4-30. -/
class IsCompleteContinuousIrreducibleFamily {ι : Type v} (π : ι → FDRep ℂ G) : Prop where
  isIrreducible (i : ι) : Representation.IsIrreducible (π i).ρ
  exists_iso (τ : FDRep ℂ G) (hτ_cont : FDRep.HasContinuousRealization τ)
      (hτ_irred : Representation.IsIrreducible τ.ρ) : ∃ i, Nonempty (τ ≅ π i)

attribute [instance] IsCompleteContinuousIrreducibleFamily.isIrreducible

namespace IsCompleteIrreducibleFamily

/-- The Chapter 3 completeness owner is stronger than the Chapter 4 continuity-sensitive one:
every irreducible `FDRep ℂ G` is covered, so in particular every continuously realizable
irreducible object is covered. -/
theorem toIsCompleteContinuousIrreducibleFamily {ι : Type v} {π : ι → FDRep ℂ G}
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    IsCompleteContinuousIrreducibleFamily π where
  isIrreducible i := by
    letI : Simple (π i) := hπ_complete.isSimple i
    simpa using FDRep.isIrreducible_of_simple (π i)
  exists_iso τ _ hτ_irred := by
    letI : Representation.IsIrreducible τ.ρ := hτ_irred
    exact hπ_complete.exists_iso τ (FDRep.simple_of_isIrreducible τ)

end IsCompleteIrreducibleFamily

namespace IsCompleteContinuousIrreducibleFamily

/-- The source-facing completeness owner applies directly to a continuous irreducible
finite-dimensional representation. -/
theorem exists_iso_of_representation {ι : Type v} (π : ι → FDRep ℂ G)
    (hπ_complete : IsCompleteContinuousIrreducibleFamily π)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W]
    (ρ : Representation ℂ G W) [Representation.IsContinuous ρ]
    (hρ_irred : Representation.IsIrreducible ρ) :
    ∃ i, Nonempty (FDRep.of ρ ≅ π i) :=
  hπ_complete.exists_iso (FDRep.of ρ)
    (FDRep.hasContinuousRealization_of_representation ρ) (by simpa using hρ_irred)

end IsCompleteContinuousIrreducibleFamily

end

end Representation
