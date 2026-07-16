import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_23_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped CategoryTheory

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

attribute [local instance] HasDerivedCategory.standard

/- Proposition 13.23.1: once a homotopy resolution functor `j` is fixed, the canonical functor
`K^+(\mathcal I) ⥤ D^+(\mathcal A)` is an equivalence. This public owner statement reuses the
chapter-level owners `boundedBelowInjectiveHomotopyProperty`,
`mapBoundedBelowHomotopyToDerivedBelow`, and `HomotopyResolutionFunctor`. -/
/-- Proposition 13.23.1, canonical owner form: for any homotopy resolution functor
`j : K^+(\mathcal A) ⥤ K^+(\mathcal I)`, the canonical functor
`K^+(\mathcal I) ⥤ D^+(\mathcal A)` is an equivalence of categories. -/
theorem HomotopyResolutionFunctor.toDerived_isEquivalence
    (j : HomotopyResolutionFunctor 𝒜) :
    Functor.IsEquivalence
      (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
        mapBoundedBelowHomotopyToDerivedBelow) := by
  sorry

/-- Proposition 13.23.1: if an abelian category `𝒜` has enough injectives, then the canonical
functor `K^+(\mathcal I) ⥤ D^+(\mathcal A)` from bounded-below complexes of injective objects to
the bounded-below derived category is an equivalence of categories. -/
theorem boundedBelowInjectiveHomotopyToDerived_isEquivalence [EnoughInjectives 𝒜] :
    Functor.IsEquivalence
      (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
        mapBoundedBelowHomotopyToDerivedBelow) := by
  obtain ⟨j⟩ : Nonempty (HomotopyResolutionFunctor 𝒜) := exists_homotopyResolutionFunctor
  simpa using j.toDerived_isEquivalence

end

end CategoryTheory
