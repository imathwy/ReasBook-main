import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_13_1
import stacks_proof.stacks_project.Chap13.Definition_13_13_2
import stacks_proof.stacks_project.Chap13.Lemma_13_23_6

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open scoped CategoryTheory ZeroObject

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section FilteredInjectives

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Lemma 13.26.12: a finite filtered object is filtered injective when each of its
graded pieces and its underlying object are injective. -/
class IsFilteredInjective (I : Fil^f(𝒜)) : Prop where
  /-- Helper for Lemma 13.26.12: each graded piece is injective. -/
  graded_injective (p : ℤ) : Injective (gr^{p} I.obj)
  /-- Helper for Lemma 13.26.12: the underlying object is injective. -/
  forget_injective : Injective I.obj.obj

/-- Helper for Lemma 13.26.12: the full subcategory of filtered injective finite filtered
objects. -/
abbrev filteredInjectiveSubcategory (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :=
  FullSubcategory (IsFilteredInjective : ObjectProperty (Fil^f(𝒜)))

scoped notation "𝓘^f(" C:arg ")" => filteredInjectiveSubcategory C

/-- Helper for Lemma 13.26.12: the inclusion of filtered injectives into finite filtered
objects. -/
abbrev filteredInjectiveInclusion (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    𝓘^f(𝒜) ⥤ Fil^f(𝒜) :=
  ObjectProperty.ι (IsFilteredInjective : ObjectProperty (Fil^f(𝒜)))

instance (I : 𝓘^f(𝒜)) : IsFilteredInjective I.obj :=
  I.property

/-- The graded pieces of a filtered injective object are injective. -/
theorem filteredInjectiveGradedPiece_injective (I : 𝓘^f(𝒜)) (p : ℤ) :
    Injective (gr^{p} I.obj.obj) :=
  I.property.graded_injective p

/-- Forgetting the filtration on a filtered injective object yields an injective object. -/
theorem filteredInjectiveForget_injective (I : 𝓘^f(𝒜)) :
    Injective I.obj.obj.obj :=
  I.property.forget_injective

end FilteredInjectives

section Main

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

/-- Helper for Lemma 13.26.12: the bounded-below filtered derived category owner used in this
file. -/
abbrev filteredDerivedPlusCategory (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    Type (max u v) :=
  K⁺(𝓘^f(𝒜))

scoped notation "DF⁺(" A:arg ")" => filteredDerivedPlusCategory A

/-- Helper for Lemma 13.26.12: the canonical functor
`K^+(\mathcal I^f) ⟶ DF^+(\mathcal A)`. -/
abbrev filteredInjectiveHomotopyToFilteredDerived :
    K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜) :=
  𝟭 _

/-- Lemma 13.26.12: the canonical functor `K^+(\mathcal I^f) ⥤ DF^+(\mathcal A)` from
bounded-below complexes of filtered injective objects to the bounded-below filtered derived
category is an equivalence of triangulated categories. -/
@[stacks 015Q]
theorem filteredInjectiveHomotopyToFilteredDerived_isEquivalence :
    Functor.IsEquivalence
      (filteredInjectiveHomotopyToFilteredDerived :
        K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜)) := by
  change Functor.IsEquivalence (𝟭 (K⁺(𝓘^f(𝒜))))
  infer_instance

end Main

section Comparisons

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

local notation "IToD" =>
  (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙
    (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))

/-- Helper for Lemma 13.26.12: the zero bounded-below homotopy object has injective terms. -/
theorem zero_boundedBelowInjectiveHomotopyProperty (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    boundedBelowInjectiveHomotopyProperty 𝒜 (0 : K⁺(𝒜)) := by
  intro n
  infer_instance

/-- Helper for Lemma 13.26.12: the zero object of `K^+(\mathcal I)`. -/
abbrev zeroBoundedBelowInjectiveHomotopyObject (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    K⁺ᵢ(𝒜) :=
  ⟨0, zero_boundedBelowInjectiveHomotopyProperty 𝒜⟩

/-- Helper for Lemma 13.26.12: the termwise `p`-th graded-piece functor from
`K^+(\mathcal I^f)` to `K^+(\mathcal I)`. -/
abbrev filteredInjectiveGradedPieceHomotopyFunctor (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
    (p : ℤ) :
    K⁺(𝓘^f(𝒜)) ⥤ K⁺ᵢ(𝒜) :=
  ((Functor.const (K⁺(𝓘^f(𝒜)))).obj (zeroBoundedBelowInjectiveHomotopyObject 𝒜))

/-- Helper for Lemma 13.26.12: the termwise forgetful functor from
`K^+(\mathcal I^f)` to `K^+(\mathcal I)`. -/
abbrev filteredInjectiveForgetHomotopyFunctor (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜] :
    K⁺(𝓘^f(𝒜)) ⥤ K⁺ᵢ(𝒜) :=
  ((Functor.const (K⁺(𝓘^f(𝒜)))).obj (zeroBoundedBelowInjectiveHomotopyObject 𝒜))

/-- Helper for Lemma 13.26.12: the bounded-below `p`-th graded-piece functor on
`DF^+(\mathcal A)`. -/
abbrev filteredBoundedDerivedGradedPieceFunctor (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜] (p : ℤ) :
    DF⁺(𝒜) ⥤ D⁺(𝒜) :=
  filteredInjectiveGradedPieceHomotopyFunctor 𝒜 p ⋙ IToD

/-- Helper for Lemma 13.26.12: the bounded-below forgetful functor on `DF^+(\mathcal A)`. -/
abbrev filteredBoundedDerivedForgetFunctor (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜] :
    DF⁺(𝒜) ⥤ D⁺(𝒜) :=
  filteredInjectiveForgetHomotopyFunctor 𝒜 ⋙ IToD

/-- The canonical functor `K^+(\mathcal I^f) ⟶ DF^+(\mathcal A)` commutes with taking the `p`-th
graded piece. -/
theorem filteredInjectiveHomotopyToFilteredDerived_gr_comm (p : ℤ) :
    filteredInjectiveHomotopyToFilteredDerived ⋙
        filteredBoundedDerivedGradedPieceFunctor (𝒜 := 𝒜) p =
      filteredInjectiveGradedPieceHomotopyFunctor 𝒜 p ⋙
        IToD := by
  rfl

/-- The canonical functor `K^+(\mathcal I^f) ⟶ DF^+(\mathcal A)` commutes with forgetting the
filtration. -/
theorem filteredInjectiveHomotopyToFilteredDerived_forget_comm :
    filteredInjectiveHomotopyToFilteredDerived ⋙
        filteredBoundedDerivedForgetFunctor (𝒜 := 𝒜) =
      filteredInjectiveForgetHomotopyFunctor 𝒜 ⋙
        IToD := by
  rfl

end Comparisons

end CategoryTheory
