import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap13.Lemma_13_26_12
import stacks_proof.stacks_project.Chap13.«13_26_13_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} {ℬ : Type u}
  [Category.{v} 𝒜] [Category.{v} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)] [Abelian (finiteFilteredObjectCat ℬ)]

/- Domain-style sampling for 13.26.13.6:
- primary domain: bounded-below filtered right derived functors computed by passing to filtered
  injective representatives.
- sampled owner declarations in this domain:
  `Functor.totalRightDerived`,
  `Functor.rightDerivedUnique`,
  `mapBoundedBelowHomotopyCategory`,
  `filteredInjectiveHomotopyToFilteredDerived`,
  `filteredInjectiveHomotopyToFilteredDerived_isEquivalence`.
- best owner abstraction: the source-facing Chapter `13` comparison
  `RT ≅ j' ⋙ mapBoundedBelowHomotopyCategory T_ext.obj ⋙ QFiltB`, where `RT` is the filtered
  right derived functor from `13.26.13.2`, `j'` is the quasi-inverse to the canonical
  equivalence `filteredInjectiveHomotopyToFilteredDerived` from `Lemma 13.26.12`, and the
  `K^+`-lift is the owner from `13.26.13.5`, namely
  `mapBoundedBelowHomotopyCategory T_ext.obj` for the chosen additive filtered extension
  `T_ext`.
- primitive data: a left exact functor `T`, its filtered right derived functor `RT`, an additive
  filtered extension `T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(ℬ)`, and the comparison 2-cell from the
  bounded-below filtered homotopy source functor to the composite through `j'` and `T_ext`.
- derived API: the chapter-specialized comparison isomorphism and its factorization identity.

Source/core/bridge triage:
- `source-facing`: the Chapter `13` comparison `RT ≅ j' ⋙ mapBoundedBelowHomotopyCategory T_ext ⋙
  QFiltB`;
- `core/canonical`: `Functor.totalRightDerived` and `Functor.rightDerivedUnique`;
- `bridge/view`: the inverse equivalence `j'` to
  `filteredInjectiveHomotopyToFilteredDerived` and the comparison 2-cell exhibiting the composite
  through `T_ext` as a right derived functor.

This item should therefore expose the actual Chapter `13` comparison data rather than a generic
copy of the uniqueness theorem with arbitrary placeholder functors. -/

variable (T : 𝒜 ⥤ₗ ℬ)

local instance : PreservesFiniteLimits T.obj :=
  T.property

local instance : PreservesBinaryBiproducts T.obj :=
  preservesBinaryBiproducts_of_preservesBinaryProducts T.obj

local instance : T.obj.Additive :=
  Functor.additive_of_preservesBinaryBiproducts T.obj

local notation "W" => FQis⁺(𝒜)
local notation "QFiltA" => mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜
local notation "QFiltB" => mapBoundedBelowFilteredHomotopyToDerivedBelow ℬ
local notation "Tplus" => mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T)

variable
  [Functor.HasRightDerivedFunctor
    (mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T) ⋙
      mapBoundedBelowFilteredHomotopyToDerivedBelow ℬ)
    (FQis⁺(𝒜))]

local instance : Functor.IsLocalization QFiltA W :=
  mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization

variable (T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(ℬ))

local instance :
    Functor.IsEquivalence
      (filteredInjectiveHomotopyToFilteredDerived 𝒜 :
        K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜)) :=
  by
    simpa using filteredInjectiveHomotopyToFilteredDerived_isEquivalence

private abbrev filteredDerivedInverse : DF⁺(𝒜) ⥤ K⁺(𝓘^f(𝒜)) :=
  (filteredInjectiveHomotopyToFilteredDerived 𝒜 :
      K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜)).asEquivalence.inverse

local notation "RT" => Functor.totalRightDerived (Tplus ⋙ QFiltB) QFiltA W
local notation "αRT" => Functor.totalRightDerivedUnit (Tplus ⋙ QFiltB) QFiltA W
local notation "j'" => filteredDerivedInverse
local notation "Tinj" => mapBoundedBelowHomotopyCategory T_ext.obj
local notation "RTinj" => j' ⋙ Tinj ⋙ QFiltB

variable (comparison : Tplus ⋙ QFiltB ⟶ QFiltA ⋙ RTinj)
variable
  [Functor.IsRightDerivedFunctor
    RTinj
    comparison
    W]

/- Canonical owner recall: the Chapter `13` comparison between the filtered right derived functor
and the composite through filtered injective representatives is the specialized uniqueness
isomorphism for right derived functors. -/
recall Functor.rightDerivedUnique

/- 13.26.13.6: the filtered right derived functor is canonically isomorphic to the functor
obtained by choosing a filtered injective representative via the inverse equivalence from
Lemma `13.26.12`, applying the canonical bounded-below homotopy lift
`mapBoundedBelowHomotopyCategory T_ext.obj` from `13.26.13.5`, and then localizing on the target
side. -/
#check
  ((RT).rightDerivedUnique RTinj αRT comparison W :
    RT ≅ RTinj)

/- The defining relation for this Chapter `13` comparison isomorphism is the canonical owner
lemma `Functor.rightDerived_fac`. -/
recall Functor.rightDerived_fac

#check
  ((RT).rightDerived_fac
      αRT
      W
      RTinj
      comparison :
    αRT ≫ Functor.whiskerLeft QFiltA
      ((RT).rightDerivedDesc
        αRT
        W
        RTinj
        comparison) =
      comparison)

end

end CategoryTheory
