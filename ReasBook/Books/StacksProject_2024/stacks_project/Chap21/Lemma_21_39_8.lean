import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.stacks_project.Chap21.CategoryOverPointDerivedColimit

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped CategoryTheory Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section Generic

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']

/- Domain-style sampling for Lemma 21.39.8:
- primary domain: derived lower shriek for a category over a point, together with inverse image
  induced by precomposition and the cosimplicial pointlike-hom-spaces hypothesis;
- sampled owner declarations:
  `SimplicialObjectHomotopyEquivalent`,
  `CosimplicialObjectHasPointlikeHomSpaces`,
  `categoryOverPointColimitToDerived`,
  `categoryOverPointDerivedColimit`;
- best owner abstraction: the shared Chapter 21 owner layer now lives in
  `CategoryOverPointDerivedColimit.lean`;
- primitive data here: the functor `u : C' ⥤ C`, the existence of a cosimplicial object `U'_•`
  in `C'` satisfying the pointlike-hom-spaces hypothesis before and after whiskering by `u`, and
  the derived-functor instances;
- derived API here: the canonical natural isomorphisms between precomposition inverse image and
  the existing owner functor `categoryOverPointDerivedColimit`, together with proposition-level
  companions.

Source/core/bridge triage:
- `source-facing`: the two comparison theorems below;
- `core/canonical`: the owner declarations from `CategoryOverPointDerivedColimit.lean`;
- `bridge/view`: whiskering a cosimplicial object by `u` and the precomposition functors on
  presheaf categories. -/

/-- The inverse-image functor on `A`-valued presheaves induced by precomposition with `u.op`. -/
abbrev Functor.presheafInverseImage (u : C' ⥤ C) (A : Type w) [Category A] :
    (Cᵒᵖ ⥤ A) ⥤ (C'ᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ A).obj u.op

/- Source-facing notation for inverse image on presheaf categories along a functor `u : C' ⥤ C`.
The coefficient category is written explicitly because it is an owner parameter of the operation.
-/
scoped notation:max u:max "⁻¹[" A:max "]" => Functor.presheafInverseImage u A

/-- Applying a functor to a cosimplicial object degreewise. -/
abbrev Functor.mapCosimplicialObject (u : C' ⥤ C) (Ubullet : CosimplicialObject C') :
    CosimplicialObject C :=
  ((CosimplicialObject.whiskering C' C).obj u).obj Ubullet

section Abelian

instance Functor.presheafInverseImage_additive
    (A : Type w) [Category A] [Abelian A] (u : C' ⥤ C) :
    (u.presheafInverseImage A).Additive := inferInstance

instance Functor.presheafInverseImage_preservesFiniteLimits
    (A : Type w) [Category A] [Abelian A] (u : C' ⥤ C) :
    PreservesFiniteLimits (u.presheafInverseImage A) := inferInstance

instance Functor.presheafInverseImage_preservesFiniteColimits
    (A : Type w) [Category A] [Abelian A] (u : C' ⥤ C) :
    PreservesFiniteColimits (u.presheafInverseImage A) := inferInstance

end Abelian

end Generic

section AbelianTarget

variable {C : Type u} [Category.{v} C]
variable {C' : Type u} [Category.{v} C']
variable (A : Type w) [Category A] [Abelian A] [HasDerivedCategory A]
variable (u : C' ⥤ C)
variable [HasColimitsOfShape Cᵒᵖ A] [HasColimitsOfShape C'ᵒᵖ A]

local notation "Presheaf" => Cᵒᵖ ⥤ A
local notation "Presheaf'" => C'ᵒᵖ ⥤ A
local notation "QisPresheaf" => HomotopyCategory.quasiIso Presheaf (up ℤ)
local notation "QisPresheaf'" => HomotopyCategory.quasiIso Presheaf' (up ℤ)
local notation "ColimitToDerived" =>
  (categoryOverPointColimitToDerived C A :
    HomotopyCategory Presheaf (up ℤ) ⥤ DerivedCategory A)
local notation "ColimitToDerived'" =>
  (categoryOverPointColimitToDerived C' A :
    HomotopyCategory Presheaf' (up ℤ) ⥤ DerivedCategory A)

-- Proof sketch: choose `U'_•` from the hypothesis. Lemma `21.39.7` applied in `C'` identifies
-- `Lπ'_!` with evaluation on `U'_•`, and applied in `C` to the whiskered cosimplicial object
-- `u(U'_•)` identifies `Lπ_!` with evaluation on `u(U'_•)`. Since `u⁻¹[A]` is precomposition
-- with `u`, these two evaluation functors agree, yielding the desired functor isomorphism.
/-- Witness-level form of Lemma 21.39.8: if a specific cosimplicial object `U'_•` of `C'`
has pointlike hom spaces both in `C'` and after degreewise application of `u`, then
`u⁻¹[A] ⋙ Lπ![C', A]` is functorially isomorphic to `Lπ![C, A]`. -/
theorem precompositionDerivedInverseImage_comp_categoryOverPointDerivedLowerShriek_isomorphicOf
    [Functor.HasLeftDerivedFunctor ColimitToDerived QisPresheaf]
    [Functor.HasLeftDerivedFunctor ColimitToDerived' QisPresheaf']
    (Ubullet' : CosimplicialObject C')
    (hUbullet' : CosimplicialObjectHasPointlikeHomSpaces Ubullet')
    (huUbullet' : CosimplicialObjectHasPointlikeHomSpaces
      (u.mapCosimplicialObject Ubullet')) :
    IsIsomorphic
      (((u⁻¹[A]).mapDerivedCategory) ⋙
        (Lπ![C', A] : DerivedCategory Presheaf' ⥤ DerivedCategory A))
      (Lπ![C, A] : DerivedCategory Presheaf ⥤ DerivedCategory A) := by
  sorry

/-- Lemma 21.39.8, owner form: for an abelian target category `A`, if there is a cosimplicial
object `U'_•` of `C'` to which Lemma `21.39.7` applies both in `C'` and, after applying `u`,
in `C`, then the derived lower shriek from `C'` to a point composed with presheaf inverse image
`u⁻¹[A]` is functorially isomorphic to the derived lower shriek from `C` to a point. The Stacks
abelian and module clauses are recovered by
specializing `A` to `AddCommGrpCat` and `ModuleCat B`. -/
@[stacks 08QA]
theorem precompositionDerivedInverseImage_comp_categoryOverPointDerivedLowerShriek_isomorphic
    [Functor.HasLeftDerivedFunctor ColimitToDerived QisPresheaf]
    [Functor.HasLeftDerivedFunctor ColimitToDerived' QisPresheaf']
    (hUbullet :
      ∃ Ubullet' : CosimplicialObject C',
        CosimplicialObjectHasPointlikeHomSpaces Ubullet' ∧
          CosimplicialObjectHasPointlikeHomSpaces
            (u.mapCosimplicialObject Ubullet')) :
    IsIsomorphic
      (((u⁻¹[A]).mapDerivedCategory) ⋙
        (Lπ![C', A] : DerivedCategory Presheaf' ⥤ DerivedCategory A))
      (Lπ![C, A] : DerivedCategory Presheaf ⥤ DerivedCategory A) := by
  rcases hUbullet with ⟨Ubullet', hUbullet', huUbullet'⟩
  exact precompositionDerivedInverseImage_comp_categoryOverPointDerivedLowerShriek_isomorphicOf
    A u Ubullet' hUbullet' huUbullet'

end AbelianTarget

end CategoryTheory
