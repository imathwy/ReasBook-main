import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.Lemma_20_27_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_34_1
import StacksProject_2024.stacks_project.Chap21.Remark_21_19_3_core

open CategoryTheory
open AlgebraicGeometry
open ComplexShape
open scoped RingedSpace.Hom RingedSpaceClosedSubsetDerived RingedSpaceDerivedPullback

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

/- Domain-style sampling for Remark 20.34.12:
- primary domain: pullback/base-change for derived sections with support on closed subsets of
  ringed spaces;
- sampled owner declarations:
  `CategoryTheory.derivedBaseChangeMap`,
  `CategoryTheory.derivedBaseChangeMap_spec`,
  `RingedSpace.modulePullbackDerived`,
  `Adjunction.ofIsLeftAdjoint`,
  `Adjunction.homEquiv`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: the pullback/base-change morphism
    `pullbackOnClosedSubsetDerived.obj ((R𝓗[hZ]).obj K) ⟶
      (R𝓗[hZ']).obj ((L(f)^*).obj K)`;
  `core/canonical`: `CategoryTheory.derivedBaseChangeMap`, specialized to
    `i⋆[hZ] ⊣ R𝓗[hZ]` and `i⋆[hZ'] ⊣ R𝓗[hZ']`;
  `bridge/view`: the pushforward-side `CommSq` obtained by applying `i⋆[hZ']` and undoing the
    chosen comparison isomorphism
    `pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*`.

Primitive data are only the closed-subset pullback functor and the pushforward-side comparison
isomorphism. The actual pullback morphism on the closed-subset derived categories is already the
generic owner `CategoryTheory.derivedBaseChangeMap`, so this file is theorem-level after
refinement: it recalls that canonical owner and keeps only its specialized mate formula and the
pushforward-side square as chapter-specific bridge API. -/

variable {X X' : RingedSpace.{u}} {Z : Set X} {Z' : Set X'}
variable (f : X' ⟶ X) (hZ : IsClosed Z) (hZ' : IsClosed Z')
variable
  [CategoryWithHomology (RingedSpace.Modules X)]
  [CategoryWithHomology (RingedSpace.Modules X')]
  [(f^*).Additive]
  [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis X)]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModZ" => closedSubsetModuleDerived X Z
local notation "DModZ'" => closedSubsetModuleDerived X' Z'

private noncomputable abbrev derivedAdjunctionZ :
    i⋆[hZ] ⊣ R𝓗[hZ] :=
  closedSubsetModulePushforwardDerivedAdjunction X Z hZ

private noncomputable abbrev derivedAdjunctionZPrime :
    i⋆[hZ'] ⊣ R𝓗[hZ'] :=
  closedSubsetModulePushforwardDerivedAdjunction X' Z' hZ'

local notation "adjZ" => derivedAdjunctionZ hZ
local notation "adjZPrime" => derivedAdjunctionZPrime hZ'

variable
  (pullbackOnClosedSubsetDerived : DModZ ⥤ DModZ')
  (pullbackOnClosedSubsetPushforwardIso :
    pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)

/- Remark 20.34.12 uses the canonical base-change morphism
`CategoryTheory.derivedBaseChangeMap`, specialized to the derived closed-subset adjunctions
`i⋆[hZ] ⊣ R𝓗[hZ]` and `i⋆[hZ'] ⊣ R𝓗[hZ']`. -/
recall CategoryTheory.derivedBaseChangeMap

/-- Transposing the canonical base-change morphism of Remark 20.34.12 across
`i⋆[hZ'] ⊣ R𝓗[hZ']` recovers the pullback of the counit prescribed by the chosen pushforward
comparison isomorphism. -/
@[stacks 0G78]
theorem closedSubsetSectionsWithSupportDerivedBaseChangeMap_spec
    (pullbackOnClosedSubsetDerived : DModZ ⥤ DModZ')
    (pullbackOnClosedSubsetPushforwardIso :
      pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)
    (K : DModX) :
    ((adjZPrime).homEquiv
        (pullbackOnClosedSubsetDerived.obj ((R𝓗[hZ]).obj K))
        ((L(f)^*).obj K)).symm
        (CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
          pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
          (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K) =
      pullbackOnClosedSubsetPushforwardIso.hom.app ((R𝓗[hZ]).obj K) ≫
        (L(f)^*).map ((adjZ).counit.app K) := by
  simpa using
    (CategoryTheory.derivedBaseChangeMap_spec (i⋆[hZ]) (i⋆[hZ'])
      pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
      (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K)

/-- Applying `i⋆[hZ']` to the pullback comparison of Remark 20.34.12 and undoing the canonical
pushforward-side pullback identification yields a commutative square with the two adjunction
counits. -/
theorem closedSubsetPullback_sectionsWithSupportDerived_pushforward_commSq
    (pullbackOnClosedSubsetDerived : DModZ ⥤ DModZ')
    (pullbackOnClosedSubsetPushforwardIso :
      pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)
    (K : DModX) :
    CommSq
      (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
        (i⋆[hZ']).map
          (CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
            pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
            (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K))
      ((L(f)^*).map ((adjZ).counit.app K))
      ((adjZPrime).counit.app ((L(f)^*).obj K))
      (𝟙 ((L(f)^*).obj K)) := by
  let η :=
    CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
      pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
      (derivedAdjunctionZ hZ) (derivedAdjunctionZPrime hZ')
      pullbackOnClosedSubsetPushforwardIso K
  have hhom :
      (i⋆[hZ']).map η ≫ (derivedAdjunctionZPrime hZ').counit.app ((L(f)^*).obj K) =
      ((derivedAdjunctionZPrime hZ').homEquiv
          (pullbackOnClosedSubsetDerived.obj ((R𝓗[hZ]).obj K))
          ((L(f)^*).obj K)).symm η := by
    simpa using
      ((adjZPrime).homEquiv_counit
        (pullbackOnClosedSubsetDerived.obj ((R𝓗[hZ]).obj K))
        ((L(f)^*).obj K)
        η).symm
  have hstep1 :
      (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
          (i⋆[hZ']).map η) ≫
        (adjZPrime).counit.app ((L(f)^*).obj K) =
      pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
          ((adjZPrime).homEquiv
              (pullbackOnClosedSubsetDerived.obj ((R𝓗[hZ]).obj K))
              ((L(f)^*).obj K)).symm η := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫ t)
        hhom
  have hspec :
      ((adjZPrime).homEquiv
          (pullbackOnClosedSubsetDerived.obj ((R𝓗[hZ]).obj K))
          ((L(f)^*).obj K)).symm η =
      pullbackOnClosedSubsetPushforwardIso.hom.app ((R𝓗[hZ]).obj K) ≫
        (L(f)^*).map ((adjZ).counit.app K) := by
    simpa [η] using
      (closedSubsetSectionsWithSupportDerivedBaseChangeMap_spec
        f
        hZ
        hZ'
        pullbackOnClosedSubsetDerived
        pullbackOnClosedSubsetPushforwardIso
        K)
  have hstep2 :
      pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
          ((adjZPrime).homEquiv
              (pullbackOnClosedSubsetDerived.obj ((R𝓗[hZ]).obj K))
              ((L(f)^*).obj K)).symm η =
        pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
          pullbackOnClosedSubsetPushforwardIso.hom.app ((R𝓗[hZ]).obj K) ≫
            (L(f)^*).map ((adjZ).counit.app K) := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫ t)
        hspec
  have hstep3 :
      pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
          pullbackOnClosedSubsetPushforwardIso.hom.app ((R𝓗[hZ]).obj K) ≫
            (L(f)^*).map ((adjZ).counit.app K) =
        (L(f)^*).map ((adjZ).counit.app K) := by
    simpa [Category.assoc] using
      (pullbackOnClosedSubsetPushforwardIso.app ((R𝓗[hZ]).obj K)).inv_hom_id_assoc
        ((L(f)^*).map ((adjZ).counit.app K))
  have hstep4 :
      (L(f)^*).map ((adjZ).counit.app K) =
        (L(f)^*).map ((adjZ).counit.app K) ≫ 𝟙 ((L(f)^*).obj K) := by
    simp
  exact CommSq.mk (hstep1.trans (hstep2.trans (hstep3.trans hstep4)))

/-- The pushforward-side pullback morphism of Remark 20.34.12 intertwines the two adjunction
counits. -/
theorem closedSubsetPullback_sectionsWithSupportDerived_pushforward_comp_counit
    (pullbackOnClosedSubsetDerived : DModZ ⥤ DModZ')
    (pullbackOnClosedSubsetPushforwardIso :
      pullbackOnClosedSubsetDerived ⋙ i⋆[hZ'] ≅ i⋆[hZ] ⋙ L(f)^*)
    (K : DModX) :
    (pullbackOnClosedSubsetPushforwardIso.inv.app ((R𝓗[hZ]).obj K) ≫
        (i⋆[hZ']).map
          (CategoryTheory.derivedBaseChangeMap (i⋆[hZ]) (i⋆[hZ'])
            pullbackOnClosedSubsetDerived (L(f)^*) (R𝓗[hZ]) (R𝓗[hZ'])
            (adjZ) (adjZPrime) pullbackOnClosedSubsetPushforwardIso K)) ≫
      (adjZPrime).counit.app ((L(f)^*).obj K) =
    (L(f)^*).map ((adjZ).counit.app K) := by
  simpa using
    (closedSubsetPullback_sectionsWithSupportDerived_pushforward_commSq f hZ hZ'
      pullbackOnClosedSubsetDerived pullbackOnClosedSubsetPushforwardIso K).w

end

end AlgebraicGeometry.RingedSpace
