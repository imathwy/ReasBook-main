import StacksProject_2024.stacks_project.Chap21.Lemma_21_28_6

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty
open scoped RingedSite.Hom
open scoped RingedSiteDerived
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (ε : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [Abelian ModX] [Abelian ModY]
variable [HasInjectiveResolutions ModX]
variable [(PresheafOfModules.pushforward.{max u v} ε.structureSheafMap.hom).IsRightAdjoint]
variable [(SheafOfModules.pushforward ε.structureSheafMap).IsRightAdjoint]
variable [Fact (IsFlat ε)]
variable [ε.modulePushforward.Additive]
variable [(ε^*).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived ε) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived ε) (ModuleQis Y)]

variable (A' : ObjectProperty ModY) (A : ObjectProperty ModX)
variable [IsWeakSerreClass A]
variable (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A ((ε^*).obj ℱ'))

/- Domain-style sampling for Lemma 21.29.1:
- primary domain: weak Serre subcategories of module sheaves on ringed sites and the restricted
  derived pullback/pushforward functors attached to a flat morphism;
- sampled owner declarations:
  `ObjectProperty.lift`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence`;
- best owner abstraction: the restricted-derived equivalence theorem from Lemma `21.28.6`;
- primitive data: the object properties `A'` and `A`, the pullback-membership hypothesis
  `hpull_mem`, the exactness hypothesis on pushforward over `A`, and the underived
  pullback/pushforward unit data;
- derived API: the target weak-Serre transfer in part `(1)`, and the already-owned restricted
  derived equivalence in part `(2)`.

Source/core/bridge triage:
- `source-facing`: `targetWeakSerreSubcategory_of_pullbackEquivalence_of_pushforwardExact`;
- `core/canonical`: the restricted pullback equivalence theorem from Lemma `21.28.6`, stated for
  the canonical `modulePullbackDerivedOfFlatWithCohomologyIn` owner;
- `bridge/view`: the current file only restates the source theorem in part `(1)`, while part `(2)`
  should expose the equivalence of that owner functor directly rather than split it into a functor
  recall and a separate equivalence predicate recall. -/

-- Proof sketch: pushforward is assumed exact on the source weak Serre full subcategory. Pull back
-- a five-term exact sequence in `A'`, apply weak-Serre closure on `A`, and then use the underived
-- adjunction unit isomorphisms together with exact pushforward to transport the middle term back
-- to `A'`.
section

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

/-- Lemma 21.29.1 (1): in the topology-comparison situation, if pullback identifies the target
subcategory `𝒜'` with a weak Serre subcategory `𝒜` on the source and pushforward is exact on
the source subcategory, then `𝒜'` is a weak Serre subcategory of `Mod(𝒪_{τ'})`. This
formalizes the target-side image of the textbook subcategory `𝒜`. -/
@[stacks 07A8]
theorem targetWeakSerreSubcategory_of_pullbackEquivalence_of_pushforwardExact
    (hpush_mem : ∀ ⦃ℱ : ModX⦄, A ℱ → A' (ε.modulePushforward.obj ℱ))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories ε A' A hpull_mem)]
    (hpush_exact : exactFunctor A.FullSubcategory ModY
      (A.ι ⋙ ε.modulePushforward))
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction ε.structureSheafMap).unit.app ℱ'.obj)) :
    IsWeakSerreClass A' := sorry

/-- The target object property `A'` inherits a weak Serre structure from
Lemma `21.29.1 (1)`. -/
instance instTargetWeakSerreSubcategoryOfPullbackEquivalenceOfPushforwardExact
    (hpush_mem : ∀ ⦃ℱ : ModX⦄, A ℱ → A' (ε.modulePushforward.obj ℱ))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories ε A' A hpull_mem)]
    (hpush_exact : exactFunctor A.FullSubcategory ModY
      (A.ι ⋙ ε.modulePushforward))
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction ε.structureSheafMap).unit.app ℱ'.obj)) :
    IsWeakSerreClass A' :=
  by
    let _ := hpush_mem
    let _ := hpush_exact
    let _ := hunit
    simpa using
      targetWeakSerreSubcategory_of_pullbackEquivalence_of_pushforwardExact
        ε A' A hpull_mem hpush_mem hpush_exact hunit

end

/-
Lemma 21.29.1 (2): under the topology-comparison hypotheses from part `(1)` and the bounded-
cohomology hypotheses from Lemma `21.28.6`, the canonical functor
`modulePullbackDerivedOfFlatWithCohomologyIn ε A' A hpull_mem` is an equivalence. This theorem
exposes the owner statement from Lemma `21.28.6` after deriving the target weak-Serre structure
from part `(1)`, rather than reintroducing inline `ObjectProperty.lift` wrappers for the
underived or derived pullback functors. -/
section

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

variable (hpush_mem : ∀ ⦃ℱ : ModX⦄, A ℱ → A' (ε.modulePushforward.obj ℱ))
variable [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategories ε A' A hpull_mem)]
variable (hpush_exact : exactFunctor A.FullSubcategory ModY
  (A.ι ⋙ ε.modulePushforward))
variable (hunit : ∀ ℱ' : A'.FullSubcategory,
  IsIso ((SheafOfModules.pullbackPushforwardAdjunction ε.structureSheafMap).unit.app ℱ'.obj))

local instance : IsWeakSerreClass A' :=
  instTargetWeakSerreSubcategoryOfPullbackEquivalenceOfPushforwardExact
    ε A' A hpull_mem hpush_mem hpush_exact hunit

theorem modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence_of_topologyComparison
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisY : BoundedCohomologyBasis Y.structureSheaf A')
    (hunitDerived : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction ε).unit.app
          ((DerivedCategory.singleFunctor ModY (0 : ℤ)).obj ℱ'.obj))) :
    Functor.IsEquivalence
      ((modulePullbackDerivedOfFlatWithCohomologyIn ε A' A hpush_mem) : D_{A'} ⥤ D_{A}) :=
  modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence basisX basisY hunitDerived

instance instModulePullbackDerivedOfFlatWithCohomologyInIsEquivalenceOfTopologyComparison
    (basisX : BoundedCohomologyBasis X.structureSheaf A)
    (basisY : BoundedCohomologyBasis Y.structureSheaf A')
    (hunitDerived : ∀ ℱ' : A'.FullSubcategory,
      IsIso
        ((modulePullbackDerived_pushforward_adjunction ε).unit.app
          ((DerivedCategory.singleFunctor ModY (0 : ℤ)).obj ℱ'.obj))) :
    Functor.IsEquivalence
      ((modulePullbackDerivedOfFlatWithCohomologyIn ε A' A hpush_mem) : D_{A'} ⥤ D_{A}) :=
  letI : Functor.IsEquivalence
      ((modulePullbackDerivedOfFlatWithCohomologyIn ε A' A hpush_mem) : D_{A'} ⥤ D_{A}) :=
    modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence_of_topologyComparison
      hpush_mem hpush_exact hunit basisX basisY hunitDerived
  inferInstance

end

end

end RingedSite.Hom
