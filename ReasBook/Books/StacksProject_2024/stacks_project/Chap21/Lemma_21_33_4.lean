import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_19_2
import StacksProject_2024.Chap21.Lemma_21_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.33.4:
- primary domain: compatibility of the relative derived cup product with composition of derived
  pushforwards on module sheaves over ringed sites;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct_comp_commSq`,
  `CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`,
  `RingedSite.Hom.modulePushforwardDerived_compIso`;
- best owner abstraction:
  `source-facing`: the Chapter 21 ringed-site composition law for the relative cup product;
  `core/canonical`: the generic categorical composition owners
    `CategoryTheory.relativeDerivedCupProduct_comp_commSq` and
    `CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated`;
  `bridge/view`: specialization to `ModuleDerived X`, `ModuleDerived Y`, `ModuleDerived Z`, the
    canonical derived adjunctions `L(-)^* ⊣ R(-)_*`, and the canonical pushforward-composition
    comparison `modulePushforwardDerived_compIso`.
- primitive data: the composable morphisms `f`, `g`, the pullback-composition comparison
  `L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*`, and the three pullback-tensor comparison isomorphisms;
- derived API: direct reuse of the two categorical owner theorems in the ringed-site derived
  setting, with `modulePushforwardDerived_compIso_hom_counit` supplying the canonical counit
  compatibility required by the owner abstraction.

Source/core/bridge triage:
- `source-facing`: the ringed-site composition law for the relative cup product;
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_comp_commSq` and
  `CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated`;
- `bridge/view`: the specialization below using
  `modulePullbackDerived_pushforward_adjunction` and `modulePushforwardDerived_compIso`. -/

section

variable {X Y Z : RingedSite.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]

variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [f.modulePushforward.Additive]
variable [g.modulePushforward.Additive]
variable [(modulePushforward (f ≫ g)).Additive]

variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} (f ≫ g).structureSheafMap.hom).IsRightAdjoint]

variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} (f ≫ g).structureSheafMap)]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (f ≫ g)) (ModuleQis X)]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (f ≫ g)) (ModuleQis Z)]

variable (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
variable (tensorMiddle : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
variable (tensorTarget : ModuleDerived Z ⥤ ModuleDerived Z ⥤ ModuleDerived Z)

variable
  (pullbackCompIso : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
  (pullbackTensorIso_f :
    ∀ K L : ModuleDerived Y,
      (modulePullbackDerived f).obj ((tensorMiddle.obj L).obj K) ≅
        ((tensorSource.obj ((modulePullbackDerived f).obj L)).obj
          ((modulePullbackDerived f).obj K)))
  (pullbackTensorIso_g :
    ∀ K L : ModuleDerived Z,
      (modulePullbackDerived g).obj ((tensorTarget.obj L).obj K) ≅
        ((tensorMiddle.obj ((modulePullbackDerived g).obj L)).obj
          ((modulePullbackDerived g).obj K)))
  (pullbackTensorIso_comp :
    ∀ K L : ModuleDerived Z,
      (modulePullbackDerived (f ≫ g)).obj ((tensorTarget.obj L).obj K) ≅
        ((tensorSource.obj ((modulePullbackDerived (f ≫ g)).obj L)).obj
          ((modulePullbackDerived (f ≫ g)).obj K)))

/- The Chapter 21 bridge data for Lemma 21.33.4 consists of the three canonical derived
adjunctions together with the canonical comparison
`R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_*` and its counit compatibility law from Lemma `21.19.2`. -/
#check modulePullbackDerived_pushforward_adjunction f
#check modulePullbackDerived_pushforward_adjunction g
#check modulePullbackDerived_pushforward_adjunction (f ≫ g)
#check modulePushforwardDerived_compIso f g pullbackCompIso
#check modulePushforwardDerived_compIso_hom_counit f g pullbackCompIso

/- Lemma 21.33.4: for composable morphisms of ringed topoi formalized by ringed-site morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z`, the relative cup product for the composite morphism agrees with the
iterated relative cup product after inserting the canonical comparison
`R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_*`. This is the generic owner theorem
`CategoryTheory.relativeDerivedCupProduct_comp_commSq`, used in the Chapter 21 ringed-site
derived setting with the bridge data above. -/
recall CategoryTheory.relativeDerivedCupProduct_comp_commSq

/- Equality-form companion to the previous square-form recall, in the same Chapter 21 ringed-site
derived context and with the same canonical comparison
`modulePushforwardDerived_compIso`. -/
recall CategoryTheory.relativeDerivedCupProduct_comp_eq_iterated

end

end RingedSite.Hom
