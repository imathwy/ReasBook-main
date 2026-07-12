import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import StacksProject_2024.Chap21.Lemma_21_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

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

/- Domain-style sampling for Lemma 21.19.2:
- primary domain: uniqueness of right adjoints for the derived pullback/pushforward adjunctions on
  module sheaves over ringed sites;
- sampled owner declarations:
  `modulePullbackDerived_pushforward_adjunction`,
  `Adjunction.rightAdjointUniq`,
  `Adjunction.rightAdjointUniq_hom_counit`,
  `AlgebraicGeometry.RingedSpace.moduleDerivedPushforward_compIso`;
- best owner abstraction:
  `source-facing`: `modulePushforwardDerived_compIso`;
  `core/canonical`: the derived adjunction owner of Lemma `21.19.1`, together with
    `Adjunction.rightAdjointUniq`;
  `bridge/view`: the pullback-composition adjunction obtained from the canonical derived
    adjunctions via `Adjunction.ofNatIsoLeft`.
- primitive data: the pullback comparison `hpull`;
- derived API: the source-facing comparison
  `R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_*` and its counit characterization.

Source/core/bridge triage:
- `source-facing`: the comparison `Rg_* ∘ Rf_* ≅ R(g ∘ f)_*`;
- `core/canonical`: the derived pullback-pushforward adjunction together with
  `Adjunction.rightAdjointUniq`;
- `bridge/view`: the ringed-site pullback-composition adjunction built from the canonical derived
  adjunctions via `Adjunction.ofNatIsoLeft`.
-/

private abbrev compPushforwardAdjunction
    (hpull : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*) :
    L((f ≫ g))^* ⊣ R(f)_* ⋙ R(g)_* :=
  ((modulePullbackDerived_pushforward_adjunction g).comp
      (modulePullbackDerived_pushforward_adjunction f)).ofNatIsoLeft hpull

/-- Lemma 21.19.2: for composable morphisms of ringed topoi, formalized here by ringed-site
morphisms `f` and `g`, the derived pushforward of the composite morphism is canonically
isomorphic to the composite `Rg_* ∘ Rf_*`. This is the canonical right-adjoint-uniqueness
comparison attached to the pullback comparison `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` and the canonical
derived pullback-pushforward adjunctions. -/
@[stacks 0D6E]
noncomputable def modulePushforwardDerived_compIso
    (hpull : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*) :
    R(f)_* ⋙ R(g)_* ≅ R((f ≫ g))_* :=
  (compPushforwardAdjunction f g hpull).rightAdjointUniq
    (modulePullbackDerived_pushforward_adjunction (f ≫ g))

/-- The comparison isomorphism from iterated derived pushforward to the derived pushforward of the
composite is characterized by compatibility with the counits of the canonical derived
adjunctions. -/
theorem modulePushforwardDerived_compIso_hom_counit
    (hpull : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*) :
    Functor.whiskerRight
        (modulePushforwardDerived_compIso f g hpull).hom
        (L((f ≫ g))^*) ≫
      (modulePullbackDerived_pushforward_adjunction (f ≫ g)).counit =
        (compPushforwardAdjunction f g hpull).counit := by
  simpa [modulePushforwardDerived_compIso, compPushforwardAdjunction] using
    (Adjunction.rightAdjointUniq_hom_counit
      (compPushforwardAdjunction f g hpull)
      (modulePullbackDerived_pushforward_adjunction (f ≫ g)))

/-- The component of `modulePushforwardDerived_compIso f g hpull` at `K` is the unique morphism
whose image under `L((f ≫ g))^*` identifies the canonical counit of
`modulePullbackDerived_pushforward_adjunction (f ≫ g)` with the counit of the transported
composite adjunction. -/
theorem modulePushforwardDerived_compIso_hom_app_counit
    (hpull : L(g)^* ⋙ L(f)^* ≅ L((f ≫ g))^*)
    (K : ModuleDerived X) :
    (L((f ≫ g))^*).map ((modulePushforwardDerived_compIso f g hpull).hom.app K) ≫
        (modulePullbackDerived_pushforward_adjunction (f ≫ g)).counit.app K =
        (compPushforwardAdjunction f g hpull).counit.app K := by
  simpa using
    congrArg
      (fun η ↦ η.app K)
      (modulePushforwardDerived_compIso_hom_counit f g hpull)

end

end RingedSite.Hom
