import StacksProject_2024.stacks_project.Chap21.Remark_21_19_3_core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1

open CategoryTheory
open ComplexShape
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Remark 21.19.3:
- primary domain: unbounded derived base change for module sheaves on ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.IsUnboundedBaseChangeMap`,
  `RingedSite.Hom.unboundedBaseChangeMap`,
  `CategoryTheory.IsDerivedBaseChangeMap`,
  `CategoryTheory.derivedBaseChangeMap`,
  `CategoryTheory.derivedBaseChangeMap_spec`;
- best owner abstraction:
  `source-facing`: the ringed-site specialization of the canonical derived base-change mate;
  `core/canonical`: `CategoryTheory.IsDerivedBaseChangeMap` and
    `CategoryTheory.derivedBaseChangeMap`;
  `bridge/view`: this file, which records the ringed-site specialization surface and reexports the
    canonical owner through the Chapter 21 ringed-site notation built from
    `modulePullbackDerived_pushforward_adjunction`.
- primitive data: the square comparison isomorphism `L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*`, the
  object `K`, and the canonical derived pullback-pushforward adjunction owners;
- derived API: the predicate and canonical mate obtained by specializing the categorical owner.

This file no longer owns a parallel ringed-site copy of the base-change predicate and map. The
canonical owner now lives upstream in `Remark_21_19_3_core`, and Remark `21.19.3` is expressed as
its ringed-site specialization.
-/

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y')
variable (f : X ⟶ Y) (g : Y' ⟶ Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify X'.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y'.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [X'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y'.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} f'.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g'.structureSheafMap.hom).IsRightAdjoint]

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f'.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g'.structureSheafMap)]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]

variable (hpull : L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*)
variable (K : ModuleDerived X)

/-- Remark 21.19.3, predicate form specialized to the canonical derived adjunctions
`modulePullbackDerived_pushforward_adjunction f` and
`modulePullbackDerived_pushforward_adjunction f'`. -/
abbrev IsUnboundedBaseChangeMap
    (η :
      ((L(g)^*).obj ((R(f)_*).obj K)) ⟶
        ((R(f')_*).obj ((L(g')^*).obj K))) : Prop :=
  IsDerivedBaseChangeMap
    (L(f)^*) (L(f')^*) (L(g)^*) (L(g')^*) (R(f)_*) (R(f')_*)
    (modulePullbackDerived_pushforward_adjunction f)
    (modulePullbackDerived_pushforward_adjunction f')
    hpull
    K
    η

/-- The canonical ringed-site base-change morphism `L(g)^* (R(f)_* K) ⟶ R(f')_* (L(g')^* K)`. -/
noncomputable abbrev unboundedBaseChangeMap :
    ((L(g)^*).obj ((R(f)_*).obj K)) ⟶
      ((R(f')_*).obj ((L(g')^*).obj K)) :=
  derivedBaseChangeMap
    (L(f)^*) (L(f')^*) (L(g)^*) (L(g')^*) (R(f)_*) (R(f')_*)
    (modulePullbackDerived_pushforward_adjunction f)
    (modulePullbackDerived_pushforward_adjunction f')
    hpull
    K

/-- Remark 21.19.3, predicate form: the canonical ringed-site base-change morphism
`L(g)^* (R(f)_* K) ⟶ R(f')_* (L(g')^* K)` satisfies the defining mate formula for an unbounded
base-change map. -/
theorem unboundedBaseChangeMap_isUnboundedBaseChangeMap :
    IsUnboundedBaseChangeMap g' f' f g hpull K
      (unboundedBaseChangeMap g' f' f g hpull K) := by
  simpa [IsUnboundedBaseChangeMap, unboundedBaseChangeMap, IsDerivedBaseChangeMap] using
    (derivedBaseChangeMap_spec
      (L(f)^*) (L(f')^*) (L(g)^*) (L(g')^*) (R(f)_*) (R(f')_*)
      (modulePullbackDerived_pushforward_adjunction f)
      (modulePullbackDerived_pushforward_adjunction f')
      hpull
      K)

/- Applying `Adjunction.homEquiv.symm` to the canonical ringed-site base-change morphism recovers
the pullback of the counit through `hpull`. -/
theorem unboundedBaseChangeMap_spec :
    ((modulePullbackDerived_pushforward_adjunction f').homEquiv
        ((L(g)^*).obj ((R(f)_*).obj K))
        ((L(g')^*).obj K)).symm
        (unboundedBaseChangeMap g' f' f g hpull K) =
      hpull.hom.app ((R(f)_*).obj K) ≫
        (L(g')^*).map ((modulePullbackDerived_pushforward_adjunction f).counit.app K) := by
  simpa using
    (derivedBaseChangeMap_spec
      (L(f)^*) (L(f')^*) (L(g)^*) (L(g')^*) (R(f)_*) (R(f')_*)
      (modulePullbackDerived_pushforward_adjunction f)
      (modulePullbackDerived_pushforward_adjunction f')
      hpull
      K)

/-- Any morphism satisfying the ringed-site unbounded base-change formula is the canonical
`unboundedBaseChangeMap`. -/
theorem IsUnboundedBaseChangeMap.eq_unboundedBaseChangeMap
    {η :
      ((L(g)^*).obj ((R(f)_*).obj K)) ⟶
        ((R(f')_*).obj ((L(g')^*).obj K))}
    (hη : IsUnboundedBaseChangeMap g' f' f g hpull K η) :
    η = unboundedBaseChangeMap g' f' f g hpull K := by
  simpa [IsUnboundedBaseChangeMap, unboundedBaseChangeMap] using
    (hη.eq_derivedBaseChangeMap)

end

end RingedSite.Hom
