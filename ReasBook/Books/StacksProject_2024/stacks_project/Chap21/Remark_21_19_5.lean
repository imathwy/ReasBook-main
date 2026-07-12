import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import StacksProject_2024.Chap13.Lemma_13_30_1
import StacksProject_2024.Chap18.Definition_18_31_1
import StacksProject_2024.Chap21.Lemma_21_19_1
import StacksProject_2024.Chap21.Remark_21_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Remark 21.19.5:
- primary domain: unbounded derived base-change for module sheaves on ringed sites, specialized to
  two horizontally composable squares;
- sampled owner declarations:
  `RingedSite.Hom.IsUnboundedBaseChangeMap`,
  `RingedSite.Hom.unboundedBaseChangeMap`,
  `CategoryTheory.IsDerivedBaseChangeMap`,
  `CategoryTheory.derivedBaseChangeMap`,
  `RingedSite.Hom.modulePullbackDerived`,
  `RingedSite.Hom.modulePushforwardDerived`;
- best owner abstraction: the source-facing owner is the canonical morphism
  `unboundedBaseChangeMap` specialized to the ringed-site square from Remark `21.19.3`, with the
  predicate `IsUnboundedBaseChangeMap` retained as the proof-oriented characterization; the only genuinely
  local datum here is the bridge isomorphism identifying the outer pullback with the iterated
  pullback through the two adjacent squares;
- primitive data: the two square pullback comparisons `hpull0`, `hpull1`, the composition
  comparisons `hcomp`, `gcomp`, the canonical derived pullback-pushforward adjunction owner
  `modulePullbackDerived_pushforward_adjunction`, and the two square-wise
  base-change morphisms;
- derived API: the horizontal-composition criterion and its specialization to the canonical
  base-change maps.

Primitive data versus derived API:
- primitive data: the two component base-change morphisms `η0`, `η1` and the four comparison
  isomorphisms;
- derived API: the source-facing outer-rectangle base-change condition. There is no need for a
  second public owner for the explicit composite morphism.

Source/core/bridge triage:
- `source-facing`: the canonical-map specialization
  `horizontalComposite_unboundedBaseChangeMap_spec`;
- `core/canonical`: `CategoryTheory.IsDerivedBaseChangeMap` and
  `CategoryTheory.derivedBaseChangeMap`;
- `bridge/view`: `outerRectanglePullbackIso`, which packages the associator-whiskering comparison
  for the outer rectangle, together with the helper theorem
  `horizontalComposite_isUnboundedBaseChangeMap`. -/

section

variable {X2 X1 X0 Y2 Y1 Y0 : RingedSite.{u, v}}
variable (g1 : X2 ⟶ X1) (g0 : X1 ⟶ X0)
variable (f2 : X2 ⟶ Y2) (f1 : X1 ⟶ Y1) (f0 : X0 ⟶ Y0)
variable (h1 : Y2 ⟶ Y1) (h0 : Y1 ⟶ Y0)

variable [HasWeakSheafify X0.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify X1.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify X2.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y1.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y2.siteTopology AddCommGrpCat.{max u v}]
variable [X0.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [X1.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [X2.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y1.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [Y2.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v} f0.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} f1.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} f2.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g0.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} g1.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} h0.structureSheafMap.hom).IsRightAdjoint]
variable [(PresheafOfModules.pushforward.{max u v} h1.structureSheafMap.hom).IsRightAdjoint]
variable [((PresheafOfModules.pushforward.{max u v}
  (g1 ≫ g0).structureSheafMap.hom)).IsRightAdjoint]
variable [((PresheafOfModules.pushforward.{max u v}
  (h1 ≫ h0).structureSheafMap.hom)).IsRightAdjoint]

variable [f0.modulePushforward.Additive]
variable [f1.modulePushforward.Additive]
variable [f2.modulePushforward.Additive]

variable [Functor.Additive (SheafOfModules.pullback.{max u v} f0.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f1.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f2.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g0.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} g1.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} h0.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} h1.structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} (g1 ≫ g0).structureSheafMap)]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} (h1 ≫ h0).structureSheafMap)]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f0) (ModuleQis X0)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f1) (ModuleQis X1)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f2) (ModuleQis X2)]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f0) (ModuleQis Y0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f1) (ModuleQis Y1)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f2) (ModuleQis Y2)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g0) (ModuleQis X0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g1) (ModuleQis X1)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h0) (ModuleQis Y0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h1) (ModuleQis Y1)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (g1 ≫ g0)) (ModuleQis X0)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (h1 ≫ h0)) (ModuleQis Y0)]

/-- Helper for Remark `21.19.5`: the horizontal composite of two inner base-change morphisms. -/
private noncomputable def horizontalCompositeMap
    (hcomp :
      L((h1 ≫ h0))^* ≅
        L(h0)^* ⋙ L(h1)^*)
    (gcomp :
      L((g1 ≫ g0))^* ≅
        L(g0)^* ⋙ L(g1)^*)
    (K : ModuleDerived X0)
    (η0 :
      ((L(h0)^*).obj ((R(f0)_*).obj K)) ⟶
        ((R(f1)_*).obj ((L(g0)^*).obj K)))
    (η1 :
      ((L(h1)^*).obj
          ((R(f1)_*).obj ((L(g0)^*).obj K))) ⟶
        ((R(f2)_*).obj
          ((L(g1)^*).obj ((L(g0)^*).obj K)))) :
    ((L((h1 ≫ h0))^*).obj ((R(f0)_*).obj K)) ⟶
      ((R(f2)_*).obj ((L((g1 ≫ g0))^*).obj K)) :=
  (hcomp.app ((R(f0)_*).obj K)).hom ≫
    (L(h1)^*).map η0 ≫
    η1 ≫
    (R(f2)_*).map ((gcomp.symm.app K).hom)

/-- Helper for Remark `21.19.5`: the horizontal composite of the two canonical inner base-change
maps. -/
private noncomputable def horizontalCompositeCanonicalMap
    (hpull0 :
      L(h0)^* ⋙ L(f1)^* ≅
        L(f0)^* ⋙ L(g0)^*)
    (hpull1 :
      L(h1)^* ⋙ L(f2)^* ≅
        L(f1)^* ⋙ L(g1)^*)
    (hcomp :
      L((h1 ≫ h0))^* ≅
        L(h0)^* ⋙ L(h1)^*)
    (gcomp :
      L((g1 ≫ g0))^* ≅
        L(g0)^* ⋙ L(g1)^*)
    (K : ModuleDerived X0) :
    ((L((h1 ≫ h0))^*).obj ((R(f0)_*).obj K)) ⟶
      ((R(f2)_*).obj ((L((g1 ≫ g0))^*).obj K)) :=
  horizontalCompositeMap g1 g0 f2 f1 f0 h1 h0 hcomp gcomp K
    (unboundedBaseChangeMap g0 f1 f0 h0 hpull0 K)
    (unboundedBaseChangeMap g1 f2 f1 h1 hpull1 ((L(g0)^*).obj K))

/-- The pullback commutativity isomorphisms for two horizontally composable squares combine to the
pullback commutativity isomorphism for the outer rectangle. -/
noncomputable abbrev outerRectanglePullbackIso
    (hpull0 :
      L(h0)^* ⋙ L(f1)^* ≅
        L(f0)^* ⋙ L(g0)^*)
    (hpull1 :
      L(h1)^* ⋙ L(f2)^* ≅
        L(f1)^* ⋙ L(g1)^*)
    (hcomp :
      L((h1 ≫ h0))^* ≅
        L(h0)^* ⋙ L(h1)^*)
    (gcomp :
      L((g1 ≫ g0))^* ≅
        L(g0)^* ⋙ L(g1)^*) :
    L((h1 ≫ h0))^* ⋙ L(f2)^* ≅
      L(f0)^* ⋙ L((g1 ≫ g0))^* :=
  Functor.isoWhiskerRight hcomp (L(f2)^*) ≪≫
    Functor.associator (L(h0)^*) (L(h1)^*) (L(f2)^*) ≪≫
    Functor.isoWhiskerLeft (L(h0)^*) hpull1 ≪≫
    (Functor.associator (L(h0)^*) (L(f1)^*) (L(g1)^*)).symm ≪≫
    Functor.isoWhiskerRight hpull0 (L(g1)^*) ≪≫
    Functor.associator (L(f0)^*) (L(g0)^*) (L(g1)^*) ≪≫
    Functor.isoWhiskerLeft (L(f0)^*) gcomp.symm

/-- Helper for Remark `21.19.5`: any chosen inner base-change maps can be rewritten to the
canonical derived base-change maps inside the horizontal composite. -/
private lemma horizontalComposite_eq_canonical_of_isUnboundedBaseChangeMap
    (hpull0 :
      L(h0)^* ⋙ L(f1)^* ≅
        L(f0)^* ⋙ L(g0)^*)
    (hpull1 :
      L(h1)^* ⋙ L(f2)^* ≅
        L(f1)^* ⋙ L(g1)^*)
    (hcomp :
      L((h1 ≫ h0))^* ≅
        L(h0)^* ⋙ L(h1)^*)
    (gcomp :
      L((g1 ≫ g0))^* ≅
        L(g0)^* ⋙ L(g1)^*)
    (K : ModuleDerived X0)
    (η0 :
      ((L(h0)^*).obj ((R(f0)_*).obj K)) ⟶
        ((R(f1)_*).obj ((L(g0)^*).obj K)))
    (η1 :
      ((L(h1)^*).obj
          ((R(f1)_*).obj ((L(g0)^*).obj K))) ⟶
        ((R(f2)_*).obj
          ((L(g1)^*).obj ((L(g0)^*).obj K))))
    (hη0 :
      IsUnboundedBaseChangeMap g0 f1 f0 h0 hpull0 K η0)
    (hη1 :
      IsUnboundedBaseChangeMap
        g1 f2 f1 h1 hpull1 ((L(g0)^*).obj K) η1) :
    horizontalCompositeMap g1 g0 f2 f1 f0 h1 h0 hcomp gcomp K η0 η1 =
      horizontalCompositeCanonicalMap
        g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp K := by
  -- Replace the chosen inner maps by the canonical maps from Remark `21.19.3`.
  have h0 := hη0.eq_unboundedBaseChangeMap
  have h1 := hη1.eq_unboundedBaseChangeMap
  subst η0
  subst η1
  rfl


-- Proof sketch: expand the outer pullback commutativity isomorphism by composing the two square
-- isomorphisms with associators, then transpose the canonical composite along the adjunction
-- `L(f2)^* ⊣ R(f2)_*`. The two square-wise formulas reduce the transpose to the pullback of the
-- counit through the outer rectangle.
/-- Helper for Remark `21.19.5`: transposing the composite of the two canonical inner base-change
maps across `L(f2)^* ⊣ R(f2)_*` gives the outer-rectangle counit formula. -/
private lemma horizontalComposite_canonical_transpose
    (hpull0 :
      L(h0)^* ⋙ L(f1)^* ≅
        L(f0)^* ⋙ L(g0)^*)
    (hpull1 :
      L(h1)^* ⋙ L(f2)^* ≅
        L(f1)^* ⋙ L(g1)^*)
    (hcomp :
      L((h1 ≫ h0))^* ≅
        L(h0)^* ⋙ L(h1)^*)
    (gcomp :
      L((g1 ≫ g0))^* ≅
        L(g0)^* ⋙ L(g1)^*)
    (K : ModuleDerived X0) :
    (((modulePullbackDerived_pushforward_adjunction f2).homEquiv
        ((L((h1 ≫ h0))^*).obj ((R(f0)_*).obj K))
        ((L((g1 ≫ g0))^*).obj K)).symm
        (horizontalCompositeCanonicalMap
          g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp K)) =
      ((outerRectanglePullbackIso
          g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp).hom.app
          ((R(f0)_*).obj K) ≫
        (L((g1 ≫ g0))^*).map
          ((modulePullbackDerived_pushforward_adjunction f0).counit.app K)) := by
  sorry

-- Proof sketch: rewrite the chosen inner base-change maps to the canonical ones from Remark
-- `21.19.3`, then invoke the canonical outer-rectangle computation.
/-- If the two inner morphisms satisfy the base-change formula of Remark `21.19.3`, then their
horizontal composite satisfies the base-change formula for the outer rectangle. -/
theorem horizontalComposite_isUnboundedBaseChangeMap
    (hpull0 :
      L(h0)^* ⋙ L(f1)^* ≅
        L(f0)^* ⋙ L(g0)^*)
    (hpull1 :
      L(h1)^* ⋙ L(f2)^* ≅
        L(f1)^* ⋙ L(g1)^*)
    (hcomp :
      L((h1 ≫ h0))^* ≅
        L(h0)^* ⋙ L(h1)^*)
    (gcomp :
      L((g1 ≫ g0))^* ≅
        L(g0)^* ⋙ L(g1)^*)
    (K : ModuleDerived X0)
    (η0 :
      ((L(h0)^*).obj ((R(f0)_*).obj K)) ⟶
        ((R(f1)_*).obj ((L(g0)^*).obj K)))
    (η1 :
      ((L(h1)^*).obj
          ((R(f1)_*).obj ((L(g0)^*).obj K))) ⟶
        ((R(f2)_*).obj
          ((L(g1)^*).obj ((L(g0)^*).obj K))))
    (hη0 :
      IsUnboundedBaseChangeMap g0 f1 f0 h0 hpull0 K η0)
    (hη1 :
      IsUnboundedBaseChangeMap
        g1 f2 f1 h1 hpull1 ((L(g0)^*).obj K) η1) :
    IsUnboundedBaseChangeMap (g1 ≫ g0) f2 f0 (h1 ≫ h0)
      (outerRectanglePullbackIso g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp)
      K
      ((hcomp.hom.app ((R(f0)_*).obj K)) ≫
        (L(h1)^*).map η0 ≫
        η1 ≫
        (R(f2)_*).map (gcomp.inv.app K)) := by
  rw [IsUnboundedBaseChangeMap]
  change
    (((modulePullbackDerived_pushforward_adjunction f2).homEquiv
        ((L((h1 ≫ h0))^*).obj ((R(f0)_*).obj K))
        ((L((g1 ≫ g0))^*).obj K)).symm
        (horizontalCompositeMap g1 g0 f2 f1 f0 h1 h0 hcomp gcomp K η0 η1)) =
      ((outerRectanglePullbackIso
          g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp).hom.app
          ((R(f0)_*).obj K) ≫
        (L((g1 ≫ g0))^*).map
          ((modulePullbackDerived_pushforward_adjunction f0).counit.app K))
  rw [horizontalComposite_eq_canonical_of_isUnboundedBaseChangeMap
      g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp
      K η0 η1 hη0 hη1]
  exact
    horizontalComposite_canonical_transpose
      g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp K

/-- Remark 21.19.5: for two horizontally composable squares of ringed topoi, the composition of
the canonical base-change maps from Remark `21.19.3` is the canonical base-change map for the
outer rectangle. -/
@[stacks 0E47]
theorem horizontalComposite_unboundedBaseChangeMap_spec
    (hpull0 :
      L(h0)^* ⋙ L(f1)^* ≅
        L(f0)^* ⋙ L(g0)^*)
    (hpull1 :
      L(h1)^* ⋙ L(f2)^* ≅
        L(f1)^* ⋙ L(g1)^*)
    (hcomp :
      L((h1 ≫ h0))^* ≅
        L(h0)^* ⋙ L(h1)^*)
    (gcomp :
      L((g1 ≫ g0))^* ≅
        L(g0)^* ⋙ L(g1)^*)
    (K : ModuleDerived X0) :
    ((hcomp.hom.app ((R(f0)_*).obj K)) ≫
      (L(h1)^*).map (unboundedBaseChangeMap g0 f1 f0 h0 hpull0 K) ≫
      unboundedBaseChangeMap g1 f2 f1 h1 hpull1 ((L(g0)^*).obj K) ≫
      (R(f2)_*).map (gcomp.inv.app K)) =
      unboundedBaseChangeMap (g1 ≫ g0) f2 f0 (h1 ≫ h0)
      (outerRectanglePullbackIso g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp)
      K := by
  exact
    (horizontalComposite_isUnboundedBaseChangeMap
      g1 g0 f2 f1 f0 h1 h0
      hpull0 hpull1 hcomp gcomp
      K
      (unboundedBaseChangeMap g0 f1 f0 h0 hpull0 K)
      (unboundedBaseChangeMap g1 f2 f1 h1 hpull1 ((L(g0)^*).obj K))
      (unboundedBaseChangeMap_isUnboundedBaseChangeMap g0 f1 f0 h0 hpull0 K)
      (unboundedBaseChangeMap_isUnboundedBaseChangeMap
        g1 f2 f1 h1 hpull1 ((L(g0)^*).obj K))).eq_unboundedBaseChangeMap

end

end RingedSite.Hom
