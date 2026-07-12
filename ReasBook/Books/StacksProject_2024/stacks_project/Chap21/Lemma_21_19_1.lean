import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap13.Lemma_13_30_1
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.RingedSiteFlatPullbackExact

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped RingedSite.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Fact (IsFlat f)]

/-- The exact-model derived pullback `(f^*).mapDerivedCategory` agrees canonically with the Chapter
21 owner `modulePullbackDerived f`. -/
noncomputable def modulePullbackDerived_exactIso :
    (f^*).mapDerivedCategory ≅ modulePullbackDerived f := by
  let F₀ : ModuleCat Y ⥤ ModuleCat X := f^*
  let F := modulePullbackToDerived f
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso (ModuleCat Y) (up ℤ)) := by
    simpa [F₀] using
      (Functor.isLeftDerivedFunctor_of_inverts
        (HomotopyCategory.quasiIso (ModuleCat Y) (up ℤ))
        F₀.mapDerivedCategory
        F₀.mapDerivedCategoryFactorsh)
  simpa [modulePullbackDerived, modulePullbackToDerived, F, F₀] using
    (Functor.leftDerivedNatIso
      F₀.mapDerivedCategory
      (F.totalLeftDerived
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y)
        (ModuleQis Y))
      F₀.mapDerivedCategoryFactorsh.hom
      (Functor.totalLeftDerivedCounit
        F
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y)
        (ModuleQis Y))
      (ModuleQis Y)
      (Iso.refl F))

noncomputable instance modulePullbackDerived_commShift_of_isFlat :
    (modulePullbackDerived f).CommShift ℤ :=
  Functor.CommShift.ofIso (modulePullbackDerived_exactIso f) ℤ

noncomputable instance modulePullbackDerived_isTriangulated_of_isFlat :
    (modulePullbackDerived f).IsTriangulated := by
  -- The exact-model owner `(f^*).mapDerivedCategory` is triangulated; transport that proof to the
  -- Chapter 21 owner `modulePullbackDerived f`.
  sorry

end

end RingedSite.Hom

namespace RingedSite.Hom

open scoped RingedSiteDerived

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

omit [(modulePushforward f).Additive]
  [(modulePushforwardToDerived f).HasRightDerivedFunctor (ModuleQis X)] in
/-- Helper for Lemma 21.19.1: the chosen owner `modulePullbackDerived f` carries the canonical
total-left-derived-functor structure for `modulePullbackToDerived f`. -/
private instance modulePullbackDerived_isLeftDerivedFunctor :
    (modulePullbackDerived f).IsLeftDerivedFunctor
      ((modulePullbackToDerived f).totalLeftDerivedCounit
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y)
        (ModuleQis Y))
      (ModuleQis Y) := by
  -- The total left derived functor comes with its defining universal-property witness.
  simpa [modulePullbackDerived] using
    (inferInstance :
      (Functor.totalLeftDerived
          (modulePullbackToDerived f)
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y)
          (ModuleQis Y)).IsLeftDerivedFunctor
        ((modulePullbackToDerived f).totalLeftDerivedCounit
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y)
          (ModuleQis Y))
        (ModuleQis Y))

omit [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
  [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
  [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
  [(modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis Y)] in
/-- Helper for Lemma 21.19.1: the chosen owner `modulePushforwardDerived f` carries the canonical
total-right-derived-functor structure for `modulePushforwardToDerived f`. -/
private instance modulePushforwardDerived_isRightDerivedFunctor :
    (modulePushforwardDerived f).IsRightDerivedFunctor
      ((modulePushforwardToDerived f).totalRightDerivedUnit
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
        (ModuleQis X))
      (ModuleQis X) := by
  -- The total right derived functor comes with its defining universal-property witness.
  simpa [modulePushforwardDerived] using
    (inferInstance :
      (Functor.totalRightDerived
          (modulePushforwardToDerived f)
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
          (ModuleQis X)).IsRightDerivedFunctor
        ((modulePushforwardToDerived f).totalRightDerivedUnit
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
          (ModuleQis X))
        (ModuleQis X))

private instance modulePullbackDerived_comp_modulePushforwardDerived_isLeftDerivedFunctor :
    (modulePullbackDerived f ⋙ modulePushforwardDerived f).IsLeftDerivedFunctor
      ((Functor.associator
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y)
          (modulePullbackDerived f)
          (modulePushforwardDerived f)).inv ≫
        Functor.whiskerRight
      ((modulePullbackToDerived f).totalLeftDerivedCounit
            (DerivedCategory.Qh :
              HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y)
            (ModuleQis Y))
          (modulePushforwardDerived f))
      (ModuleQis Y) := by
  -- Route correction: use the owner-level preservation API for postcomposing a left derived
  -- functor with the fixed total right derived functor `Rf_*`.
  -- TODO: discharge this through `Functor.PreservesRightKanExtension` from
  -- `Mathlib/CategoryTheory/Functor/KanExtension/Preserves.lean`. The concrete missing bridge is a
  -- postcomposition-preservation instance for `modulePushforwardDerived f` acting on the right Kan
  -- extension that defines `modulePullbackDerived f`.
  sorry

private instance modulePushforwardDerived_comp_modulePullbackDerived_isRightDerivedFunctor :
    (modulePushforwardDerived f ⋙ modulePullbackDerived f).IsRightDerivedFunctor
      (Functor.whiskerRight
          ((modulePushforwardToDerived f).totalRightDerivedUnit
            (DerivedCategory.Qh :
              HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
            (ModuleQis X))
          (modulePullbackDerived f) ≫
        (Functor.associator
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
          (modulePushforwardDerived f)
          (modulePullbackDerived f)).hom)
      (ModuleQis X) := by
  -- Route correction: use the owner-level preservation API for postcomposing a right derived
  -- functor with the fixed total left derived functor `Lf^*`.
  -- TODO: discharge this through `Functor.PreservesLeftKanExtension` from
  -- `Mathlib/CategoryTheory/Functor/KanExtension/Preserves.lean`. The concrete missing bridge is a
  -- postcomposition-preservation instance for `modulePullbackDerived f` acting on the left Kan
  -- extension that defines `modulePushforwardDerived f`.
  sorry

/-- The canonical derived adjunction `L(f)^* ⊣ R(f)_*` from Lemma 21.19.1. -/
noncomputable def modulePullbackDerived_pushforward_adjunction :
    L(f)^* ⊣ R(f)_* :=
  Adjunction.derived
    (SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).mapHomotopyCategory
    (ModuleQis Y)
    (ModuleQis X)
    ((modulePullbackToDerived f).totalLeftDerivedCounit
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ ModuleDerived Y)
      (ModuleQis Y))
    ((modulePushforwardToDerived f).totalRightDerivedUnit
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
      (ModuleQis X))

/-- Lemma 21.19.1: the unbounded derived pullback is a left adjoint, and the unbounded derived
pushforward is a right adjoint. -/
@[stacks 07A6]
theorem modulePullbackDerived_isLeftAdjoint_and_modulePushforwardDerived_isRightAdjoint :
    Functor.IsLeftAdjoint (L(f)^*) ∧ Functor.IsRightAdjoint (R(f)_*) := by
  let adjD := modulePullbackDerived_pushforward_adjunction f
  constructor
  · exact adjD.isLeftAdjoint
  · exact adjD.isRightAdjoint

/-- Lemma 21.19.1: the unbounded derived pullback is left adjoint to the unbounded derived
pushforward. This is the `L(f)^*` companion to the source-facing adjointness theorem above. -/
@[stacks 07A6]
instance modulePullbackDerived_isLeftAdjoint :
    (L(f)^*).IsLeftAdjoint := by
  exact
    (modulePullbackDerived_isLeftAdjoint_and_modulePushforwardDerived_isRightAdjoint f).1

/-- Companion to Lemma 21.19.1: the unbounded derived pushforward is right adjoint to the
unbounded derived pullback. -/
instance modulePushforwardDerived_isRightAdjoint :
    (R(f)_*).IsRightAdjoint := by
  exact
    (modulePullbackDerived_isLeftAdjoint_and_modulePushforwardDerived_isRightAdjoint f).2

end

end RingedSite.Hom
