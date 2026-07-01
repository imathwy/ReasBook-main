import Mathlib
import stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open Opposite
open AlgebraicGeometry Scheme
open CategoryTheory.DerivedCategory

universe w v u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/- Domain-style sampling for 20.3.0.3:
- primary domain: bounded-below right derived sections of `𝒪_X`-modules on a scheme;
- sampled owner API:
  `t.plus`,
  `boundedBelowDerivedCategory`,
  `ObjectProperty.lift`,
  `Scheme.Modules.toPresheafOfModules`;
- best owner abstraction: the Chapter 20 bounded-below derived-category owner
  `boundedBelowDerivedCategory`, cut out by `t.plus`, with `ObjectProperty.lift` for the
  restriction;
- primitive data: the sections functor on `U` and its ambient total right derived functor;
- derived API: the bounded-below lift of that total right derived functor.

Source/core/bridge triage:
- `source-facing`: the bounded-below derived sections functor `D⁺(X) ⥤ D⁺(Γ(X, U))`;
- `core/canonical`: `boundedBelowDerivedCategory` and `ObjectProperty.lift`;
- `bridge/view`: the underlying-object compatibility theorem for the lifted functor.
-/

/-- The sections functor on `𝒪_X`-modules over the open subset `U`. -/
abbrev sectionsFunctorAtOpen {X : Scheme.{u}} (U : X.Opens) : X.Modules ⥤ ModuleCat ↑(Γ(X, U)) :=
  toPresheafOfModules X ⋙ PresheafOfModules.evaluation _ (.op U)

/-- The total right derived functor of sections on `U` on ambient derived categories. -/
abbrev sectionsTotalRightDerived {X : Scheme.{u}} (U : X.Opens)
    [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{v} (ModuleCat ↑(Γ(X, U)))]
    [((sectionsFunctorAtOpen U)).Additive]
    [Functor.HasRightDerivedFunctor
      (((sectionsFunctorAtOpen U).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat ↑(Γ(X, U))) ℤ ⥤
          DerivedCategory (ModuleCat ↑(Γ(X, U)))))
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))] :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat ↑(Γ(X, U))) :=
  Functor.totalRightDerived
    (((sectionsFunctorAtOpen U).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Q : CochainComplex (ModuleCat ↑(Γ(X, U))) ℤ ⥤
        DerivedCategory (ModuleCat ↑(Γ(X, U)))))
    (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules)
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

/-- 20.3.0.3: the total right derived functor of sections on `U` restricts to a functor
`D⁺(X) ⥤ D⁺(\Gamma(X, U))`. -/
abbrev sectionsTotalRightDerivedBoundedBelow {X : Scheme.{u}} (U : X.Opens)
    [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{v} (ModuleCat ↑(Γ(X, U)))]
    [((sectionsFunctorAtOpen U)).Additive]
    [Functor.HasRightDerivedFunctor
      (((sectionsFunctorAtOpen U).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat ↑(Γ(X, U))) ℤ ⥤
          DerivedCategory (ModuleCat ↑(Γ(X, U)))))
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))]
    (h_boundedBelow :
      ∀ K : boundedBelowDerivedCategory X.Modules,
        (t.plus : ObjectProperty (DerivedCategory (ModuleCat ↑(Γ(X, U)))))
          ((sectionsTotalRightDerived U).obj K.obj)) :
    boundedBelowDerivedCategory X.Modules ⥤
      boundedBelowDerivedCategory (ModuleCat ↑(Γ(X, U))) :=
  ObjectProperty.lift (t.plus : ObjectProperty (DerivedCategory (ModuleCat ↑(Γ(X, U)))))
    (ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory X.Modules)) ⋙
      sectionsTotalRightDerived U)
    h_boundedBelow

-- Proof sketch: this is the specialization of `ObjectProperty.ι_obj_lift_obj` to the lift of the
-- ambient total right derived functor through the bounded-below full subcategory.
/-- The bounded-below lift of the total right derived sections functor has the expected underlying
object in the ambient derived category. -/
theorem sectionsTotalRightDerivedBoundedBelow_obj_obj {X : Scheme.{u}} (U : X.Opens)
    [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{v} (ModuleCat ↑(Γ(X, U)))]
    [((sectionsFunctorAtOpen U)).Additive]
    [Functor.HasRightDerivedFunctor
      (((sectionsFunctorAtOpen U).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat ↑(Γ(X, U))) ℤ ⥤
          DerivedCategory (ModuleCat ↑(Γ(X, U)))))
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))]
    (h_boundedBelow :
      ∀ K : boundedBelowDerivedCategory X.Modules,
        (t.plus : ObjectProperty (DerivedCategory (ModuleCat ↑(Γ(X, U)))))
          ((sectionsTotalRightDerived U).obj K.obj))
    (K : boundedBelowDerivedCategory X.Modules) :
    (ObjectProperty.ι
        (t.plus : ObjectProperty (DerivedCategory (ModuleCat ↑(Γ(X, U)))))).obj
        ((sectionsTotalRightDerivedBoundedBelow U h_boundedBelow).obj K)
      = (sectionsTotalRightDerived U).obj K.obj :=
  rfl

end AlgebraicGeometry.Scheme.Modules
