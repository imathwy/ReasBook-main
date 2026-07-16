import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_2
import StacksProject_2024.stacks_project.Chap20.«20_2_0_4»
import StacksProject_2024.stacks_project.Chap20.«20_3_0_4»
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.stacks_project.Chap21.Lemma_21_12_2
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_6
import StacksProject_2024.stacks_project.Chap21.Lemma_21_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open DerivedCategory.TStructure
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom
open scoped RingedSiteCohomology
open scoped RingedSiteDerived

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(f _*).Additive]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]

local notation "Xrs" => opensRingedSite X
local notation "Yrs" => opensRingedSite Y
local notation "frs" => opensRingedSiteHom f
local notation "JY" => Opens.grothendieckTopology Y.carrier
local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)
local notation "DModX" => D⁺(ModX)

local instance ringedSpaceModules_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u} (RingedSpace.Modules X) :=
  sheafModules_isGrothendieckAbelian X

local instance opensRingedSite_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u} (RingedSite.Hom.ModuleCat Xrs) := by
  change IsGrothendieckAbelian.{u} (RingedSpace.Modules X)
  infer_instance

/-- Helper for Lemma 20.7.3: the degree-zero objectwise cohomology presheaf on the opens ringed
site is the usual cohomology presheaf of the underlying abelian sheaf. -/
private theorem singleObjectwiseCohomologyPresheaf_isomorphic_cohomologyPresheaf
    (ℱ : ModX) (p : ℕ) :
    IsIsomorphic
      (RingedSite.Hom.objectwiseCohomologyPresheaf Xrs ((single0).obj ℱ) (p : ℤ))
      (((moduleUnderlyingSheaf X).obj ℱ).cohomologyPresheaf p) := by
  -- Proof comment: specialize the canonical right-derived/sheaf-cohomology-presheaf comparison to
  -- the underlying abelian sheaf of `ℱ`.
  simpa
    [RingedSite.Hom.objectwiseCohomologyPresheaf,
      RingedSite.Hom.underlyingAbelianPresheafDerived,
      RingedSite.Hom.underlyingAbelianPresheafFunctor,
      RingedSite.Hom.underlyingAbelianSheafFunctor,
      moduleUnderlyingSheaf,
      moduleUnderlyingPresheaf]
    using
      (SheafOfModules.cohomologyPresheaf_toPresheaf_isomorphic X.ringCatSheaf ℱ p)

/-- Helper for Lemma 20.7.3: the bounded-below ringed-space cohomology sheaf agrees with the
opens-site cohomology sheaf after comparing the bounded and unbounded right-derived values. -/
private theorem boundedBelowUnderlyingCohomologySheafIso
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
      (boundedBelowHomotopyQuasiIso ModX)]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.modulePushforwardToDerived frs)
      (RingedSite.Hom.ModuleQis Xrs)]
    (K : DModX) (i : ℤ) :
    IsIsomorphic
      ((moduleUnderlyingSheaf Y).obj
        ((DerivedCategory.homologyFunctor ModY i).obj
          (((Hom.modulePushforwardDerivedPlus f).obj K).toDerived)))
      (RingedSite.Hom.underlyingAbelianCohomologySheaf Yrs
        ((RingedSite.Hom.modulePushforwardDerived frs).obj K.toDerived) i) := by
  -- Proof comment: the bounded-below direct image is compared with the unbounded opens-site
  -- right-derived value before taking cohomology and forgetting module structure.
  refine ⟨?_⟩
  simpa [RingedSite.Hom.underlyingAbelianCohomologySheaf, RingedSite.Hom.cohomologySheaf] using
    (moduleUnderlyingSheaf Y).mapIso
      ((DerivedCategory.homologyFunctor ModY i).mapIso
        ((CategoryTheory.right_derived_value_comparison_iso_bounded_below
          (KtoD := RingedSite.Hom.modulePushforwardToDerived frs)
          (KplusToDplus := mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
          (Qis := RingedSite.Hom.ModuleQis Xrs)
          K).symm))

/-- Lemma 20.7.3: for a morphism of ringed spaces `f : X ⟶ Y` and an `𝒪_X`-module
`𝓕`, the underlying abelian sheaf of `R^p f_* 𝓕`, written in Lean as
`R^{p}_[f](ℱ)`, is the sheaf associated to the presheaf `V ↦ H^p(f⁻¹(V), 𝓕)` on `Y`.
-/
@[stacks 01E4]
theorem higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology
    (ℱ : RingedSpace.Modules X) (p : ℕ) :
    IsIsomorphic
      ((moduleUnderlyingSheaf Y).obj (R^{p}_[f](ℱ)))
      ((presheafToSheaf JY AddCommGrpCat.{u}).obj
        ((TopologicalSpace.Opens.map f.hom.base).op ⋙
          (((moduleUnderlyingSheaf X).obj ℱ).cohomologyPresheaf p))) := by
  letI :
      Functor.HasRightDerivedFunctor
        (RingedSite.Hom.modulePushforwardToDerived frs)
        (RingedSite.Hom.ModuleQis Xrs) := by
    infer_instance
  -- Proof comment: use the ringed-site degree-zero specialization from Chapter 21, then replace
  -- the source presheaf by the usual cohomology presheaf of the underlying abelian sheaf.
  rcases
      RingedSite.Hom.sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianHigherDirectImageModule
        (f := frs) ℱ p with
    ⟨eSource⟩
  rcases
      singleObjectwiseCohomologyPresheaf_isomorphic_cohomologyPresheaf
        (X := X) ℱ p with
    ⟨ePresheafSource⟩
  let ePresheaf :
      ((TopologicalSpace.Opens.map f.hom.base).op ⋙
        RingedSite.Hom.objectwiseCohomologyPresheaf Xrs ((single0).obj ℱ) (p : ℤ)) ≅
      ((TopologicalSpace.Opens.map f.hom.base).op ⋙
        (((moduleUnderlyingSheaf X).obj ℱ).cohomologyPresheaf p)) :=
    Functor.isoWhiskerLeft (TopologicalSpace.Opens.map f.hom.base).op
      ePresheafSource
  exact ⟨eSource.symm ≪≫ (presheafToSheaf JY AddCommGrpCat.{u}).mapIso ePresheaf⟩

omit [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
  [HasInjectiveResolutions (RingedSpace.Modules X)] in
/-- Companion to Lemma 20.7.3: for a bounded-below complex `K`, the underlying abelian sheaf of
`H^i(Rf_* K)` is the sheaf associated to the presheaf `V ↦ H^i(f⁻¹(V), K)`. -/
theorem boundedBelowDerivedPushforwardCohomologySheaf_underlyingSheaf_is_sheafification_of_objectwise_cohomology
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
      (boundedBelowHomotopyQuasiIso ModX)]
    (K : DModX) (i : ℤ) :
    IsIsomorphic
      ((moduleUnderlyingSheaf Y).obj
        ((DerivedCategory.homologyFunctor ModY i).obj
          (((Hom.modulePushforwardDerivedPlus f).obj K).toDerived)))
      ((presheafToSheaf JY AddCommGrpCat.{u}).obj
        ((TopologicalSpace.Opens.map f.hom.base).op ⋙
          RingedSite.Hom.objectwiseCohomologyPresheaf Xrs K.toDerived i)) := by
  letI :
      Functor.HasRightDerivedFunctor
        (RingedSite.Hom.modulePushforwardToDerived frs)
        (RingedSite.Hom.ModuleQis Xrs) := by
    infer_instance
  -- Proof comment: first normalize the target to the unbounded opens-site cohomology sheaf, then
  -- apply the ringed-site sheafification theorem to `K.toDerived`.
  rcases boundedBelowUnderlyingCohomologySheafIso (f := f) K i with ⟨eTarget⟩
  rcases
      RingedSite.Hom.sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_underlyingAbelianCohomologySheaf
        (f := frs) K.toDerived i with
    ⟨eSource⟩
  exact ⟨eTarget ≪≫ eSource.symm⟩

end

end AlgebraicGeometry.RingedSpace
