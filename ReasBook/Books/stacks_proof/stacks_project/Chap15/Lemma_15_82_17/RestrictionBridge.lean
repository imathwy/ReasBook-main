import Mathlib
import stacks_proof.stacks_project.Chap12.Remark_12_29_2

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "HB" => DerivedCategory.homologyFunctor (ModuleCat B)

/-- Helper for Lemma 15.82.17: restriction of scalars is exact, so it preserves finite limits on
module categories. -/
local instance restrictScalars_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) :=
  ((exactFunctor_iff (ModuleCat.restrictScalars.{u} f)).1 (restrictScalars_exact f)).1

/-- Helper for Lemma 15.82.17: if a `B`-module becomes zero after restricting scalars to `A`,
then it was already zero as a `B`-module. -/
lemma isZero_of_restrictScalars_obj
    (M : ModuleCat B)
    (hM : IsZero ((ModuleCat.restrictScalars f).obj M)) :
    IsZero M := by
  -- Proof comment: restriction of scalars keeps the underlying additive group, so zero objects
  -- reflect along this identity-on-carriers functor.
  letI : Subsingleton ↑((ModuleCat.restrictScalars f).obj M) :=
    ModuleCat.subsingleton_of_isZero hM
  have hsub : Subsingleton ↑M := by
    simpa using
      (inferInstance : Subsingleton ↑((ModuleCat.restrictScalars f).obj M))
  letI : Subsingleton ↑M := hsub
  exact ModuleCat.isZero_of_subsingleton M

/-- Helper for Lemma 15.82.17: restricting scalars from `B` to `A` commutes with homology on the
derived category of modules. -/
noncomputable def restrictScalars_homology_iso
    (L : DModB) (i : ℤ) :
    (HA i).obj (((ModuleCat.restrictScalars f).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars f).obj ((HB i).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eB : (HB i).obj L ≅ K.homology i :=
    ((HB i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app K
  -- Proof comment: compute homology on a chosen cochain model of `L`, compare strict homology
  -- before and after restriction of scalars, and then return to the derived category.
  exact
    (HA i).mapIso
        ((((ModuleCat.restrictScalars f).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          ((ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.restrictScalars f) ≪≫
      (ModuleCat.restrictScalars f).mapIso eB.symm

end

end CategoryTheory
