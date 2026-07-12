import StacksProject_2024.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/- Domain-style sampling for Lemma 20.32.2:
- primary domain: restriction of derived `𝒪_X`-modules to an open subspace, viewed in the
  intrinsic derived category `D(𝒪_U)`;
- sampled owner declarations:
  `moduleRestrictionToOpenDerived`,
  `restrictedModuleDerivedOnOpen`;
- best owner abstraction:
  `source-facing`: the restriction of a derived `𝒪_X`-module to the open subspace `U`;
  `core/canonical`: the chapter-level exact derived restriction functor
    `moduleRestrictionToOpenDerived`;
  `bridge/view`: this item's proposition-level canonical comparison between the functorial
    restriction and the intrinsic restricted object `K↾[U]`.
-/

/-- Lemma 20.32.2: for `K : D(𝒪_X)`, the functorial derived restriction of `K` to `U` is
canonically isomorphic to the intrinsic restricted derived object `K↾[U]` on `X|_U`. -/
@[stacks 0D5V]
theorem moduleRestrictionToOpenDerived_obj_isomorphic_restrictedModuleDerivedOnOpen
    (K : DModX) :
    IsIsomorphic ((moduleRestrictionToOpenDerived X U).obj K) (K↾[U]) := by
  refine
    ⟨(moduleRestrictionToOpenDerived X U).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫ ?_⟩
  simpa [restrictedModuleDerivedOnOpen] using
    moduleRestrictionToOpenDerivedFactors X U (DerivedCategory.Q.objPreimage K)

end

end AlgebraicGeometry.RingedSpace
