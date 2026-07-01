import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

/-
Domain-style sampling:
- primary domain: object properties on a derived category and the full subcategories they define;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.FullSubcategory`,
  `CategoryTheory.derivedCategoryCohomologyInProperty`,
  `SheafOfModules.ChaoticSite.derivedQuasiCoherentProperty`,
  `CategoryTheory.ModulesOnCategory.QC`;
- best owner abstraction: the object property on `D` cut out by the comparison maps, with
  `QC(\mathcal C, \mathcal O)` as the associated full subcategory;
- primitive data: `RGamma`, `derivedRestrict`, and `comparison`;
- derived API: the full subcategory `QC`, with membership unpacked by the inherited field
  `K.property`.

Source/core/bridge triage:
- `source-facing`: the Section `21.43` quasi-coherent condition and its full subcategory;
- `core/canonical`: `ObjectProperty D` and its `FullSubcategory`;
- `bridge/view`: membership in `QC` is read directly through the canonical full-subcategory field
  `K.property`.
-/

section

variable {C : Type u} [Category C]
variable {D : Type v} [Category D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

/-- The object property cutting out those `K ∈ D(\mathcal O)` whose derived restriction
comparison morphisms are isomorphisms on every arrow of `\mathcal C`. -/
def isQuasiCoherent : ObjectProperty D :=
  fun K ↦ ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K)

/-- Definition 21.43.1: `QC(\mathcal C, \mathcal O)` is the full subcategory of `D(\mathcal O)`
consisting of those objects `K` for which, for every arrow `U ⟶ V` in `\mathcal C`, the canonical
derived base-change map `RΓ(V, K) \otimes_{\mathcal O(V)}^{\mathbf L} \mathcal O(U) ⟶ RΓ(U, K)`
is an isomorphism in `D(\mathcal O(U))`. -/
abbrev QC :=
  (isQuasiCoherent 𝒪 RGamma derivedRestrict comparison).FullSubcategory

end

end CategoryTheory.ModulesOnCategory
