import Mathlib
import stacks_project.Chap13.Lemma_13_18_8
import stacks_project.Chap13.Lemma_13_19_8
import stacks_project.Chap13.Definition_13_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open scoped DerivedExt

noncomputable section

universe v u

namespace CochainComplex

section

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.27.2:
- primary domain: morphisms in the derived category of cochain complexes, computed from
  K-injective and K-projective resolutions;
- sampled owner API:
  `CategoryTheory.Abelian.Ext.homAddEquiv`,
  `DerivedCategory.Q.commShiftIso`,
  `DerivedCategory.Qh.mapAddHom`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedBelow_injective`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.ProjectiveResolution`;
- best owner abstraction: the canonical quotient functors
  `HomotopyCategory.quotient 𝒜 (up ℤ)` and `DerivedCategory.Qh`, together with their shift
  compatibilities and the chapter owner bijectivity theorems for bounded-below injective and
  bounded-above projective complexes;
- primitive data: a chosen injective or projective resolution;
- derived API: the owner-level shifted-Hom comparison equivalences
  `InjectiveResolution.extAddEquiv` and `ProjectiveResolution.extAddEquiv`.

Source/core/bridge triage:
- `source-facing`: the Ext-computation statements with a chosen injective or projective
  resolution;
- `core/canonical`: `Q.commShiftIso`, `quotientCompQhIso`, and the owner bijectivity theorems
  for `Qh.mapAddHom`;
- `bridge/view`: the owner-level equivalences below transporting raw Hom-types to `ShiftedHom`.

The local raw-Hom helper abbreviations were duplicate shells around this owner API, so the file
should expose only the source-facing additive bridge equivalences on the chosen resolution owners.
-/

private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) where
  toEquiv := α.homCongr β
  map_add' := by
    intro f g
    simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

namespace InjectiveResolution

variable {Y : CochainComplex 𝒜 ℤ}

/-- Lemma 13.27.2 (1): if `Y^• ⟶ I^•` is an injective resolution, then
`Ext^i_{\mathcal A}(X^•, Y^•)` is computed by the shifted homotopy-category morphisms
`Hom_{K(\mathcal A)}(X^•, I^•[i])` as an additive equivalence. -/
noncomputable def extAddEquiv (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext^i(Q.obj X, Q.obj Y) ≃+ Ext^i((KQ).obj X, (KQ).obj I) :=
  (isoHomCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm).trans
    ((isoHomCongrAddEquiv (Iso.refl _) (asIso (Q.map (I.ι⟦i⟧')))).trans
      ((AddEquiv.ofBijective
          (Qh.mapAddHom : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) →+ _)
          (show Function.Bijective (Qh.map : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) → _) from
            IsKInjective.Qh_map_bijective ((KQ).obj X) (I⟦i⟧))).symm.trans
        (isoHomCongrAddEquiv (Iso.refl _) (((quotient 𝒜 (up ℤ)).commShiftIso i).app I))))

end InjectiveResolution

namespace ProjectiveResolution

variable {X : CochainComplex 𝒜 ℤ}

/-- Lemma 13.27.2 (2): if `P^• ⟶ X^•` is a projective resolution, then
`Ext^i_{\mathcal A}(X^•, Y^•)` is computed by the shifted homotopy-category morphisms out of
`P^•`, equivalently by `Hom_{K(\mathcal A)}(P^•[-i], Y^•)`, as an additive equivalence. -/
noncomputable def extAddEquiv (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext^i(Q.obj X, Q.obj Y) ≃+ Ext^i((KQ).obj P, (KQ).obj Y) :=
  (isoHomCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm).trans
    ((isoHomCongrAddEquiv (asIso (Q.map P.π)).symm (Iso.refl _)).trans
      ((AddEquiv.ofBijective
          (Qh.mapAddHom : ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) →+ _)
          (homotopyCategory_to_derived_bijective_of_boundedAbove_projective P (Y⟦i⟧))).symm.trans
        (isoHomCongrAddEquiv (Iso.refl _) (((quotient 𝒜 (up ℤ)).commShiftIso i).app Y))))

end ProjectiveResolution

end

end CochainComplex
