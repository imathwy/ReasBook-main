import Mathlib
import StacksProject_2024.Chap18.Definition_18_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

noncomputable section

/-
Domain-style sampling for 19.7.2.1:
- primary domain: sheafification on a site, free abelian presheaves, and the Yoneda lemma;
- sampled owner declarations:
  `ℤ_ G`,
  `sheafificationAdjunction`,
  `(AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv`,
  `yonedaEquiv`;
- best owner abstraction: the project owner `ℤ_ G` for the free abelian presheaf, with this file
  keeping only the derived sheafified Hom-to-sections equivalence;
- primitive data: the site `(C, K)`, the object `X : C`, the sheaf `𝒢`, and the canonical
  sheafification/free/Yoneda equivalences;
- derived API: the composite equivalence below.

Source/core/bridge triage:
- `source-facing`: the sheafified free abelian presheaf
  `(presheafToSheaf K AddCommGrpCat).obj (ℤ_ (yoneda.obj X))`;
- `core/canonical`: `sheafificationAdjunction`, the whiskered free-forgetful adjunction, and
  `yonedaEquiv`;
- `bridge/view`: the composite equivalence below.
-/

/-- 19.7.2.1: morphisms from the free abelian sheaf on `X` to an abelian sheaf `𝒢`
correspond to sections of `𝒢` over `X`. -/
def freeAbelianSheafOn_homEquiv_sections {C : Type u} [Category.{v} C]
    (K : GrothendieckTopology C) [HasWeakSheafify K AddCommGrpCat.{v}]
    (X : C) (𝒢 : Sheaf K AddCommGrpCat.{v}) :
    ((presheafToSheaf K AddCommGrpCat.{v}).obj (ℤ_ (yoneda.obj X)) ⟶ 𝒢) ≃
      𝒢.obj.obj (op X) :=
  (((sheafificationAdjunction K AddCommGrpCat.{v}).homEquiv _ _).trans
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)).trans yonedaEquiv

-- Proof sketch: this is immediate because `freeAbelianSheafOn_homEquiv_sections` is an
-- equivalence, hence bijective as a function.
/-- The comparison map from morphisms out of the free abelian sheaf on `X` to sections over `X`
is bijective. -/
theorem freeAbelianSheafOn_homEquiv_sections_bijective {C : Type u} [Category.{v} C]
    (K : GrothendieckTopology C) [HasWeakSheafify K AddCommGrpCat.{v}]
    (X : C) (𝒢 : Sheaf K AddCommGrpCat.{v}) :
    Function.Bijective (freeAbelianSheafOn_homEquiv_sections K X 𝒢) :=
  (freeAbelianSheafOn_homEquiv_sections K X 𝒢).bijective
