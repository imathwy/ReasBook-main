import Mathlib
import StacksProject_2024.Chap18.Definition_18_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open scoped CategoryTheory.FreeAbelianSheaf

universe u v

noncomputable section

/-
Domain-style sampling for 19.7.2.1:
- primary domain: free abelian sheaves on a site and the Hom-to-sections equivalence for
  representables;
- sampled owner declarations:
  `(ℤ_ G)^#[K]`,
  `sheafificationAdjunction`,
  `Adjunction.homEquiv`,
  `(AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv`,
  `yonedaEquiv`;
- best owner abstraction: no new owner is needed here; the source-facing object is the chapter-18
  free abelian sheaf `(ℤ_ (yoneda.obj X))^#[K]`, and this file only reuses the canonical
  Hom-equivalences coming from sheafification, the whiskered free-forgetful adjunction, and
  Yoneda;
- primitive data: the site `(C, K)`, the object `X : C`, the sheaf `𝒢`, and the canonical
  sheafification/free/Yoneda equivalences;
- derived API: only the composite equivalence below and its canonical bijectivity.

Source/core/bridge triage:
- `source-facing`: the free abelian sheaf `(ℤ_ (yoneda.obj X))^#[K]`;
- `core/canonical`: `sheafificationAdjunction`, the whiskered free-forgetful adjunction, and
  `yonedaEquiv`;
- `bridge/view`: the composite equivalence below, with no separate local owner name.
-/

section

variable {C : Type u} [Category.{v} C]
variable (K : GrothendieckTopology C) [HasWeakSheafify K AddCommGrpCat.{v}]
variable (X : C) (𝒢 : Sheaf K AddCommGrpCat.{v})

/- 19.7.2.1: morphisms from the free abelian sheaf on `X` to an abelian sheaf `𝒢`
correspond to sections of `𝒢` over `X`. This is exactly the direct composite of the canonical
sheafification `homEquiv`, the whiskered free-forgetful `homEquiv`, and `yonedaEquiv`. -/
#check
  ((((sheafificationAdjunction K AddCommGrpCat.{v}).homEquiv _ _).trans
      ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)).trans yonedaEquiv :
    ((ℤ_ (yoneda.obj X))^#[K] ⟶ 𝒢) ≃ 𝒢.obj.obj (op X))

/- Companion check: the source bijection statement is exactly the canonical bijectivity theorem
for the specialized composite equivalence above. -/
#check
  (((((sheafificationAdjunction K AddCommGrpCat.{v}).homEquiv _ _).trans
        ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)).trans yonedaEquiv).bijective :
    Function.Bijective
      ((((sheafificationAdjunction K AddCommGrpCat.{v}).homEquiv _ _).trans
          ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)).trans yonedaEquiv))

end
