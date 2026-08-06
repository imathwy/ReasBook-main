import Mathlib.CategoryTheory.Yoneda

open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C]
variable {Z : C} {k' : Cᵒᵖ ⥤ Type v}

-- Semantic recall via `lean_leansearch`: `CategoryTheory.yonedaEquiv` is the canonical
-- Yoneda-lemma equivalence between natural transformations from `yoneda.obj Z`
-- and elements of the target presheaf evaluated at `Z`.

/- Lemma 22.5.1: Yoneda lemma. The canonical equivalence is
`yonedaEquiv : (yoneda.obj Z ⟶ k') ≃ k'.obj (op Z)`. -/
#check (yonedaEquiv : (yoneda.obj Z ⟶ k') ≃ k'.obj (op Z))

/- Evaluating `yonedaEquiv` on a natural transformation is evaluation at `𝟙 Z`. -/
#check
  (yonedaEquiv_apply :
    ∀ f : yoneda.obj Z ⟶ k', yonedaEquiv f = f.app (op Z) (𝟙 Z))
