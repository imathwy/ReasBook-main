import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory

/-- Lemma 21.10.1: an injective abelian sheaf on a site is injective as an object of the category
of abelian presheaves. -/
-- Proof sketch: apply Lemma `12.29.1` to the sheafification adjunction
-- `presheafToSheaf J AddCommGrpCat ⊣ sheafToPresheaf J AddCommGrpCat`. Exactness of abelian
-- sheafification gives preservation of injective objects by the right adjoint.
theorem injective_underlying_abelian_presheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{max u v}) (hF : Injective F) :
    Injective ((sheafToPresheaf J AddCommGrpCat.{max u v}).obj F) := sorry

end CategoryTheory
