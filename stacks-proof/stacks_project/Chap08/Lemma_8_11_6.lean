import Mathlib
import stacks_project.Chap08.Definition_8_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ Zₛ : StackInGroupoidsOver J}

-- Proof sketch: by Lemma `8.11.3`, a gerbe morphism is exactly a morphism that is locally
-- essentially surjective on objects and locally lifts fiber morphisms. These local conditions are
-- stable under composition after refining covers, so they apply to `F ≫ G`.
/-- Lemma 8.11.6: if `F : Xₛ ⟶ Yₛ` and `G : Yₛ ⟶ Zₛ` are gerbes over their targets, then the
composite `F ≫ G : Xₛ ⟶ Zₛ` is again a gerbe over `Zₛ`. -/
theorem isGerbeOver_comp
    (F : Xₛ ⟶ Yₛ) (G : Yₛ ⟶ Zₛ)
    (hF : StackInGroupoidsOver.Hom.IsGerbeOver F)
    (hG : StackInGroupoidsOver.Hom.IsGerbeOver G) :
    StackInGroupoidsOver.Hom.IsGerbeOver (F ≫ G) := by
  sorry

end CategoryTheory
