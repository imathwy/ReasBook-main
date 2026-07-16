import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Internal.Chap08.StackInGroupoidsTwoFibreProductSquare
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_7
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_5
import StacksProject_2024.stacks_project.Chap08.Lemma_8_4_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 8.5.6:
- primary domain: stacks in groupoids over a site and their bicategorical `2`-fibre products;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProductSquare`,
  `StackInGroupoidsOver`,
  `stackTwoFibreProduct_isStack`,
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- best owner abstraction: the pullback object is owned upstream by
  `FibredInGroupoidsOver.twoFibreProduct F G`; this file should add only the owner-level
  rebundling `StackInGroupoidsOver.twoFibreProduct F G`, with the comparison square stated in the
  stack bicategory and its legs reused directly from the ambient owner projections;
- primitive data: the fibred-in-groupoids `2`-fibre product and its canonical projections;
- derived API: the owner-level bundled view `StackInGroupoidsOver.twoFibreProduct` and the
  resulting based-functor square.

Source/core/bridge triage:
- `source-facing`: `StackInGroupoidsOver.twoFibreProductSquare` and
  `StackInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `FibredInGroupoidsOver.twoFibreProduct F G`,
  `FibredInGroupoidsOver.twoFibreProductSquare F G`, and
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- `bridge/view`: the rebundled stack owner `StackInGroupoidsOver.twoFibreProduct F G`. -/

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackInGroupoidsOver J}
variable (F : X ⟶ S) (G : Y ⟶ S)

namespace StackInGroupoidsOver

/-- The canonical `2`-fibre product of stacks in groupoids over `(C, J)`, obtained by bundling
the chapter-level owner `FibredInGroupoidsOver.twoFibreProduct` as an object of the full
sub-`2`-category `StackInGroupoidsOver J`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    StackInGroupoidsOver J :=
  ⟨FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom, inferInstance⟩

/- The canonical `2`-commutative square in the bicategory of stacks in groupoids over `(C, J)`,
formed by restricting the chapter-level pullback owner of the stack morphisms `F` and `G`. -/
noncomputable abbrev twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  mkTwoFibreProductSquare F G
    (show IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct F.toFibredCategoryMor G.toFibredCategoryMor).p from
        inferInstance)

/- The canonical square `twoFibreProductSquare F G` is a bicategorical `2`-fibre product in
the bicategory of stacks in groupoids over `(C, J)`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  sorry

end StackInGroupoidsOver

/- Lemma 8.5.6 reuses the ambient explicit `2`-fibre-product theorem from Categories,
Lemma `4.32.3`, already formalized as `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`. -/
recall CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct

end

end CategoryTheory
