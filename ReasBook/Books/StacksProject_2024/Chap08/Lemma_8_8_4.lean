import Mathlib
import stacks_project.Chap04.Lemma_4_44_2
import stacks_project.Chap04.Lemma_4_33_10
import stacks_project.Chap08.Lemma_8_4_6
import stacks_project.Chap08.Lemma_8_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory
open FibredCategoryOver
open scoped Bicategory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

variable {X Y Z : FibredCategoryOver C}
variable {X' Y' Z' : StackOver J}

namespace WideSubcategory

private abbrev toFibredCategoryMor {T S : StackOver J} (f : T ⟶ S) :=
  InducedCategory.Hom.toFibredCategoryMor f

end WideSubcategory

/- Domain-style sampling for Lemma 8.8.4:
- primary domain: stacks over a site together with bicategorical `2`-fibre products of fibred
  categories.
- inspected owner-level declarations:
  `FibredCategoryOver.twoFibreProduct`,
  `FibredCategoryOver.twoFibreProductSquare`,
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `BicategoricalTwoCommutativeSquare.postcompose`,
  `BicategoricalTwoCommutativeSquare.postcomposeRight`.
- best owner abstraction: the canonical comparison map should be derived from the owner square
  `FibredCategoryOver.twoFibreProductSquare` and the terminality of the pullback square for the
  lifted morphisms `f'` and `g'`; the old objectwise fiber construction is only bridge/view data.
- primitive data: the source pullback owner `twoFibreProduct f g`, the stackification maps
  `i`, `j`, `k`, and the ambient comparison `2`-isomorphisms `α`, `β`.
- derived API: the induced square over `f'` and `g'`, the terminal comparison morphism into the
  target pullback owner, and the resulting source-facing stackification theorem.

Source/core/bridge triage:
- `source-facing`: `twoFibreProduct_of_stackifications_isStackification`.
- `core/canonical`: `FibredCategoryOver.twoFibreProductSquare` together with
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `BicategoricalTwoCommutativeSquare.postcompose`,
  `BicategoricalTwoCommutativeSquare.postcomposeRight`.
- `bridge/view`: the induced square below and the terminal morphism
  `twoFibreProductOfStackificationsHom`. -/

private noncomputable def twoFibreProductOfStackificationsSquare
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver)
    (α : i ≫ fF ≅ f ≫ j)
    (β : k ≫ gF ≅ g ≫ j) :
    BicategoricalTwoCommutativeSquare fF gF := by
  simpa using
    (((twoFibreProductSquare f g).postcompose β.symm).symm.postcomposeRight α.symm).symm

/-- The canonical morphism of fibred categories from the explicit `2`-fibre product of `f` and
`g` to the explicit `2`-fibre product of the chosen lifted morphisms `f'` and `g'`. -/
noncomputable def twoFibreProductOfStackificationsHom
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j) :
    FibredCategoryMor
      (twoFibreProduct f g)
      (twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor) := by
  let fF : FibredCategoryMor X'.toFibredCategoryOver Y'.toFibredCategoryOver := f'.toFibredCategoryMor
  let gF : FibredCategoryMor Z'.toFibredCategoryOver Y'.toFibredCategoryOver := g'.toFibredCategoryMor
  let P := twoFibreProductOfStackificationsSquare f g i j k fF gF α β
  let Q := twoFibreProductSquare fF gF
  let _ : Bicategory.IsFinal Q :=
    twoFibreProduct_isTwoFibreProduct fF gF
  exact (show P ⟶ Q from ⊤_ (P ⟶ Q)).hom

-- Proof sketch: apply Lemma `8.4.6` to the chosen lifted morphisms `f' : X' ⟶ Y'` and
-- `g' : Z' ⟶ Y'` to put a stack structure on their explicit `2`-fibre product. The comparison
-- `2`-isomorphisms `α` and `β` already live on the ambient fibred-category morphisms
-- `f'.toFibredCategoryMor` and `g'.toFibredCategoryMor`, so they directly define the square
-- `twoFibreProductOfStackificationsSquare f g i j k f'.toFibredCategoryMor
-- g'.toFibredCategoryMor α β`. The canonical comparison map is
-- then the induced terminal morphism to the owner pullback square
-- `FibredCategoryOver.twoFibreProductSquare f'.toFibredCategoryMor g'.toFibredCategoryMor`.
/-- Lemma 8.8.4: if `i : X ⟶ X'`, `j : Y ⟶ Y'`, and `k : Z ⟶ Z'` are stackifications of fibred
categories over the site `(C, J)`, and if `f' : X' ⟶ Y'` and `g' : Z' ⟶ Y'` are chosen lifts of
`f : X ⟶ Y` and `g : Z ⟶ Y` together with comparison `2`-isomorphisms to the original
composites, then the induced canonical morphism from the explicit `2`-fibre product of `f` and
`g` to the explicit `2`-fibre product of `f'` and `g'` is a stackification. -/
theorem twoFibreProduct_of_stackifications_isStackification
    (f : FibredCategoryMor X Y) (g : FibredCategoryMor Z Y)
    (i : FibredCategoryMor X X') (j : FibredCategoryMor Y Y') (k : FibredCategoryMor Z Z')
    (f' : X' ⟶ Y') (g' : Z' ⟶ Y')
    (α : i ≫ f'.toFibredCategoryMor ≅ f ≫ j)
    (β : k ≫ g'.toFibredCategoryMor ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i)
    (hj : FibredCategoryMor.IsStackification j)
    (hk : FibredCategoryMor.IsStackification k) :
    let target : StackOver J :=
      ⟨twoFibreProduct f'.toFibredCategoryMor g'.toFibredCategoryMor, inferInstance⟩
    FibredCategoryMor.IsStackification
      (show FibredCategoryMor
          (twoFibreProduct f g)
          target
        from twoFibreProductOfStackificationsHom f g i j k f' g' α β) := sorry

end

end CategoryTheory
