import Mathlib
import stacks_proof.stacks_project.Chap08.Lemma_8_5_6
import stacks_proof.stacks_project.Chap08.Lemma_8_8_4
import stacks_proof.stacks_project.Chap08.Lemma_8_9_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open StackInGroupoidsOver.Hom

/- Domain-style sampling for Lemma 8.9.3:
- primary domain: stackifications of `2`-fibre products in the stack-in-groupoids specialization
  of Chapter 8;
- inspected owner-level declarations:
  `FibredInGroupoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProduct`,
  `FibredCategoryMor.IsStackification`,
  `CategoryTheory.twoFibreProduct_of_stackifications_isStackification`;
- best owner abstraction: the numbered item should live at the groupoid-specialized source-facing
  layer, with the pullback objects owned by `FibredInGroupoidsOver.twoFibreProduct` on the source
  side and `StackInGroupoidsOver.twoFibreProduct` on the stack side, while the ambient fibred-
  category theorem is reused only as the proof engine;
- primitive data: the source morphisms in `FibredInGroupoidsMor`, the three stackification
  morphisms into stacks in groupoids, the lifted morphisms in `StackInGroupoidsOver`, and the
  comparison `2`-isomorphisms;
- derived API: the ambient fibred-category stackification theorem and the groupoid bridge
  `FibredInGroupoidsMor.toStackFibredCategoryMor`.

Source/core/bridge triage:
- `source-facing`: the groupoid-specialized stackification statement for `2`-fibre products;
- `core/canonical`: `CategoryTheory.twoFibreProduct_of_stackifications_isStackification`;
- `bridge/view`: the coercions from stacks in groupoids to stacks and from
  `FibredInGroupoidsMor` to the ambient owner predicate via
  `FibredInGroupoidsMor.toStackFibredCategoryMor`. -/

namespace FibredInGroupoidsMor

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Z : FibredInGroupoidsOver C}
variable {X' Y' Z' : StackInGroupoidsOver J}

private def toStackAmbientIso
    {A : FibredInGroupoidsOver C}
    {S : StackInGroupoidsOver J}
    {u v : FibredInGroupoidsMor A S.toFibredInGroupoidsOver}
    (e : u ≅ v) :
    (show FibredCategoryMor (A : FibredCategoryOver C) (S : StackOver J) from u) ≅
      (show FibredCategoryMor (A : FibredCategoryOver C) (S : StackOver J) from v) := by
  simpa using
    Functor.mapIso
      (((fibredInGroupoidsOverSubTwoCategory C).hom A S.toFibredInGroupoidsOver).inclusion)
      e

/- The canonical comparison morphism from the `2`-fibre product of `f` and `g` to the
`2`-fibre product of the compatible lifted morphisms `f'` and `g'`. This is the groupoid-valued
bridge to the ambient fibred-category comparison morphism. -/
noncomputable abbrev twoFibreProductOfStackificationsHom
    (f : FibredInGroupoidsMor X Y)
    (g : FibredInGroupoidsMor Z Y)
    (i : FibredInGroupoidsMor X X')
    (j : FibredInGroupoidsMor Y Y')
    (k : FibredInGroupoidsMor Z Z')
    (f' : X' ⟶ Y')
    (g' : Z' ⟶ Y')
    (α : i ≫ f' ≅ f ≫ j)
    (β : k ≫ g' ≅ g ≫ j) :
    FibredInGroupoidsMor
      (FibredInGroupoidsOver.twoFibreProduct f g)
      (StackInGroupoidsOver.twoFibreProduct f' g') := by
  let αF :
      i.toStackFibredCategoryMor ≫ f'.toFibredCategoryMor ≅
        (show FibredCategoryMor (X : FibredCategoryOver C) (Y' : StackOver J) from f ≫ j) := by
    simpa [FibredInGroupoidsMor.toStackFibredCategoryMor] using toStackAmbientIso α
  let βF :
      k.toStackFibredCategoryMor ≫ g'.toFibredCategoryMor ≅
        (show FibredCategoryMor (Z : FibredCategoryOver C) (Y' : StackOver J) from g ≫ j) := by
    simpa [FibredInGroupoidsMor.toStackFibredCategoryMor] using toStackAmbientIso β
  let fS : (X' : StackOver J) ⟶ (Y' : StackOver J) :=
    InducedCategory.Hom.ofFibredCategoryMor f'.toFibredCategoryMor
  let gS : (Z' : StackOver J) ⟶ (Y' : StackOver J) :=
    InducedCategory.Hom.ofFibredCategoryMor g'.toFibredCategoryMor
  exact FibredInGroupoidsMor.ofAmbientHom <|
    CategoryTheory.twoFibreProductOfStackificationsHom
      f g i.toStackFibredCategoryMor j.toStackFibredCategoryMor k.toStackFibredCategoryMor
      fS gS αF βF

/- Lemma 8.9.3: the canonical comparison morphism from the `2`-fibre product of morphisms of
categories fibred in groupoids to the `2`-fibre product of compatible stackifications in
groupoids is itself a stackification. This is the source-facing groupoid specialization of the
ambient fibred-category theorem `twoFibreProduct_of_stackifications_isStackification`. -/
@[stacks 04Y2]
theorem twoFibreProduct_of_stackifications_isStackification
    (f : FibredInGroupoidsMor X Y)
    (g : FibredInGroupoidsMor Z Y)
    (i : FibredInGroupoidsMor X X')
    (j : FibredInGroupoidsMor Y Y')
    (k : FibredInGroupoidsMor Z Z')
    (f' : X' ⟶ Y')
    (g' : Z' ⟶ Y')
    (α : i ≫ f' ≅ f ≫ j)
    (β : k ≫ g' ≅ g ≫ j)
    (hi : FibredCategoryMor.IsStackification i.toStackFibredCategoryMor)
    (hj : FibredCategoryMor.IsStackification j.toStackFibredCategoryMor)
    (hk : FibredCategoryMor.IsStackification k.toStackFibredCategoryMor) :
    FibredCategoryMor.IsStackification
      (twoFibreProductOfStackificationsHom f g i j k f' g' α β).toStackFibredCategoryMor := by
  let αF :
      i.toStackFibredCategoryMor ≫ f'.toFibredCategoryMor ≅
        (show FibredCategoryMor (X : FibredCategoryOver C) (Y' : StackOver J) from f ≫ j) := by
    simpa [FibredInGroupoidsMor.toStackFibredCategoryMor] using toStackAmbientIso α
  let βF :
      k.toStackFibredCategoryMor ≫ g'.toFibredCategoryMor ≅
        (show FibredCategoryMor (Z : FibredCategoryOver C) (Y' : StackOver J) from g ≫ j) := by
    simpa [FibredInGroupoidsMor.toStackFibredCategoryMor] using toStackAmbientIso β
  let fS : (X' : StackOver J) ⟶ (Y' : StackOver J) :=
    InducedCategory.Hom.ofFibredCategoryMor f'.toFibredCategoryMor
  let gS : (Z' : StackOver J) ⟶ (Y' : StackOver J) :=
    InducedCategory.Hom.ofFibredCategoryMor g'.toFibredCategoryMor
  simpa only [twoFibreProductOfStackificationsHom] using
    (CategoryTheory.twoFibreProduct_of_stackifications_isStackification
      f g i.toStackFibredCategoryMor j.toStackFibredCategoryMor k.toStackFibredCategoryMor
      fS gS αF βF hi hj hk)

end

end FibredInGroupoidsMor

end CategoryTheory
