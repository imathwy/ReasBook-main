import Mathlib
import StacksProject_2024.Internal.Chap04.FibredInSetoidsTwoFibreProduct
import StacksProject_2024.Internal.Chap08.StackInSetoidsTwoFibreProductSquare
import StacksProject_2024.Chap08.Lemma_8_5_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 8.6.6:
- primary domain: stacks in setoids over a site and their bicategorical `2`-fibre products;
- inspected owner-level declarations:
  `StackInSetoidsOver`,
  `FibredInSetoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProductSquare`,
  `StackInSetoidsOver.ofStackInGroupoidsSquare`,
  `Bicategory.IsFinal`;
- best owner abstraction: the source-facing square in `StackInSetoidsOver J` should be obtained by
  restricting the canonical stack-in-groupoids pullback square to the full sub-`2`-category of
  stacks in setoids, while the setoid-side primitive owner data is taken directly from the
  Chapter 4 owner `FibredInSetoidsOver.twoFibreProduct`;
- primitive data: the Chapter 4 setoid pullback owner `FibredInSetoidsOver.twoFibreProduct`
  together with the Chapter 8 ambient stack pullback square;
- derived API: the canonical square in `StackInSetoidsOver J` and the `Bicategory.IsFinal`
  statement expressing the `2`-fibre-product property.

Source/core/bridge triage:
- `source-facing`: `StackInSetoidsOver.twoFibreProduct`,
  `StackInSetoidsOver.twoFibreProductSquare`, and
  `StackInSetoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `FibredInSetoidsOver.twoFibreProduct`,
  `StackInGroupoidsOver.twoFibreProductSquare`, and `Bicategory.IsFinal`;
- `bridge/view`: `StackInSetoidsOver.ofStackInGroupoidsSquare`, which restricts the ambient square
  to the full sub-`2`-category of stacks in setoids. -/

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackInSetoidsOver J}
variable (F : X ⟶ S) (G : Y ⟶ S)

namespace StackInSetoidsOver

-- Proof sketch: compare the Chapter 8 stack-in-groupoids pullback with the Chapter 4 owner
-- `FibredInSetoidsOver.twoFibreProduct`, whose projection is already fibred in setoids.
/-- The ambient stack-in-groupoids pullback of morphisms of stacks in setoids is fibred in
setoids. -/
private theorem ambientTwoFibreProduct_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids
      (StackInGroupoidsOver.twoFibreProduct
        (toStackInGroupoidsHom F)
        (toStackInGroupoidsHom G)).p := sorry

/-- The canonical `2`-fibre product of stacks in setoids over `(C, J)`, obtained by equipping the
Chapter 8 stack pullback owner `StackInGroupoidsOver.twoFibreProduct` with the fiberwise setoid
structure supplied by the Chapter 4 owner `FibredInSetoidsOver.twoFibreProduct`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    StackInSetoidsOver J :=
  ⟨StackInGroupoidsOver.twoFibreProduct
      (toStackInGroupoidsHom F)
      (toStackInGroupoidsHom G),
    ambientTwoFibreProduct_isFibredInSetoids F G⟩

/- The ambient stack-in-groupoids pullback square, recorded with its exact owner-level type to
avoid repeated coercion and reduction work during elaboration. -/
private noncomputable abbrev ambientTwoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F.obj.obj G.obj.obj :=
  StackInGroupoidsOver.twoFibreProductSquare F.obj.obj G.obj.obj

-- Proof sketch: the apex of the canonical ambient stack-in-groupoids pullback square is the same
-- pullback owner as above, so its projection is again fibred in setoids.
/-- The apex of the canonical ambient stack-in-groupoids pullback square is fibred in setoids. -/
private theorem ambientTwoFibreProductSquare_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids
      (ambientTwoFibreProductSquare F G).obj.p := sorry

/-- The canonical `2`-commutative square in `StackInSetoidsOver J`, obtained by restricting the
canonical stack-in-groupoids pullback square to the full sub-`2`-category of stacks in setoids
through the Chapter 8 bridge `ofStackInGroupoidsSquare`. -/
@[irreducible] noncomputable def twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  ofStackInGroupoidsSquare (F := F) (G := G)
    (ambientTwoFibreProductSquare F G)
    (ambientTwoFibreProductSquare_isFibredInSetoids F G)

-- Proof sketch: start from the canonical stack-in-groupoids pullback square, whose finality is
-- Lemma `8.5.6`, and restrict that universal property to the full sub-`2`-category of stacks in
-- setoids using the bridge `ofStackInGroupoidsSquare`.
/-- Lemma 8.6.6: the `2`-category of stacks in setoids over the site `(C, J)` has `2`-fibre
products, and the canonical square `twoFibreProductSquare F G` is described by the same explicit
pullback model as in Categories, Lemma `4.32.3`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := sorry

end StackInSetoidsOver

end

end CategoryTheory
