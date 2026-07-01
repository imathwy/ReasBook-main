import Mathlib
import stacks_project.Chap04.Definition_4_44_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Bicategory

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 4.44.2:
- primary domain: dotted-arrow categories attached to bicategorical `2`-commutative squares;
- owner abstractions inspected: `BicategoricalTwoCommutativeSquare`, `Bicategory.IsFinal`,
  `LeftLift.whiskering`, and `DottedArrow.postcomposeFunctor`;
- source/core/bridge triage:
  `source-facing`: postcomposition on dotted-arrow categories along a right square,
  `core/canonical`: `Functor.IsEquivalence (DottedArrow.postcomposeFunctor S φ)` under the
  owner hypothesis that the right square is bicategorically final,
  `bridge/view`: the underlying `LeftLift` whiskering picture from which dotted arrows are the
  source-facing refinement;
- primitive data: a source square `S : BicategoricalTwoCommutativeSquare y p` and a right-square
  comparison `φ : p ≫ g ≅ q ≫ f`;
- derived API: the outer square `S.postcompose φ`, the induced functor
  `DottedArrow.postcomposeFunctor S φ`, and its equivalence property under
  `[Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)]`. -/

namespace DottedArrow

section

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable (S : BicategoricalTwoCommutativeSquare y p)
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}

/-- Lemma 4.44.2: if the right square `⟨X', q, p, φ.symm⟩` is `2`-cartesian, then
postcomposition with that square induces an equivalence on dotted-arrow categories. -/
noncomputable instance postcomposeFunctor_isEquivalence
    (φ : p ≫ g ≅ q ≫ f)
    [Bicategory.IsFinal (⟨X', q, p, φ.symm⟩ : BicategoricalTwoCommutativeSquare f g)] :
    (postcomposeFunctor S φ).IsEquivalence := sorry

end

end DottedArrow

end CategoryTheory
