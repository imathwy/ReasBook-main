import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ZeroObject

/-
Domain-style sampling:
- primary domain: distinguished triangles in a pretriangulated category, specialized to the cone
  on a fixed morphism `f : X ⟶ Y`;
- sampled owner declarations:
  `Pretriangulated.Triangle.isZero₃_iff_isIso₁`,
  `Pretriangulated.Triangle.distinguished_iff_of_isZero₃`;
- best owner abstraction: the canonical owner is `Triangle` equipped with the distinguished-triangle
  predicate `distTriang`; the book statement here is a source-facing bridge built from the owner
  characterization of an isomorphism by the distinguished zero cone;
- primitive data: a single morphism `f : X ⟶ Y`;
- derived API: the zero-object criterion for an arbitrary distinguished triangle `Triangle.mk f g h`
  on `f`.

Source/core/bridge triage:
- `source-facing`: the textbook criterion phrased for a fixed morphism `f`;
- `core/canonical`: `Triangle.isZero₃_iff_isIso₁` and
  `Triangle.distinguished_iff_of_isZero₃`;
- `bridge/view`: specialize those canonical owners to triangles of the form `Triangle.mk f g h`.
-/

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

-- Proof sketch: `Triangle.isZero₃_iff_isIso₁` is the owner equivalence for any distinguished
-- triangle on `f`, and `Triangle.distinguished_iff_of_isZero₃` specializes it to the zero cone
-- `Triangle.mk f 0 0`.
/- Lemma 13.4.9, source-facing clause `(1) ↔ (3)`: a morphism `f : X ⟶ Y` is an isomorphism
if and only if every distinguished triangle `Triangle.mk f g h` on `f` has zero third object. -/
set_option linter.unusedVariables false in
theorem isIso_iff_isZero_obj₃_of_distinguished_triangle {X Y : D} (f : X ⟶ Y) :
    IsIso f ↔
      ∀ ⦃Z : D⦄ ⦃g : Y ⟶ Z⦄ ⦃h : Z ⟶ X⟦(1 : ℤ)⟧⦄
        (hT : Triangle.mk f g h ∈ distTriang D), IsZero Z := by
  constructor
  · intro hf Z g h hT
    simpa using (Triangle.isZero₃_of_isIso₁ (Triangle.mk f g h) hT hf)
  · intro hzero
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
    exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hzero hT)

/-- Lemma 13.4.9, source-facing clause `(1) ↔ (2)`: for a morphism `f : X ⟶ Y` in a
pretriangulated category, `f` is an isomorphism if and only if the zero cone
`Triangle.mk f 0 0` is distinguished. -/
@[stacks 05QR]
theorem isIso_iff_zero_cone_triangle_distinguished {X Y : D} (f : X ⟶ Y) :
    IsIso f ↔ Triangle.mk f (0 : Y ⟶ 0) 0 ∈ distTriang D := by
  simpa using
    (Triangle.distinguished_iff_of_isZero₃
      (Triangle.mk f (0 : Y ⟶ 0) 0) (isZero_zero D)).symm

end CategoryTheory
