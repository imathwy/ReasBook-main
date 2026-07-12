import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C)

/- Domain-style sampling for Lemma 13.4.16:
- primary domain: triangulated object properties in a pretriangulated category and the associated
  Verdier morphism property `P.trW`;
- sampled owner declarations:
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsTriangulated.toContainsZero`,
  `ObjectProperty.IsTriangulated.toIsStableUnderShift`,
  `ObjectProperty.trW`;
- best owner abstraction: `ObjectProperty.IsTriangulated P`;
- primitive data: the owner fields `P.ContainsZero`, `P.IsStableUnderShift ℤ`, and
  `P.IsTriangulatedClosed₂`;
- derived API: the companion closure clauses `Closed₁` and `Closed₃`, and the cone morphism
  property `P.trW`;
- source/core/bridge triage:
  `source-facing`: the Stacks characterization of a triangulated object property by zero, shift,
    and cone closure for morphisms between objects of `P`;
  `core/canonical`: `ObjectProperty.IsTriangulated`;
  `bridge/view`: the ambient-category reformulation of the cone clause in terms of `P.trW`.

The two implication clauses that are already exact fields of `ObjectProperty.IsTriangulated`
should therefore be direct recalls, not new theorem wrappers, while the converse direction remains
as a bridge theorem. -/

namespace ObjectProperty

/- Lemma 13.4.16 (1): a triangulated object property contains the zero object. This is the
`toContainsZero` field of the canonical owner `ObjectProperty.IsTriangulated`. -/
recall IsTriangulated.toContainsZero

/- Lemma 13.4.16 (2): a triangulated object property is stable under the shift functor. This is
the `toIsStableUnderShift` field of `ObjectProperty.IsTriangulated`. -/
recall IsTriangulated.toIsStableUnderShift

/-- Lemma 13.4.16 (3): if `P` is triangulated, then every morphism between objects of `P` lies in
the Verdier morphism property `P.trW`. -/
@[stacks 05QX]
theorem trW_of_isTriangulated
    (hTriangulated : P.IsTriangulated)
    {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P.trW f := by
  letI := hTriangulated
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  simpa [P.trW_isoClosure] using
    trW.mk P.isoClosure hT (P.ext_of_isTriangulatedClosed₃' _ hT hX hY)

/-- Lemma 13.4.16 (4): if `P` contains zero, is stable under shifts, and every morphism between
objects of `P` lies in `P.trW`, then `P` is triangulated. -/
@[stacks 05QX]
theorem isTriangulated_of_containsZero_of_isStableUnderShift_of_trW
    (hZero : P.ContainsZero) (hShift : P.IsStableUnderShift ℤ)
    (hW : ∀ {X Y : C} (f : X ⟶ Y) (_ : P X) (_ : P Y), P.trW f) :
    P.IsTriangulated where
  toContainsZero := hZero
  toIsStableUnderShift := hShift
  toIsTriangulatedClosed₂ := by
    letI := hShift
    refine ⟨fun T hT h₁ h₃ ↦ ?_⟩
    have hmem : P.isoClosure.trW T.mor₃ := by
      simpa [P.trW_isoClosure] using hW T.mor₃ h₃ (P.le_shift 1 _ h₁)
    simpa using
      ((P.isoClosure).trW_iff_of_distinguished' T.rotate (rot_of_distTriang _ hT)).1 hmem

end ObjectProperty

end

end CategoryTheory
