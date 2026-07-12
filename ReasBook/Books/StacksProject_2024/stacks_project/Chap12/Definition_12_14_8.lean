import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
variable (A : CochainComplex C ℤ) (i k : ℤ)

/- Domain-style sampling:
- primary domain: cohomology of shifted cochain complexes in a category with homology;
- sampled owner declarations:
  `CochainComplex.ShiftSequence.shiftIso`,
  `(homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso`,
  `CategoryTheory.Functor.ShiftSequence.shiftIso`;
- best owner abstraction for this file: the cochain-complex owner
  `CochainComplex.ShiftSequence.shiftIso`, whose underlying generic interface is
  `CategoryTheory.Functor.ShiftSequence.shiftIso`.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.ShiftSequence.shiftIso`;
- `core/canonical`: `CategoryTheory.Functor.ShiftSequence.shiftIso`;
- `bridge/view`: the inherited shift-sequence morphism
  `(homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso`.

Primitive data in this domain are the cochain-complex shift/cohomology comparison encoded by
`CochainComplex.ShiftSequence.shiftIso`; the generic functor-level shift-sequence interface and
the specialized morphism `(homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso` are derived API.

Definition 12.14.8 is a source-facing recall item: for a cochain complex `A` and any shift
`k : ℤ`, the canonical cohomology-shift identification is exactly
`CochainComplex.ShiftSequence.shiftIso`, and its inverse identifies `H^(i + k)(A)` with
`H^i(A⟦k⟧)`. -/
recall CochainComplex.ShiftSequence.shiftIso

/-- Definition 12.14.8: the canonical identification
`H^(i + k)(A) ≅ H^i(A⟦k⟧)` coming from the shift isomorphism. -/
noncomputable def cohomologyShiftIso :
    A.homology (i + k) ≅ (A⟦k⟧).homology i :=
  -- Specialize the recalled cohomology shift comparison exactly at `i + k`;
  -- the textbook arrow is the inverse component at `A`.
  ((CochainComplex.ShiftSequence.shiftIso C k i (i + k) (add_comm k i)).app A).symm

/-- Helper for Definition 12.14.8: the canonical cohomology-shift identification is
definitionally the inverse of the recalled shift-isomorphism component at `A`. -/
lemma cohomology_shift_iso_eq_shift_iso_symm :
    cohomologyShiftIso C A i k =
      ((CochainComplex.ShiftSequence.shiftIso C k i (i + k) (add_comm k i)).app A).symm := by
  -- The definition is chosen so this source-facing comparison is judgmentally equal
  -- to the recalled owner specialization.
  rfl

end CategoryTheory
