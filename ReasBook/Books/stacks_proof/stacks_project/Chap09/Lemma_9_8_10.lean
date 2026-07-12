import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/- Domain-style sampling for Lemma 9.8.10:
- primary domain: algebraic field extensions and the canonical bundled subobject hierarchy over a
  base field;
- sampled owner declarations:
  `Subalgebra.isField_of_algebraic`,
  `Subalgebra.toIntermediateField'`,
  `Subfield`,
  `Subfield.toIntermediateField`;
- best owner abstraction: `Subalgebra.isField_of_algebraic`;
- primitive data: a subring `R : Subring E` together with the condition that `R` contains the
  image of `F`, which is exactly the data needed to regard `R` as an `F`-subalgebra of `E`;
- derived API: the induced `Subalgebra F E`, the resulting field structure on `R`, and any
  bundled `Subfield` or `IntermediateField` obtained from that field structure.

Source/core/bridge triage:
- `source-facing`: a subring of an algebraic field extension containing the image of the base
  field is a field;
- `core/canonical`: `Subalgebra.isField_of_algebraic`;
- `bridge/view`: the conversion from a `Subring E` plus `hF` to a `Subalgebra F E`.

This file should therefore stay a minimal bridge theorem: the source statement is not literally
the owner theorem, but it should delegate directly to that owner instead of introducing any
parallel local wrapper API. -/

namespace Subring

/-- Lemma 9.8.10: in an algebraic extension `E/F`, any subring `R ⊆ E` containing the image of
`F` is a field. This is the minimal `Subring` bridge to the canonical owner theorem
`Subalgebra.isField_of_algebraic`. -/
@[stacks 0BID]
theorem isField_of_algebraic (R : Subring E) (hF : ∀ x : F, algebraMap F E x ∈ R) :
    IsField R := by
  -- View `R` as the corresponding `F`-subalgebra of `E` using the hypothesis that it contains
  -- the image of the base field.
  -- The canonical owner theorem proves that this bundled subalgebra is a field in an algebraic
  -- extension, and the carrier is definitionally the original subring.
  simpa using
    (Subalgebra.isField_of_algebraic (Subalgebra.mk R.toSubsemiring hF : Subalgebra F E))

end Subring

end
