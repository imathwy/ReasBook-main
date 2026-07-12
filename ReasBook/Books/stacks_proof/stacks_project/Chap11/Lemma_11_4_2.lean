import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A]

/- Domain-style sampling for Lemma 11.4.2:
- primary domain: centers of simple finite-dimensional algebras;
- sampled owner declarations:
  `FiniteDimensional`,
  `FiniteDimensional.finiteDimensional_subalgebra`,
  `Subalgebra.center`,
  `IsSimpleRing.isField_center`;
- best owner abstraction: this item is `source-facing`, with the finiteness input carried by the
  chapter owner `FiniteDimensional k A`; the center itself is the canonical owner object
  `Subalgebra.center k A`;
- primitive data: the ambient `k`-algebra structure on `A`, together with `[FiniteDimensional k A]`
  and `[IsSimpleRing A]`;
- derived API: finite-dimensionality of the center as a subalgebra, and the field structure read
  from the simple-ring center theorem through `Subalgebra.center_toSubring`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that the center of a finite simple `k`-algebra is a
  finite field extension of `k`;
- `core/canonical`: `Subalgebra.center k A`, `FiniteDimensional`, and
  `IsSimpleRing.isField_center`;
- `bridge/view`: `Subalgebra.center_toSubring`, identifying the algebra center with the ring
  center used by the owner theorem. -/

/- Owner recall for the field part of Lemma 11.4.2: the center of a simple ring is a field via
`IsSimpleRing.isField_center`; for a `k`-algebra this is read through
`Subalgebra.center_toSubring`. -/
recall IsSimpleRing.isField_center

/- The finite-dimensional part is derived, not additional center-specific structure: a subalgebra
of a finite-dimensional algebra over a field is finite-dimensional. -/
#check FiniteDimensional.finiteDimensional_subalgebra

/-- Lemma 11.4.2: if `A` is a finite simple `k`-algebra, then its center
`Subalgebra.center k A` is a finite field extension of `k`. -/
@[stacks 074A]
theorem center_finiteFieldExtension [FiniteDimensional k A] [IsSimpleRing A] :
    FiniteDimensional k (Subalgebra.center k A) ∧ IsField (Subalgebra.center k A) := by
  refine ⟨inferInstance, ?_⟩
  simpa [Subalgebra.center_toSubring] using IsSimpleRing.isField_center A

end
