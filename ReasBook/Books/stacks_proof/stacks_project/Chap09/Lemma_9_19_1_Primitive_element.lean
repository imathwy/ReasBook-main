import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped IntermediateField

universe u v

section

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/- Domain-style sampling for Lemma 9.19.1:
- primary domain: primitive elements of finite field extensions and finiteness of the lattice of
  intermediate fields;
- sampled owner declarations:
  `Field.exists_primitive_element_iff_finite_intermediateField`,
  `Field.finite_intermediateField_of_exists_primitive_element`,
  `Field.exists_primitive_element_of_finite_intermediateField`,
  `Field.exists_primitive_element`;
- best owner abstraction: the canonical primitive-element API in namespace `Field`, with the owner
  equivalence between primitive elements and finiteness of intermediate fields;
- primitive data: none locally beyond the ambient finite extension `E/F`;
- derived API: the finite-dimensional specialization of the owner equivalence and the separable
  corollary.

Source/core/bridge triage:
- `source-facing`: the Stacks finite-extension specialization and its finite separable corollary;
- `core/canonical`: the `Field` primitive-element theorems listed above;
- `bridge/view`: `finite_extension_exists_primitive_element_iff_finite_intermediateField`, which
  specializes the canonical owner equivalence from algebraic extensions to finite extensions.
-/

/-- Lemma 9.19.1 (Primitive element): for a finite extension `E/F`, there exists `α : E` with
`F⟮α⟯ = ⊤` if and only if there are only finitely many intermediate fields `K` with `F ≤ K ≤ E`. -/
-- Proof sketch: specialize the canonical `Field` owner theorems for algebraic extensions to the
-- finite-dimensional situation. The forward direction is
-- `Field.finite_intermediateField_of_exists_primitive_element`, and the reverse direction is
-- `Field.exists_primitive_element_of_finite_intermediateField` applied to `⊤`.
@[stacks 030N]
theorem finite_extension_exists_primitive_element_iff_finite_intermediateField :
    (∃ α : E, F⟮α⟯ = ⊤) ↔ Finite (IntermediateField F E) := by
  constructor
  · exact Field.finite_intermediateField_of_exists_primitive_element F E
  · intro h
    letI := h
    simpa using
      Field.exists_primitive_element_of_finite_intermediateField F E (⊤ : IntermediateField F E)

section

variable [Algebra.IsSeparable F E]

/-- A finite separable field extension has only finitely many intermediate fields. -/
-- Proof sketch: combine the canonical primitive element theorem
-- `Field.exists_primitive_element` with the canonical owner theorem
-- `Field.finite_intermediateField_of_exists_primitive_element`.
theorem finite_intermediateField_of_finite_separable_extension :
    Finite (IntermediateField F E) :=
  Field.finite_intermediateField_of_exists_primitive_element F E
    (Field.exists_primitive_element F E)

end

end
