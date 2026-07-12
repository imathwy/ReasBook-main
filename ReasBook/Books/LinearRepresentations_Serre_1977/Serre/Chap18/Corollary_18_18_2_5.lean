import Mathlib
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u w

namespace Representation

section

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type w}

/- Domain-style sampling for this corollary:
* source-facing: the count of irreducibles in a complete simple family;
* core/canonical owner in this domain:
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions`;
* relevant upstream owner data reused here:
  `PRegularConjClass G p`,
  `IsCompleteIrreducibleFamily`,
  `IsCompleteIrreducibleFamily.finite_index`.

Primitive data vs. derived API:
* primitive data: the family `E` with pairwise nonisomorphism and completeness;
* derived API: the induced basis of `PRegularConjClass G p → k`, whose cardinal comparison gives
  the count.

Layer triage:
* source-facing: this cardinality statement;
* core/canonical: the field-valued basis owner from Theorem `18-18.2-1`;
* bridge/view used internally: the canonical subgroup inclusion `(primeToPRoots p k).subtype`.
-/

-- Proof sketch: the canonical owner theorem
-- `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions`
-- supplies a `k`-basis of the full function space on `PRegularConjClass G p` indexed by the
-- complete simple family `E`. Comparing the cardinality of that basis with the standard basis of
-- the function space yields the count.
/-- Corollary 18-18.2-5: for a complete family of pairwise nonisomorphic simple finite-dimensional
`k[G]`-representations, the number of indices is the number of `p`-regular conjugacy classes of
`G`. -/
theorem card_eq_card_pRegularConjugacyClasses_of_complete_simple_family
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Nat.card ι = Nat.card (PRegularConjClass G p) := by
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  let b :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (primeToPRoots p k).subtype (Subgroup.subtype_injective (primeToPRoots p k))
      E hE_pairwise hE_complete
  -- Route correction: in characteristic `p` the index type is finite because the Brauer
  -- characters form a basis of the finite-dimensional regular class-function space (the
  -- semisimple `finite_index` owner needs `NeZero (|G| : k)`, unavailable here).
  letI : Module.Finite k (PRegularConjClass G p → k) :=
    Module.Finite.of_basis (Pi.basisFun k (PRegularConjClass G p))
  letI : Finite ι := Module.Finite.finite_basis b
  letI : Fintype ι := Fintype.ofFinite ι
  calc
    Nat.card ι = Fintype.card ι := Nat.card_eq_fintype_card
    _ = Module.finrank k (PRegularConjClass G p → k) := by
      simpa using (Module.finrank_eq_card_basis b).symm
    _ = Fintype.card (PRegularConjClass G p) := Module.finrank_fintype_fun_eq_card k
    _ = Nat.card (PRegularConjClass G p) := Nat.card_eq_fintype_card.symm

end

end Representation
