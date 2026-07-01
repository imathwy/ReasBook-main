import stacks_project.Chap05.FiniteUnionOfLocallyClosed

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

/-
Domain-style sampling for dense traces on irreducible subspaces:
- primary domain: irreducible subsets, generic points, dense traces, and finite unions of locally
  closed subsets;
- sampled canonical declarations:
  `IsGenericPoint.mem_open_set_iff`,
  `IsGenericPoint.mem_closed_set_iff`,
  `IsFiniteUnionOfLocallyClosed.exists_eq_iUnion`,
  `Set.preimage_val_eq_univ_of_subset`,
  `IsLocallyClosed.isOpen_preimage_val_closure`;
- best owner abstractions: `IsGenericPoint` owns the pointwise generic-point criterion, while
  `IsIrreducible` is the natural owner for the irreducible-subspace dense/open-dense dichotomy;
- primitive-vs-derived split: the primitive inputs are the irreducible set or generic point,
  together with the finite locally closed decomposition of `E`; the open dense trace is derived
  data and should be exposed via `Opens Z`, with the trace written through the canonical subtype
  notation `Z ↓∩ E` rather than raw subtype preimages.

Layer triage:
- `source-facing`: the irreducible-subspace dense/open-dense criterion;
- `core/canonical`: `IsIrreducible`, `IsGenericPoint`, and `Opens`;
- `bridge/view`: the canonical subtype trace `Z ↓∩ E` together with the finite locally closed
  decomposition supplied by `IsFiniteUnionOfLocallyClosed.exists_eq_iUnion`.
-/

-- Proof sketch: write `E ∩ Z` as a finite union of locally closed subsets of the irreducible
-- subspace `Z`; one dense locally closed piece is then open in its closure, hence yields an open
-- dense subset of `Z`.
/-- Lemma 5.15.15: if `Z` is irreducible and `E` is a finite union of locally closed subsets of
`X`, then `E ∩ Z` contains an open dense subset of `Z` if and only if `E ∩ Z` is dense in `Z`. -/
theorem IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} (hZ : IsIrreducible Z) (hE : IsFiniteUnionOfLocallyClosed E) :
    (∃ U : Opens Z, Dense (U : Set Z) ∧ (U : Set Z) ⊆ Z ↓∩ E) ↔ Dense (Z ↓∩ E) := sorry

-- Proof sketch: if `ξ` is a generic point of `Z`, then membership `ξ ∈ E` is equivalent to the
-- trace `E ∩ Z` being dense in `Z`; combine the generic-point characterization of dense subsets of
-- an irreducible space with the locally closed decomposition of `E`.
/-- For a generic point `ξ` of `Z`, a finite union of locally closed subsets has dense trace on
`Z` exactly when `ξ` belongs to it. -/
theorem IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed
    {Z E : Set X} {ξ : X} (hξ : IsGenericPoint ξ Z) (hE : IsFiniteUnionOfLocallyClosed E) :
    Dense (Z ↓∩ E) ↔ ξ ∈ E := by
  let ξZ : Z := ⟨ξ, hξ.mem⟩
  have hξZ : IsGenericPoint ξZ (Set.univ : Set Z) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simpa [subtype_specializes_iff] using
      (hξ.specializes_iff_mem : ξ ⤳ (y : X) ↔ (y : X) ∈ Z)
  constructor
  · intro hDense
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      (hξ.isIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed hE).2
        hDense
    haveI : Nonempty Z := ⟨ξZ⟩
    have hU_nonempty : (U : Set Z).Nonempty := hU_dense.nonempty
    have hξU : ξZ ∈ U := by
      exact (hξZ.mem_open_set_iff U.2).2 (by simpa using hU_nonempty)
    exact hU_subset hξU
  · intro hξE
    rw [Subtype.dense_iff]
    have hξ_closure : ξ ∈ closure (Z ∩ E) := subset_closure ⟨hξ.mem, hξE⟩
    simpa [Subtype.image_preimage_val] using
      (hξ.mem_closed_set_iff isClosed_closure).1 hξ_closure
