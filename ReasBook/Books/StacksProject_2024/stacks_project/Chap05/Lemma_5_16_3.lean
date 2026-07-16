import StacksProject_2024.stacks_project.Chap05.Lemma_5_15_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X]

-- Proof sketch: first use `IsConstructible.isFiniteUnionOfLocallyClosed` on `E`, then apply the
-- earlier irreducible-space theorem that a finite union of locally closed subsets has dense trace
-- on `Z` exactly when it contains an open dense subset of `Z`.
/-- A constructible subset has, on each irreducible closed trace, either a nonempty open subtrace
or a non-dense trace. -/
theorem IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense {E : Set X}
    (hE : IsConstructible E) (Z : IrreducibleCloseds X) :
    (∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E) ∨
      ¬ Dense ((Z : Set X) ↓∩ E) := by
  have hE_lc : IsFiniteUnionOfLocallyClosed E := hE.isFiniteUnionOfLocallyClosed
  letI : Nonempty Z := by
    rcases Z.isIrreducible.nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  by_cases hDense : Dense (((Z : Set X) ↓∩ E) : Set Z)
  · left
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      (Z.isIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
        hE_lc).2 hDense
    exact ⟨U, hU_dense.nonempty, hU_subset⟩
  · exact Or.inr hDense

end

end Topology

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/-
Domain-style sampling for constructible subsets detected on irreducible closed traces:
- primary domain: constructible subsets in Noetherian spaces, tested by their traces on
  irreducible closed subspaces;
- inspected declarations:
  `Topology.IsConstructible`,
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed`,
  `Topology.IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`,
  the canonical subtype-trace notation `↓∩`;
- best owner abstraction: `Topology.IsConstructible`.

Layer triage:
- `source-facing`: the Stacks Project criterion for constructibility via traces on irreducible
  closed subsets;
- `core/canonical`: the owner predicate `Topology.IsConstructible`;
- `bridge/view`: the bundled irreducible closed subspace `Z : IrreducibleCloseds X` together with
  the canonical subtype trace `(Z : Set X) ↓∩ E`.

Primitive data is the ambient Noetherian topology together with the owner predicate
`IsConstructible E`. The finite-union-of-locally-closed decomposition of a trace and the
nonempty-open trace alternative are both derived API, supplied respectively by
`IsConstructible.isFiniteUnionOfLocallyClosed` and the owner-facing theorem
`IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`. The bundled irreducible closed
subspaces and the subtype-trace notation are the canonical bridge/view API, so the numbered item
should reuse that owner-facing theorem rather than carrying a parallel forward-direction argument.
-/

-- Proof sketch: the forward implication is the owner-facing theorem
-- `IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`. For the converse, argue by
-- Noetherian induction on closed subsets whose trace is not constructible, reduce to the
-- irreducible case, and use the stated dichotomy to contradict minimality.
/-- Lemma 5.16.3: in a Noetherian topological space, a subset `E` is constructible if and only if
for every irreducible closed subset `Z`, the trace of `E` on `Z` either contains a nonempty open
subset of `Z` or is not dense in `Z`. -/
theorem isConstructible_iff_forall_irreducibleCloseds_containsNonemptyOpen_or_not_dense
    (E : Set X) :
    IsConstructible E ↔
      ∀ Z : IrreducibleCloseds X,
        (∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E) ∨
          ¬ Dense ((Z : Set X) ↓∩ E) := by
  constructor
  · intro hE Z
    exact hE.exists_nonemptyOpen_subset_trace_or_not_dense Z
  · sorry

end
