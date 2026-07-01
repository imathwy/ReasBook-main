import stacks_project.Chap05.Lemma_5_16_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/-
Domain-style sampling for constructible neighborhoods detected by irreducible closed traces:
- primary domain: constructible subsets in Noetherian spaces, local neighborhoods, and dense traces
  on irreducible closed subspaces;
- sampled owner declarations:
  `Topology.IsConstructible`,
  `Topology.IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`,
  `TopologicalSpace.IrreducibleCloseds`,
  the canonical trace notation `↓∩`;
- best owner abstraction: `Topology.IsConstructible`;
- primitive vs. derived split: the primitive datum is the owner predicate `IsConstructible E`; the
  dense-trace criterion is derived local API on the canonical bridge object
  `Y : IrreducibleCloseds X`, so the numbered item should live as an owner theorem rather than as a
  parallel global wrapper.

Layer triage:
- `source-facing`: the Stacks criterion for when a constructible subset is a neighborhood of a
  point;
- `core/canonical`: the owner predicate `Topology.IsConstructible`;
- `bridge/view`: dense traces on `IrreducibleCloseds X` via `(Y : Set X) ↓∩ E`.
-/

-- Proof sketch: if `E ∈ 𝓝 x`, then its trace on any irreducible closed subspace through `x`
-- contains a neighborhood of `x` in that subspace, hence is dense there. Conversely, among closed
-- subsets through `x` on which the trace is not a neighborhood, choose a minimal one using
-- Noetherianity; prove it is irreducible, use the dense-trace hypothesis and the previous lemma
-- that a dense constructible subset of an irreducible Noetherian space contains a nonempty open,
-- and derive a contradiction.
/-- Lemma 5.16.4: for a constructible subset `E` of a Noetherian topological space `X`, `E` is a
neighborhood of `x` if and only if for every irreducible closed subset `Y` of `X` containing `x`,
the trace of `E` on the subspace `Y` is dense in `Y`. -/
theorem IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace
    {E : Set X} (hE : IsConstructible E) {x : X} :
    E ∈ 𝓝 x ↔
      ∀ Y : IrreducibleCloseds X, x ∈ Y →
        Dense ((Y : Set X) ↓∩ E) := by
  sorry

end

end Topology
