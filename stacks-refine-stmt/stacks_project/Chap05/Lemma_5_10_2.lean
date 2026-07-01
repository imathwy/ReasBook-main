import stacks_project.Chap05.Definition_5_10_1
import stacks_project.Chap05.Lemma_5_11_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace Order

/- 
Domain-style sampling for global versus local topological Krull dimension:
- primary domain: topological Krull dimension on a space and its localization at a point via open
  neighbourhoods;
- inspected owner declarations:
  `topologicalKrullDim`,
  `Order.krullDim_eq_iSup_coheight`,
  `Order.coheight_le_krullDim`,
  `codim_irreducibleClosed_restrictOpen_eq`;
- best owner abstraction: the global owner is `topologicalKrullDim X`, with the hard inequality
  proved by passing through the canonical `Order.coheight` of irreducible closed subsets and
  restricting those subsets to open neighbourhoods of a chosen point.

Layer triage:
- `source-facing`: `topologicalKrullDim_eq_iSup_topologicalKrullDimAt`;
- `core/canonical`: `topologicalKrullDim`, `Order.krullDim_eq_iSup_coheight`, and
  `Order.coheight_le_krullDim`;
- `bridge/view`: the local owner `topologicalKrullDimAt`, its infimum API from
  `Definition_5_10_1`, and the open-restriction bridge
  `codim_irreducibleClosed_restrictOpen_eq`.

Primitive data are only the ambient space and its open neighbourhoods. The local infimum
`topologicalKrullDimAt` and the codimension invariance under open restriction already provide the
derived API, so this file should reuse those owners rather than introducing any new chain-level
wrapper or chosen maximal-chain package.
-/

-- Proof sketch: the inequality `≤` comes from evaluating the neighbourhood infimum at `univ`;
-- for `≥`, choose a maximal chain of irreducible closed subsets witnessing the global dimension,
-- pick a point in its minimal member, and intersect the chain with an arbitrary neighbourhood of
-- that point to obtain the same chain length locally.
/-- Lemma 5.10.2: the Krull dimension of a topological space is the supremum of the local Krull
dimensions at its points. -/
theorem topologicalKrullDim_eq_iSup_topologicalKrullDimAt
    {X : Type u} [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt x := by
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun Y ↦ ?_
    obtain ⟨x, hx⟩ := Y.isIrreducible.nonempty
    refine le_iSup_of_le x ?_
    refine le_iInf fun U ↦ ?_
    have hYU : ((Y : Set X) ∩ (U : Set X)).Nonempty := ⟨x, hx, U.2⟩
    rw [codim_irreducibleClosed_restrictOpen_eq Y U.toOpens hYU]
    simpa [topologicalKrullDim] using Order.coheight_le_krullDim (Y.restrictOpen U.toOpens hYU)
  · refine iSup_le fun x ↦ ?_
    let U : OpenNhdsOf x := ⊤
    exact (topologicalKrullDimAt_le x U).trans <| by
      simpa [U] using topologicalKrullDim_subspace_le X (Set.univ : Set X)
