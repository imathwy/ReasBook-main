import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling:
- owner abstractions: `IsCompactOpenCovered`, `CompactOpens X`, `PrespectralSpace.isBasis_opens`
- same-domain declarations inspected: `IsCompactOpenCovered.of_isOpenMap`,
  `IsCompactOpenCovered.exists_mem_of_isBasis`,
  `PrespectralSpace.isBasis_opens`,
  `CompactOpens.map`

Layer triage:
- `source-facing`: a finite refinement theorem for an open cover of a compact open subset
- `core/canonical`: `IsCompactOpenCovered` together with the compact-open basis on prespectral
  spaces and open subspaces
- `bridge/view`: the finite operational surface lives on `Finset (CompactOpens X)`, while the
  compact-open pieces inside the covering opens are extracted from the owner abstraction

Primitive data are the compact open `U`, the indexed open family `V`, and the cover relation
`(U : Set X) ⊆ ⋃ i, V i`. The finite extraction and the compact-open pieces lying inside the cover
belong to the owner `IsCompactOpenCovered`; the resulting finite `Finset (CompactOpens X)` surface
is only a bridge/view assembled from those owner-level pieces. -/

-- Proof sketch: view the open cover as a family of open embeddings `V i ↪ X`, apply the owner
-- theorem `IsCompactOpenCovered.of_isOpenMap` to the compact open `U`, then use
-- `IsCompactOpenCovered.exists_mem_of_isBasis` on each open subspace `V i` to extract finitely
-- many compact opens there. Finally map those compact opens into `X`.
/-- Lemma 5.27.1: in a prespectral space, every open covering of a quasi-compact open subset
admits a finite refinement by quasi-compact opens. -/
theorem compactOpen_hasCofinalFiniteQuasiCompactRefiningCovers
    [PrespectralSpace X] (U : CompactOpens X)
    {ι : Type v} (V : ι → Opens X) (hV : (U : Set X) ⊆ ⋃ i, (V i : Set X)) :
    ∃ s : Finset (CompactOpens X),
      (U : Set X) = ⋃ W ∈ s, (W : Set X) ∧
        ∀ W ∈ s, ∃ i, (W : Set X) ⊆ V i := sorry
