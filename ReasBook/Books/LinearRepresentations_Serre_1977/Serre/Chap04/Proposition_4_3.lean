import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

-- Semantic recall verified: `ClosedSubgroup.instCompactSpaceSubtypeMem` is the canonical
-- compactness API for closed subgroups of compact topological groups.

universe u

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]

/- Source/core/bridge triage:
- `source-facing`: Proposition 4-3 says that a closed subgroup of a compact topological group is
  compact for the induced topology.
- `core/canonical`: mathlib records exactly this compactness statement by the instance
  `ClosedSubgroup.instCompactSpaceSubtypeMem`.
- `bridge/view`: `isCompact_univ_iff` recovers the source's set-theoretic compactness statement
  from the canonical `CompactSpace` owner when needed downstream.

This item is therefore recall-only: introducing a second local instance name would duplicate the
canonical owner without improving the reusable API surface.
-/

/- Proposition 4-3: if `H ≤ G` is a closed subgroup of a compact topological group `G`, then `H`
with the induced topology is compact. In mathlib this is the canonical instance
`ClosedSubgroup.instCompactSpaceSubtypeMem`. -/
recall ClosedSubgroup.instCompactSpaceSubtypeMem

end
