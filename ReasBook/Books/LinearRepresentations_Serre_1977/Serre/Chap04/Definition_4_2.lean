import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Group.Compact

-- Semantic recall verified: mathlib's canonical owner for compactness of the underlying space is
-- `CompactSpace`, and the set-theoretic bridge used for the source formulation is
-- `isCompact_univ_iff`.

universe u

section

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- Source/core/bridge triage:
- `source-facing`: Definition 4-2 says that a topological group `G` is compact.
- `core/canonical`: mathlib expresses this compactness by the typeclass `CompactSpace G`.
- `bridge/view`: `isCompact_univ_iff` converts between the canonical typeclass and compactness of
  the underlying set `Set.univ`, while `isCompact_iff_finite_subcover` is the open-cover
  formulation used in the source text.

This item is therefore recall-only: introducing a local alias for compact topological groups would
duplicate mathlib's canonical owner without improving the Chapter 4 API.
-/

/- Definition 4-2: a topological group `G` is compact exactly when its underlying space carries
the canonical compactness class `CompactSpace G`. -/
recall CompactSpace

/- Specializing `isCompact_iff_finite_subcover` to `Set.univ : Set G` yields the source's
equivalent formulation that every open cover of `G` admits a finite subcover; the bridge from the
canonical class to compactness of the underlying set is `isCompact_univ_iff`. -/
recall isCompact_univ_iff : IsCompact (Set.univ : Set G) ↔ CompactSpace G
recall isCompact_iff_finite_subcover

end
