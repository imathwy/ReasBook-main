import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Group.Defs

-- Semantic recall: mathlib's canonical owner for the source notion of a topological group is the
-- typeclass `IsTopologicalGroup`, with `continuous_mul` and `continuous_inv` as its immediate
-- companion projections.

universe u

section

variable (G : Type u) [Group G] [TopologicalSpace G]

/- Source/core/bridge triage:
- `source-facing`: Definition 4-1 introduces a topological group by requiring continuity of the
  multiplication map `G × G → G` and the inversion map `G → G`;
- `core/canonical`: `IsTopologicalGroup G`;
- `bridge/view`: `continuous_mul` and `continuous_inv` are the direct companion projections
  exposing the source's two continuity conditions.

This item is therefore recall-only: the canonical owner and its source-facing companion API are
already present in mathlib, so a local wrapper would be redundant.
-/

/- Definition 4-1 — Topological Group

The source notion of a topological group is formalized in mathlib by `IsTopologicalGroup G` on a
type `G` equipped with `[Group G] [TopologicalSpace G]`. This typeclass asserts continuity of the
multiplication map `G × G → G`, `(s, t) ↦ s * t`, and the inversion map `G → G`, `s ↦ s⁻¹`.
-/
recall IsTopologicalGroup

variable [IsTopologicalGroup G]

/- The multiplication map of a topological group is continuous. -/
recall continuous_mul

/- The inversion map of a topological group is continuous. -/
recall continuous_inv

end
