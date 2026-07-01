import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Topology

/- Domain-style sampling for the open mapping lemma in linearly topologized additive groups:
- primary domain: topological additive groups with linear/nonarchimedean topology and open-map
  phenomena
- sampled owner-level declarations:
  `IsLinearTopology.hasBasis_open_submodule`,
  `OpenAddSubgroup`,
  `dense_iInter_open_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup`,
  `AddSubgroup.exists_isOpen_of_iUnion_eq_univ_of_isClosed`
- best owner abstraction: `IsLinearTopology ℤ N` is the chapter/mathlib owner for a linearly
  topologized abelian group, `OpenAddSubgroup N` is the canonical owner for open subgroups, and
  `IsOpenMap` remains the owner for the open-map conclusion
- primitive data: the continuous additive homomorphism `u`, the source linear-topology and
  completeness hypotheses, and the separated target topological additive group
- derived API: the Baire-space consequences of completeness and countable generation of `𝓝 0`,
  already packaged in the preceding chapter lemmas, so they should not be restated as primitive
  public data here

Layer triage:
- `source-facing`: the Stacks either/or open-mapping statement below
- `core/canonical`: `IsLinearTopology ℤ N` for the linearly topologized source, and `IsOpenMap`
  for the openness alternative
- `bridge/view`: the chapter bridge from completeness plus countable generation to Baire-category
  consequences, used through Lemmas `15.36.3` and `15.36.4`
-/

section

variable {N : Type u} {M : Type v}
variable [TopologicalSpace N] [AddCommGroup N] [IsTopologicalAddGroup N] [IsLinearTopology ℤ N]
  [(𝓝 (0 : N)).IsCountablyGenerated]
  [@CompleteSpace N (IsTopologicalAddGroup.rightUniformSpace N)]
variable [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [T2Space M]

/-- Lemma 15.36.5 (Open mapping lemma): a continuous homomorphism from a complete linearly
topologized abelian group with a countable fundamental system of neighbourhoods of `0` to a
separated topological abelian group is either open, or the image of some open subgroup is nowhere
dense. -/
-- Proof sketch: choose a decreasing countable basis of open subgroups in `N`; if no image of such
-- a subgroup is nowhere dense, then the closures of these images form a neighborhood basis in `M`.
-- Use completeness of `N` to lift an arbitrary point of the first closure by an infinite sum, and
-- use separatedness of `M` to identify the limit with its image under `u`, proving openness.
theorem isOpenMap_or_exists_nowhereDense_image_openAddSubgroup
    (u : N →ₜ+ M) :
    IsOpenMap u ∨ ∃ N₀ : OpenAddSubgroup N, IsNowhereDense (u '' N₀) := sorry

end
