import Mathlib
import StacksProject_2024.stacks_project.Chap05.Lemma_5_12_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [PrespectralSpace X]
  [QuasiSeparatedSpace X] {T : Set X}

/- Domain-style sampling for intersections of clopen supersets and connected-component saturation:
- primary domain: connected components and clopen separation in compact prespectral
  quasi-separated spaces
- same-domain owner declarations inspected:
  `PrespectralSpace.connectedComponent_eq_iInter_isClopen`,
  `IsClopen.connectedComponent_subset`,
  `connectedComponent_subset_iInter_isClopen`,
  `IsClopen.biUnion_connectedComponent_eq`
- best owner abstraction: `connectedComponent x`, with the ambient hypotheses carried by
  `PrespectralSpace` and `QuasiSeparatedSpace`

Layer triage:
- `source-facing`: the subset-level criterion that a set is an intersection of clopen subsets
  exactly when it is closed and a union of connected components
- `core/canonical`: the pointwise owner `connectedComponent x` together with clopen neighborhood
  API
- `bridge/view`: the subset-level `sInter` proof step for the family of all clopen supersets of
  `T`, derived from the pointwise owner

Primitive data are the subset `T`, its closedness, and the component-saturation property
`∀ x ∈ T, connectedComponent x ⊆ T`. The clopen-superset intersection is derived from those data,
so the file should remain a bridge theorem over the connected-component owner rather than
introducing a parallel wrapper notion.
-/

-- Proof sketch: write `T` as an `sInter` of clopen subsets, and use that arbitrary intersections
-- of closed sets are closed.
/-- Lemma 5.12.12 (1): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is an intersection of open and closed subsets, then it is closed.
-/
theorem isClosed_of_isIntersectionOfClopens
    (hT : ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S) :
    IsClosed T := sorry

-- Proof sketch: every clopen set containing `x` contains the full connected component of `x`; an
-- intersection of such clopen sets is therefore saturated under connected components.
/-- Lemma 5.12.12 (2): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is an intersection of open and closed subsets, then it is a union
of connected components of `X`. -/
theorem connectedComponent_subset_of_isIntersectionOfClopens
    (hT : ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S)
    (x : X) (hx : x ∈ T) :
    connectedComponent x ⊆ T := sorry

-- Proof sketch: intersect all clopen supersets of `T`; closedness gives compactness of `T`, and
-- component saturation lets one separate any point outside `T` from `T` by a clopen superset.
/-- Lemma 5.12.12 (3): if a subset of a quasi-compact space with a basis of quasi-compact opens
and quasi-compact intersections is closed and is a union of connected components of `X`, then it
is an intersection of open and closed subsets. -/
theorem isIntersectionOfClopens_of_isClosed_of_union_connectedComponents
    (hT_closed : IsClosed T) (hT_components : ∀ x ∈ T, connectedComponent x ⊆ T) :
    ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S := sorry

end
