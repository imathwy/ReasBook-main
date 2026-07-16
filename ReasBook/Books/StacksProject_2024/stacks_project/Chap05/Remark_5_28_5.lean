import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_28_2
import StacksProject_2024.stacks_project.Chap05.Definition_5_28_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

/- Domain-style sampling for indexed stratifications and their closed initial families:
- sampled project owner declarations:
  `IsStratification`,
  `IsStratification.toLocallyClosedPartition_isGood`,
  `IsStratification.toLocallyClosedPartition`,
  `LocallyClosedPartition.IsGood`,
  `LocallyClosedPartition.le_iff_forall_exists_mem_subset`
- sampled topology infrastructure used by the bridge constructions:
  `LocallyFinite`,
  `Set.Iic`,
  `Set.Iio`
- best owner abstractions:
  `IsStratification` is the chapter's indexed owner and `LocallyClosedPartition` is the partition
  owner; the closed initial-family language in this remark is a source-facing bridge relating
  those owners

Layer triage:
- `source-facing`: `IsClosedInitialFamily`
- `core/canonical`: `IsStratification` and `LocallyClosedPartition`
- `bridge/view`: the initial-union and frontier-difference constructions relating the three views

Primitive data for the source-facing side are only a family `Z : I → Set X` together with its
closedness, cover, local finiteness, and intersection formula. The subtype of nonempty frontier
pieces and the recovered locally closed partition are derived API from that data, so they should
be exposed only through canonical bridge declarations.
-/

variable {X : Type u} [TopologicalSpace X]
variable {I : Type v} [PartialOrder I]

/-- A closed initial family is a locally finite covering by closed subsets satisfying the
intersection formula `Z i ∩ Z j = ⋃_{k ≤ i, j} Z k`. -/
class IsClosedInitialFamily (Z : I → Set X) : Prop where
  /-- Each member of the family is closed. -/
  isClosed (i : I) : IsClosed (Z i)
  /-- The family covers the ambient space. -/
  iUnion_eq_univ : ⋃ i, Z i = univ
  /-- Every point has a neighbourhood meeting only finitely many members of the family. -/
  locallyFinite : LocallyFinite Z
  /-- The intersection of two members is the union of the members below both indices. -/
  inter_eq_iUnion (i j : I) :
    Z i ∩ Z j = ⋃ k ∈ Iic i ∩ Iic j, Z k

namespace IsStratification

/-- The initial union `⋃_{j ≤ i} strata j` attached to an indexed family of strata. -/
abbrev initial (strata : I → Set X) (i : I) : Set X :=
  ⋃ j ∈ Iic i, strata j

/-- Remark 5.28.5 (1): the initial unions attached to a locally finite indexed stratification
form a closed initial family. -/
-- Proof sketch: use local finiteness to show each initial union is closed as a locally finite
-- union of closures of strata, then combine the partition and closure condition to identify the
-- intersections with the lower-index union.

theorem initial_isClosedInitialFamily
    {strata : I → Set X} (hstrata : IsStratification strata) (hloc : LocallyFinite strata) :
    IsClosedInitialFamily (initial strata) := sorry

/-- Remark 5.28.5 (2): a locally finite indexed stratification yields a good locally closed
partition. -/
-- Proof sketch: use the frontier condition coming from the closure-order axiom of the indexed
-- stratification after passing to the canonical locally closed partition.
theorem toLocallyClosedPartition_isGood
    {strata : I → Set X} (hstrata : IsStratification strata) (hloc : LocallyFinite strata) :
    LocallyClosedPartition.IsGood hstrata.toLocallyClosedPartition := sorry

end IsStratification

namespace IsClosedInitialFamily

/-- The difference `Z i \ ⋃_{j < i} Z j` attached to a family of closed initial subsets. -/
abbrev frontier (Z : I → Set X) (i : I) : Set X :=
  Z i \ ⋃ j ∈ Iio i, Z j

/-- The indices with nonempty frontier differences. -/
abbrev frontierIndex (Z : I → Set X) : Type v :=
  { i : I // (frontier Z i).Nonempty }

/-- The indexed family of nonempty frontier differences. -/
abbrev frontierStrata (Z : I → Set X) : frontierIndex Z → Set X :=
  fun i ↦ frontier Z i.1

/-- Remark 5.28.5 (3): the nonempty frontier differences attached to a closed initial family form
an indexed stratification. -/
-- Proof sketch: show the nonempty differences partition `X`, inherit local closedness from the
-- closed members `Z i`, and recover the closure condition from the hypotheses on the closed
-- initial family.

theorem frontier_isStratification
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) :
    IsStratification (frontierStrata Z) := sorry

/-- The frontier differences attached to a closed initial family form a locally finite family. -/
-- Proof sketch: apply local finiteness of the closed initial family and pass to the frontier
-- differences by the inclusion `frontier Z i ⊆ Z i`.
theorem locallyFinite_frontier
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) :
    LocallyFinite (frontier Z) := sorry

end IsClosedInitialFamily
