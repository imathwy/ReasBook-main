import Mathlib
import StacksProject_2024.Chap15.Lemma_15_36_3_Baire_category_theorem

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u

/- Domain-style sampling for countable closed covers in complete topological additive groups:
- primary domain: Baire-category consequences for complete topological additive groups, together
  with the canonical openness criterion for additive subgroups
- sampled owner-level declarations:
  `baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup`,
  `nonempty_interior_of_iUnion_of_closed`,
  `AddSubgroup.isOpen_of_mem_nhds`,
  `BaireSpace`
- best owner abstraction: the chapter-level `BaireSpace` bridge from Lemma `15.36.3`, together
  with the canonical consequence `nonempty_interior_of_iUnion_of_closed`; subgroup openness is
  then derived from `AddSubgroup.isOpen_of_mem_nhds`
- primitive data: a countable family of closed additive subgroups covering the ambient group
- derived API: the complete pseudometrizable/Baire-space packaging obtained from completeness and
  countable generation of `𝓝 0`

Layer triage:
- `source-facing`: the Stacks lemma asserting that one closed subgroup in a countable cover is open
- `core/canonical`: `nonempty_interior_of_iUnion_of_closed` and
  `AddSubgroup.isOpen_of_mem_nhds`, organized by the ambient owner abstraction `BaireSpace`
- `bridge/view`: the right-uniform-space route from countably generated `𝓝 0` and completeness to
  the Baire-space owner abstraction
-/

/- Lemma 15.36.4: under the assumptions of the Baire category theorem for a linearly
topologized complete topological additive group with a countable fundamental system of
neighbourhoods of `0`, if `M` is the union of countably many closed subgroups, then one of those
subgroups is open. -/
-- Proof sketch: apply the Baire theorem from Lemma 15.36.3, equivalently mathlib's
-- `nonempty_interior_of_iUnion_of_closed`, to the closed sets `(N n : Set M)`. This gives some
-- `n` together with a point of `interior (N n)`. For a subgroup, membership in its interior at
-- any point already gives openness via `AddSubgroup.isOpen_of_mem_nhds`.
section

variable {ι : Type*} {M : Type u} [Countable ι]
variable [TopologicalSpace M] [AddGroup M] [IsTopologicalAddGroup M]
variable [(𝓝 (0 : M)).IsCountablyGenerated]
variable [@CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)]

namespace AddSubgroup

/-- Lemma 15.36.4: if a complete topological additive group with countably generated `𝓝 0` is the
union of countably many closed additive subgroups, then one of those subgroups is open. As in
Lemma `15.36.3`, the linear-topology hypothesis from the surrounding Stacks context is omitted
from the statement because the argument only uses the induced `BaireSpace` owner abstraction. -/
theorem exists_isOpen_of_iUnion_eq_univ_of_isClosed
    (N : ι → AddSubgroup M) (hN_closed : ∀ i, IsClosed (N i : Set M))
    (hcover : (⋃ i, (N i : Set M)) = Set.univ) :
    ∃ i, IsOpen (N i : Set M) := by
  rcases nonempty_interior_of_iUnion_of_closed hN_closed hcover with ⟨i, _, hx⟩
  exact ⟨i, (N i).isOpen_of_mem_nhds <| mem_interior_iff_mem_nhds.1 hx⟩

end AddSubgroup

end
