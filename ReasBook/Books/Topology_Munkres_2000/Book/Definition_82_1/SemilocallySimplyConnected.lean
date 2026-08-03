module

public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions

public section

open Filter
open scoped Topology

universe u

namespace SemilocallySimplyConnectedSpace

/-- The point of a neighborhood subtype represented by its center. -/
def point {X : Type u} [TopologicalSpace X] {x : X} {U : Set X} (hU : U ∈ 𝓝 x) : U :=
  ⟨x, mem_of_mem_nhds hU⟩

end SemilocallySimplyConnectedSpace

/-- A space is semilocally simply connected when every point has a neighborhood whose
inclusion induces the trivial homomorphism on fundamental groups. -/
class SemilocallySimplyConnectedSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_nhds (x : X) : ∃ (U : Set X) (hU : U ∈ 𝓝 x),
    FundamentalGroup.mapOfSubtype U (SemilocallySimplyConnectedSpace.point hU) = 1

namespace SemilocallySimplyConnectedSpace

/-- Semilocal simple connectedness is equivalent to the pointwise neighborhood condition. -/
theorem iff_exists_nhds {X : Type u} [TopologicalSpace X] :
    SemilocallySimplyConnectedSpace X ↔ ∀ x : X, ∃ (U : Set X) (hU : U ∈ 𝓝 x),
      FundamentalGroup.mapOfSubtype U (point hU) = 1 := by
  constructor
  · exact fun h ↦ h.exists_nhds
  · exact fun h ↦ ⟨h⟩

end SemilocallySimplyConnectedSpace
