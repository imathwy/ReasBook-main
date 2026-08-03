module

public import Topology_Munkres_2000.Book.Definition_64_2.ThetaSpace

public section

open Set

universe u

namespace Topology.ThetaPresentation

variable {Y : Type u} [TopologicalSpace Y] {X : Set Y}

/-- The `i`th edge of a theta presentation of a subspace, viewed in the ambient space. -/
def ambientEdge (P : ThetaPresentation X) (i : Fin 3) : Set Y :=
  Subtype.val '' P.edge i

/-- The ambient edge is the range of the intrinsic arc followed by subtype
inclusion. -/
theorem ambientEdge_eq_range (P : ThetaPresentation X) (i : Fin 3) :
    P.ambientEdge i = Set.range (fun t ↦ (P.arc i t : Y)) := by
  -- Expand the owner definitions and identify the two existential descriptions.
  unfold ambientEdge
  rw [P.edge_eq_range]
  ext y
  constructor
  · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨P.arc i t, ⟨t, rfl⟩, rfl⟩

/-- Distinct theta edges still meet only at their two common endpoints after
inclusion into the ambient space. -/
theorem ambientEdge_inter_ambientEdge
    (P : ThetaPresentation X) (i j : Fin 3) (hij : i ≠ j) :
    P.ambientEdge i ∩ P.ambientEdge j =
      {(P.initial : Y), (P.terminal : Y)} := by
  -- Injectivity of subtype inclusion transports the intrinsic intersection.
  unfold ambientEdge
  rw [← Set.image_inter Subtype.val_injective, P.edge_inter_edge i j hij,
    Set.image_pair]

/-- Every ambient edge of a theta presentation lies in the presented subspace. -/
theorem ambientEdge_subset (P : ThetaPresentation X) (i : Fin 3) : P.ambientEdge i ⊆ X := by
  rintro y ⟨x, _, rfl⟩
  exact x.property

/-- The ambient edges of a theta presentation cover the presented subspace. -/
theorem iUnion_ambientEdge (P : ThetaPresentation X) : ⋃ i, P.ambientEdge i = X := by
  ext y
  constructor
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact P.ambientEdge_subset i hi
  · intro hy
    have hx : (⟨y, hy⟩ : X) ∈ ⋃ i, P.edge i := by
      rw [P.iUnion_edge]
      exact Set.mem_univ _
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨⟨y, hy⟩, hi, rfl⟩⟩

end Topology.ThetaPresentation

end

