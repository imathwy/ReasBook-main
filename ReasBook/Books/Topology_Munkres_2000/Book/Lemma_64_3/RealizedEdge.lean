module

public import Topology_Munkres_2000.Book.Example_50_6.Realization

public section

universe u v w

namespace SimpleGraph.LinearRealization

variable {V : Type u} {G : SimpleGraph V}

/-- A realized edge, viewed as a subset of an ambient space containing the graph. -/
def ambientEdge {Y : Type w} [TopologicalSpace Y] (R : G.LinearRealization)
    (X : Set Y) (e : R.Carrier ≃ₜ X) (edge : G.edgeSet) : Set Y :=
  Subtype.val '' (e '' R.finiteLinearGraph.edgeSet (R.edgeEquiv edge))

/-- Helper for Lemma 64.3: an ambient realized edge is the ambient image of
its intrinsic edge carrier. -/
theorem ambientEdge_eq_image_edgeSet {Y : Type w} [TopologicalSpace Y]
    (R : G.LinearRealization) (X : Set Y) (e : R.Carrier ≃ₜ X)
    (edge : G.edgeSet) :
    R.ambientEdge X e edge =
      Subtype.val '' (e '' R.finiteLinearGraph.edgeSet (R.edgeEquiv edge)) := by
  -- Expose the defining normal form once, in the construction's owner module.
  rfl

/-- A realized edge lies in the ambient copy of the graph carrier. -/
theorem ambientEdge_subset {Y : Type w} [TopologicalSpace Y] (R : G.LinearRealization)
    (X : Set Y) (e : R.Carrier ≃ₜ X) (edge : G.edgeSet) : R.ambientEdge X e edge ⊆ X := by
  rintro y ⟨x, _, rfl⟩
  exact x.property

end SimpleGraph.LinearRealization
