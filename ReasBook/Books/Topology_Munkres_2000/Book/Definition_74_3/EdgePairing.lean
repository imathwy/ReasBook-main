module

public import Topology_Munkres_2000.Book.Definition_74_3.Pasting

public section

namespace CyclicPolygon.EdgePasting

universe v

variable {n : ℕ} {poly : CyclicPolygon n} {S : Type v}

/-- Every edge has a unique distinct edge bearing the same label. -/
def PairsEdges (pasting : poly.EdgePasting S) : Prop :=
  ∀ i, ∃! j, j ≠ i ∧ pasting.label j = pasting.label i

/-- Edge labels occur in pairs exactly when every edge has a unique distinct mate
with the same label. -/
theorem pairsEdges_iff (pasting : poly.EdgePasting S) :
    pasting.PairsEdges ↔ ∀ i, ∃! j, j ≠ i ∧ pasting.label j = pasting.label i :=
  Iff.rfl


end CyclicPolygon.EdgePasting
