module

public import Topology_Munkres_2000.Book.Theorem_74_1.PolygonalPasting

public section

universe u v

namespace PolygonalPasting

variable {ι : Type u} [Fintype ι] {S : Type v}

/-- Every edge in a finite polygonal presentation has a unique distinct edge with the
same label. -/
def PairsEdges (presentation : PolygonalPasting ι S) : Prop :=
  ∀ i edge,
    ∃! mate : (j : ι) × Fin (presentation.sides j),
      mate ≠ ⟨i, edge⟩ ∧
        (presentation.pasting mate.1).label mate.2 = (presentation.pasting i).label edge

/-- Edge pairing means that each edge has a unique distinct mate with the same label. -/
theorem pairsEdges_iff (presentation : PolygonalPasting ι S) :
    presentation.PairsEdges ↔
      ∀ i edge,
        ∃! mate : (j : ι) × Fin (presentation.sides j),
          mate ≠ ⟨i, edge⟩ ∧
            (presentation.pasting mate.1).label mate.2 = (presentation.pasting i).label edge :=
  Iff.rfl


end PolygonalPasting
