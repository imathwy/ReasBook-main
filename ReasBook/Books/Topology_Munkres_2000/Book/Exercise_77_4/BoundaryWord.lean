module

public import Topology_Munkres_2000.Book.Definition_77_2.OrientationType
public import Topology_Munkres_2000.Book.Theorem_74_2.Presentation
public import Topology_Munkres_2000.Book.Definition_74_3.EdgePairing

public section

universe u

namespace CyclicPolygon.EdgePasting

variable {n : ℕ} {poly : CyclicPolygon n} {S : Type u}

/-- The polygon word canonically determined by the signed boundary of an edge pasting. -/
def toPolygonWord (pasting : poly.EdgePasting S) : PolygonWord pasting.UsedLabel :=
  ⟨pasting.boundaryWord, pasting.boundaryWord_length.symm ▸ poly.three_le⟩

/-- The underlying signed-label list of `pasting.toPolygonWord` is its boundary word. -/
theorem toPolygonWord_val (pasting : poly.EdgePasting S) :
    pasting.toPolygonWord.val = pasting.boundaryWord := sorry

/-- Properness of the boundary polygon word implies that the edge pasting pairs its edges. -/
theorem pairsEdges_of_toPolygonWord_proper (pasting : poly.EdgePasting S)
    (hproper : ({pasting.toPolygonWord} : LabellingScheme pasting.UsedLabel).Proper) :
    pasting.PairsEdges := sorry


end CyclicPolygon.EdgePasting
