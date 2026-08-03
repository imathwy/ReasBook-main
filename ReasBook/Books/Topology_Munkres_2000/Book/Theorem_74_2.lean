module

public import Topology_Munkres_2000.Book.Theorem_74_2.Presentation
public import Topology_Munkres_2000.Book.Remark_74_2.Vertices
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

public section

namespace CyclicPolygon.EdgePasting

universe v

variable {n : ℕ} {poly : CyclicPolygon n} {S : Type v}

/-- Theorem 74.2. If all vertices of a labelled cyclic polygon have the same image in
its edge-pasting realization, its fundamental group is the one-relator group whose
generators are the labels that occur and whose relator is the signed boundary word. -/
theorem fundamentalGroupMulEquiv (pasting : poly.EdgePasting S)
    (x₀ : pasting.Realization)
    (hvertices : ∀ i : Fin n, pasting.quotientMap (poly.vertexPoint i) = x₀) :
    Nonempty
      (FundamentalGroup pasting.Realization x₀ ≃*
        PresentedGroup ({pasting.relator} : Set (FreeGroup pasting.UsedLabel))) := sorry

end CyclicPolygon.EdgePasting
