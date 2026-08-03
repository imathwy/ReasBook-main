module

public import Topology_Munkres_2000.Book.Theorem_75_5.Classification
public import Topology_Munkres_2000.Book.Definition_74_6.Presentation
public import Topology_Munkres_2000.Book.Remark_74_2.Vertices
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup

public section

open CategoryTheory

namespace AcadbcbInvBd

noncomputable section

/-- The edge labels and orientations encoding `a c a d b c b⁻¹ d`. -/
def pasting (poly : CyclicPolygon 8) : poly.EdgePasting (Fin 4) :=
  .ofSigns poly ![0, 2, 0, 3, 1, 2, 1, 3] ![true, true, true, true, true, true, false, true]

/-- The quotient space obtained from the octagonal word `a c a d b c b⁻¹ d`. -/
abbrev Realization (poly : CyclicPolygon 8) := (pasting poly).Realization

/-- The concrete edge-label map is the vector encoding `a c a d b c b d`. -/
theorem pastingLabel (poly : CyclicPolygon 8) :
    (pasting poly).label = ![0, 2, 0, 3, 1, 2, 1, 3] := sorry

/-- The second `b`-edge is reversed and all other edges retain the cyclic orientation. -/
theorem pastingOrientation (poly : CyclicPolygon 8) :
    (pasting poly).sign = ![true, true, true, true, true, true, false, true] := sorry

/-- Exercise 75.3 (1). All vertices of the octagonal region have the same image under
the pasting map for the word `a c a d b c b⁻¹ d`. -/
theorem verticesIdentified (poly : CyclicPolygon 8) :
    (pasting poly).VerticesIdentified := sorry

/-- Exercise 75.3 (2). The first integral singular homology group of the octagonal
quotient is isomorphic to `ℤ³ ⊕ ZMod 2`. -/
theorem firstHomology (poly : CyclicPolygon 8) :
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
          (AddCommGrpCat.of ℤ)).obj (TopCat.of (Realization poly)) ≅
        AddCommGrpCat.of (FreeAbelianGroup (Fin 3) × ZMod 2)) := sorry

/-- Exercise 75.3 (3). The octagonal quotient is homeomorphic to the four-fold
projective plane, assuming it belongs to the classified list of compact surfaces. -/
theorem homeomorphicFourFoldProjectivePlane (poly : CyclicPolygon 8)
    (h_classified : ClassifiedClosedSurface (Realization poly)) :
    Nonempty
      (Realization poly ≃ₜ
        NonorientableSurfacePresentation.mFoldProjectivePlane 4
          (Nat.one_lt_succ_succ 2)) := sorry


end

end AcadbcbInvBd

end
