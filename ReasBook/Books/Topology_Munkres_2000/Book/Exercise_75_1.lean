module

public import Topology_Munkres_2000.Book.Example_74_8.BoundaryGluing
public import Topology_Munkres_2000.Book.Definition_60_3
public import Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Theorem_75_5.Classification
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Data.ZMod.Basic

public section

open CategoryTheory AlgebraicTopology

namespace ProjectivePlaneTorus

/-- Exercise 75.1 (1). For any explicit realization of `P² # T` obtained by deleting
open discs from `P²` and the torus and identifying their boundary circles, the first
integral homology group is `ℤ × ℤ × ZMod 2`. -/
theorem firstHomology
    (gluing : DiscBoundaryGluing RealProjectivePlane (UnitAddCircle × UnitAddCircle)) :
    Nonempty
      (((singularHomologyFunctor AddCommGrpCat 1).obj (AddCommGrpCat.of ℤ)).obj
          (TopCat.of gluing.GluedSurface) ≅
        AddCommGrpCat.of ((ℤ × ℤ) × ZMod 2)) := sorry

/-- Exercise 75.1 (2). Assuming an explicit disc-boundary realization of `P² # T`
belongs to the complete classified list of compact surfaces, it is homeomorphic to the
three-fold projective plane. -/
theorem homeomorphicThreeFoldProjectivePlane
    (gluing : DiscBoundaryGluing RealProjectivePlane (UnitAddCircle × UnitAddCircle))
    (h_classified : ClassifiedClosedSurface gluing.GluedSurface) :
    Nonempty
      (gluing.GluedSurface ≃ₜ NonorientableSurfacePresentation.mFoldProjectivePlane 3
        (Nat.one_lt_succ_succ 1)) := sorry

end ProjectivePlaneTorus

end
