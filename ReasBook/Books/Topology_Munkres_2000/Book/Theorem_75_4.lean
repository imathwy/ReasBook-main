module

public import Topology_Munkres_2000.Book.Definition_74_6.Presentation
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.Torsion

public section

open CategoryTheory

namespace NonorientableSurfacePresentation

/-- Theorem 75.4 (1). The torsion subgroup of the integral first homology of the
`m`-fold connected sum of projective planes has order `2`. -/
theorem firstHomology_torsion_card (m : ℕ) (hm : 1 < m) :
    Nat.card
        (AddCommGroup.torsion
          (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
              (AddCommGrpCat.of ℤ)).obj
            (TopCat.of (mFoldProjectivePlane m hm)))) =
      2 := sorry

/-- Theorem 75.4 (2). The quotient of the integral first homology of the `m`-fold
connected sum of projective planes by its torsion subgroup is free abelian of rank
`m - 1`. -/
theorem firstHomology_quotientTorsion_equiv (m : ℕ) (hm : 1 < m) :
    Nonempty
      (((((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
              (AddCommGrpCat.of ℤ)).obj
            (TopCat.of (mFoldProjectivePlane m hm))) ⧸
          AddCommGroup.torsion
            (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
                (AddCommGrpCat.of ℤ)).obj
              (TopCat.of (mFoldProjectivePlane m hm)))) ≃+
        FreeAbelianGroup (Fin (m - 1))) := sorry

end NonorientableSurfacePresentation

end
