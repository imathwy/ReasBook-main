module

public import Topology_Munkres_2000.Book.Definition_74_5.OrientablePasting
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.GroupTheory.FreeAbelianGroup

public section

open CategoryTheory

namespace OrientableSurfacePresentation

/-- Theorem 75.3. If `X` is the `n`-fold connected sum of tori, then its first
integral singular homology group is free abelian of rank `2 * n`. -/
theorem firstHomologyIsoFreeAbelian (n : ℕ) (hn : 0 < n) :
    Nonempty
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
          (AddCommGrpCat.of ℤ)).obj (TopCat.of (nFoldTorus n hn)) ≅
        AddCommGrpCat.of (FreeAbelianGroup (Fin (2 * n)))) := sorry

end OrientableSurfacePresentation

end
