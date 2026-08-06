import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory
open HomologicalComplex

universe u

-- Mathlib packages degreewise homology by the canonical functor `gradedHomologyFunctor`, and the
-- generated theorem `gradedHomologyFunctor_obj` identifies each graded piece with `X.homology i`.

variable (R : Type u) [CommRing R]
variable (X : ChainComplex (ModuleCat R) ℕ) (i : ℕ)

/- Remark 12.1.4. The graded object `H_*(X)` is formalized by
`(gradedHomologyFunctor (ModuleCat R) (ComplexShape.down ℕ)).obj X : GradedObject ℕ (ModuleCat R)`.
Its component in degree `i` is `X.homology i`, so this object records the homology modules
degree by degree, without summing elements across different degrees. -/
#check ((gradedHomologyFunctor (ModuleCat R) (ComplexShape.down ℕ)).obj X :
    GradedObject ℕ (ModuleCat R))
#check (gradedHomologyFunctor_obj (ModuleCat R) (ComplexShape.down ℕ) X i :
    ((gradedHomologyFunctor (ModuleCat R) (ComplexShape.down ℕ)).obj X) i = X.homology i)
