import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Functor.Currying

open CategoryTheory

-- Semantic recall via `lean_leansearch`: `SSet.toTop` in
-- `Mathlib.AlgebraicTopology.SingularSet` is the canonical owner for geometric realization of a
-- simplicial set, defined as the left Kan extension of `SimplexCategory.toTop`. For the
-- simplicial-space side, the local canonical input object is `CategoryTheory.SimplicialObject
-- TopCat`, paired with the same cosimplicial topological simplex `SimplexCategory.toTop`.

variable (X : SSet)

noncomputable section

namespace CategoryTheory.SimplicialObject

/-- The levelwise singular simplicial set of a simplicial space, viewed as a bisimplicial set. -/
abbrev singularBisimplicialSet (X : SimplicialObject TopCat) : SimplicialObject SSet :=
  ((SimplicialObject.whiskering TopCat SSet).obj TopCat.toSSet).obj X

/-- The diagonal simplicial set attached to the levelwise singular simplicial set of a simplicial
space. -/
abbrev diagonalSingularSet (X : SimplicialObject TopCat) : SSet :=
  Functor.diag (SimplexCategoryᵒᵖ) ⋙ Functor.uncurry.obj (singularBisimplicialSet X)

/-- The geometric realization of a simplicial space, formed by realizing the diagonal simplicial
set of its levelwise singular complex. -/
abbrev geometricRealization (X : SimplicialObject TopCat) : TopCat :=
  SSet.toTop.obj (diagonalSingularSet X)

end CategoryTheory.SimplicialObject

/- Construction 16.4.3. The geometric realization of a simplicial set is canonically formalized by
`SSet.toTop.obj X`, equivalently the left Kan extension of `SimplexCategory.toTop` along the
Yoneda embedding. For simplicial spaces, the corresponding source object is
`CategoryTheory.SimplicialObject TopCat`, and the same realization quotient construction is built
from the cosimplicial topological simplex `SimplexCategory.toTop`; in this file that bridge is
recorded by `CategoryTheory.SimplicialObject.singularBisimplicialSet`,
`CategoryTheory.SimplicialObject.diagonalSingularSet`, and
`CategoryTheory.SimplicialObject.geometricRealization`, matching the recipe used for `Γ X` in
Construction 16.2.1. -/
#check (SSet.toTop : SSet ⥤ TopCat)
#check (SSet.toTop.obj X : TopCat)
#check (SimplicialObject TopCat : Type _)
#check (SimplexCategory.toTop : CategoryTheory.CosimplicialObject TopCat)
#check
  (CategoryTheory.SimplicialObject.singularBisimplicialSet :
    SimplicialObject TopCat → SimplicialObject SSet)
#check (CategoryTheory.SimplicialObject.diagonalSingularSet : SimplicialObject TopCat → SSet)
#check (CategoryTheory.SimplicialObject.geometricRealization : SimplicialObject TopCat → TopCat)

end
