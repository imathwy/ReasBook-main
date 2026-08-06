import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Tactic.Recall

open CategoryTheory Simplicial

-- Semantic recall via `lean_leansearch`: `SSet.S.toN`, `SSet.S.subcomplex_toN`,
-- `SSet.exists_nonDegenerate`, `SSet.unique_nonDegenerate_simplex`,
-- `SSet.unique_nonDegenerate_map`, and `SSet.N.le_iff_exists_mono` are the
-- canonical owners for the textbook reduction maps `lambda` and `rho` after
-- specializing to `TopCat.toSSet.obj X`.

universe u

variable (X : TopCat.{u})

/- Construction 16.3.1. For the singular simplicial set `TopCat.toSSet.obj X`,
the textbook reduction maps `lambda` and `rho` are the canonical simplicial-set
API sending a simplex to its unique nondegenerate representative and recording
its degeneracy decomposition. Concretely, `SSet.S.toN` and
`SSet.S.subcomplex_toN` give the representative generating the same subcomplex,
while `SSet.exists_nonDegenerate`, `SSet.unique_nonDegenerate_map`, and
`SSet.unique_nonDegenerate_simplex` give the decomposition
`x = (TopCat.toSSet.obj X).map f.op y` and its uniqueness. The face component of
`rho` is recovered from `SSet.N.le_iff_exists_mono`, which identifies a face
relation `x ≤ y` between nondegenerate simplices with a mono
`f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌` satisfying
`(TopCat.toSSet.obj X).map f.op y.simplex = x.simplex`. -/
recall SSet.S.toN
recall SSet.S.subcomplex_toN
recall SSet.exists_nonDegenerate
recall SSet.unique_nonDegenerate_map
recall SSet.unique_nonDegenerate_simplex
recall SSet.N.le_iff_exists_mono

#check (SSet.S.toN : (TopCat.toSSet.obj X).S → (TopCat.toSSet.obj X).N)
#check ((TopCat.toSSet.obj X).exists_nonDegenerate)
#check (SSet.N.le_iff_exists_mono :
    ∀ {x y : (TopCat.toSSet.obj X).N},
      x ≤ y ↔
        ∃ (f : ⦋x.dim⦌ ⟶ ⦋y.dim⦌) (_ : Mono f),
          (TopCat.toSSet.obj X).map f.op y.simplex = x.simplex)
