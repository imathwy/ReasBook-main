import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.Single
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.AlgebraicTopology.SingularSet
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Problem_15_3_4

open CategoryTheory
open CategoryTheory.Abelian.DoldKan
open scoped Simplicial

universe u

noncomputable section

-- Semantic recall via `lean_leansearch`: `CategoryTheory.Abelian.DoldKan.Γ` supplies the
-- simplicial-Abelian-group owner, while `SSet.toTop` is the canonical realization functor.
-- For the CW route, the local owner is `existsConnectedCWComplexKPiSucc`.

/-- The simplicial abelian group obtained from the chain complex with value
`AddCommGrpCat.of (Additive π)` in degree `n + 1` and zero elsewhere. -/
noncomputable abbrev kPiSuccSimplicialAbelianGroup (π : Type u) [CommGroup π] (n : ℕ) :
    CategoryTheory.SimplicialObject AddCommGrpCat :=
  Γ.obj
    ((HomologicalComplex.single AddCommGrpCat (ComplexShape.down ℕ) (n + 1)).obj
      (AddCommGrpCat.of (Additive π)))

namespace kPiSuccSimplicialAbelianGroup

/-- The underlying simplicial set of `kPiSuccSimplicialAbelianGroup π n`. -/
noncomputable abbrev toSSet (π : Type u) [CommGroup π] (n : ℕ) : SSet :=
  kPiSuccSimplicialAbelianGroup π n ⋙ forget AddCommGrpCat

/-- The geometric realization of `kPiSuccSimplicialAbelianGroup π n`. -/
noncomputable abbrev realization (π : Type u) [CommGroup π] (n : ℕ) : TopCat :=
  SSet.toTop.obj (toSSet π n)

/-- `kPiSuccSimplicialAbelianGroup.realization π n` is the realization of the underlying
simplicial set of `kPiSuccSimplicialAbelianGroup π n`. -/
@[simp] theorem realization_def (π : Type u) [CommGroup π] (n : ℕ) :
    realization π n = SSet.toTop.obj (toSSet π n) :=
  rfl

end kPiSuccSimplicialAbelianGroup

/-- Construction 16.5.4 (1): the realization of `kPiSuccSimplicialAbelianGroup π n` gives the
simplicial-Abelian-group route to a `K(π, n + 1)` space. -/
theorem kPiSuccSimplicialAbelianGroup_spec (π : Type u) [CommGroup π] (n : ℕ) :
    ∃ x : kPiSuccSimplicialAbelianGroup.realization π n,
      IsKPiSucc π n (kPiSuccSimplicialAbelianGroup.realization π n) x :=
  sorry

/-
Construction 16.5.4 (2): the Hurewicz-chapter CW construction route is the previously established
existence statement `existsConnectedCWComplexKPiSucc π n :
  ∃ (X : TopCat.{u}) (x : X), IsKPiSucc π n X x`.
-/
#check existsConnectedCWComplexKPiSucc

end
