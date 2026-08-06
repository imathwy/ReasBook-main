import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_3_1
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

noncomputable section

universe u

open CategoryTheory

-- Definition 17.3.2 is source-facing but not a new owner: for the cochain complex
-- `homCochainComplex R X M`, the canonical graded cohomology owner is degreewise homology,
-- equivalently the graded object `(HomologicalComplex.gradedHomologyFunctor _ _).obj _`.

/-- Definition 17.3.2. For a chain complex `X` of `R`-modules and an `R`-module `M`, the
cohomology of `X` with coefficients in `M` is the graded family `H^*(Hom(X, M))`, formalized as
the graded homology object of `homCochainComplex R X M`. -/
abbrev cohomologyWithCoefficients (R : Type u) [Ring R]
    (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) :
    ℤ → ModuleCat ℤ :=
  fun n ↦
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℤ) n).obj
      (homCochainComplex R X M)

/-- Evaluating `cohomologyWithCoefficients R X M` in degree `n` recovers the degree-`n`
cohomology object of `Hom(X, M)`. -/
@[simp] theorem cohomologyWithCoefficients_apply (R : Type u) [Ring R]
    (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    cohomologyWithCoefficients R X M n = (homCochainComplex R X M).homology n :=
  rfl
