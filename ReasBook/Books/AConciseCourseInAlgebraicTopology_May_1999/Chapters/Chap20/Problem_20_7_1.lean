import Mathlib.Topology.Homotopy.Equiv
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ComplexProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

/-- The top-dimensional integral singular homology of `CP^(2n)`. -/
abbrev complexProjectiveSpaceEvenTopIntegralHomology (n : ℕ) : ModuleCat ℤ :=
  integralSingularHomology (4 * n) (TopCat.of (ComplexProjectiveSpace (2 * n)))

/-- The endomorphism of top-dimensional integral singular homology induced by a self-homotopy
equivalence of `CP^(2n)`. -/
abbrev complexProjectiveSpaceEvenTopIntegralHomologyMap (n : ℕ)
    (e : ComplexProjectiveSpace (2 * n) ≃ₕ ComplexProjectiveSpace (2 * n)) :
    complexProjectiveSpaceEvenTopIntegralHomology n ⟶
      complexProjectiveSpaceEvenTopIntegralHomology n :=
  (((singularHomologyFunctor (ModuleCat ℤ) (4 * n)).obj (ModuleCat.of ℤ ℤ)).map
    (TopCat.ofHom e.toFun))

/-- A top-dimensional integral homology class of `CP^(2n)` is a generator when it spans the
whole module. -/
def isComplexProjectiveSpaceEvenTopIntegralHomologyGenerator (n : ℕ)
    (η : complexProjectiveSpaceEvenTopIntegralHomology n) : Prop :=
  Submodule.span ℤ ({η} : Set (complexProjectiveSpaceEvenTopIntegralHomology n)) = ⊤

/-- A self-homotopy equivalence of `CP^(2n)` is orientation-reversing when its action on top
integral homology sends a generator to its negative. -/
def complexProjectiveSpaceEvenOrientationReversing (n : ℕ)
    (e : ComplexProjectiveSpace (2 * n) ≃ₕ ComplexProjectiveSpace (2 * n)) : Prop :=
  ∃ η : complexProjectiveSpaceEvenTopIntegralHomology n,
    isComplexProjectiveSpaceEvenTopIntegralHomologyGenerator n η ∧
      complexProjectiveSpaceEvenTopIntegralHomologyMap n e η = -η

/-
The source proof uses the generator `x ∈ H²(CP^(2n); ℤ)` and the nonzero top cup power
`x^(2n)`.  A self-homotopy equivalence sends `x` to `±x`; because the exponent `2n` is even, it
fixes the top cohomology class and hence preserves the orientation.  The current cohomology API
still lacks the final UCT/evaluation bridge to the top-homology action, so that bridge is recorded
as one explicit proof gap rather than as unrelated unfinished chain-level infrastructure.
-/

/-- Problem 20.7.1: there is no orientation-reversing self-homotopy equivalence
`CP^(2n) → CP^(2n)`. -/
theorem not_exists_orientationReversingSelfHomotopyEquiv_complexProjectiveSpace_even (n : ℕ) :
    ¬ ∃ e : ComplexProjectiveSpace (2 * n) ≃ₕ ComplexProjectiveSpace (2 * n),
      complexProjectiveSpaceEvenOrientationReversing n e := by
  sorry
