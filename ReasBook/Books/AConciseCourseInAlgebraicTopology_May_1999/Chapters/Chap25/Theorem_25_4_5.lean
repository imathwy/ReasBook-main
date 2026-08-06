import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_5.AdmissibleMonomials

noncomputable section

open scoped SteenrodAlgebra

-- A concrete `Module.Basis` would add chosen coordinate data. The source theorem only asserts
-- that the admissible monomials form a basis, so this file records that statement at the
-- source-facing `LinearIndependent` + `span = ⊤` layer.

/-- The admissible Steenrod monomials `Sq^I` are linearly independent over `ZMod 2`. -/
theorem modTwoSteenrodAlgebraMonomial_linearIndependent :
    LinearIndependent (ZMod 2)
      admissibleSteenrodMonomial := sorry

/-- The admissible Steenrod monomials `Sq^I` span the whole mod-`2` Steenrod algebra. -/
theorem modTwoSteenrodAlgebraMonomial_span :
    Submodule.span (ZMod 2)
        (Set.range admissibleSteenrodMonomial) =
      ⊤ := sorry

/-- Theorem 25.4.5. The mod-`2` Steenrod algebra `A = ModTwoSteenrodAlgebra` has the admissible
monomials `Sq^I`, indexed by multiindices satisfying `i_r ≥ 2 * i_{r+1}`, as a `ZMod 2`-basis. -/
theorem modTwoSteenrodAlgebraBasisOfAdmissibleMonomials :
    LinearIndependent (ZMod 2) admissibleSteenrodMonomial ∧
      Submodule.span (ZMod 2) (Set.range admissibleSteenrodMonomial) = ⊤ :=
  ⟨modTwoSteenrodAlgebraMonomial_linearIndependent, modTwoSteenrodAlgebraMonomial_span⟩
