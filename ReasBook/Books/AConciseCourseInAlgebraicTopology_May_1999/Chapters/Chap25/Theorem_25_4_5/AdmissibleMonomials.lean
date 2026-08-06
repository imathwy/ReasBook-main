module

public import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.SteenrodMultiIndex
public import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_4_1

public section

noncomputable section

open scoped SteenrodAlgebra

/-- The subtype of Steenrod multiindices indexing the admissible monomials in
`ModTwoSteenrodAlgebra`. -/
abbrev AdmissibleSteenrodMonomialIndex :=
  {I : SteenrodMultiIndex // SteenrodMultiIndex.Admissible I}

/-- An index in `AdmissibleSteenrodMonomialIndex` is exactly an admissible Steenrod multiindex. -/
theorem admissibleSteenrodMonomialIndex_spec (I : AdmissibleSteenrodMonomialIndex) :
    SteenrodMultiIndex.Admissible I.1 :=
  I.2

/-- The monomial `Sq^I` in `ModTwoSteenrodAlgebra`, defined by multiplying the generators `Sq^i`
along the multiindex `I`. -/
def modTwoSteenrodAlgebraMonomial : SteenrodMultiIndex → ModTwoSteenrodAlgebra
  | [] => 1
  | i :: I => Sq^i * modTwoSteenrodAlgebraMonomial I

/-- The admissible monomial `Sq^I` attached to an admissible Steenrod multiindex. -/
abbrev admissibleSteenrodMonomial (I : AdmissibleSteenrodMonomialIndex) :
    ModTwoSteenrodAlgebra :=
  modTwoSteenrodAlgebraMonomial I.1

/-- `admissibleSteenrodMonomial I` is the Steenrod monomial attached to the underlying
admissible multiindex. -/
theorem admissibleSteenrodMonomial_eq (I : AdmissibleSteenrodMonomialIndex) :
    admissibleSteenrodMonomial I = modTwoSteenrodAlgebraMonomial I.1 :=
  rfl

/-- The empty Steenrod multiindex gives the unit monomial in `ModTwoSteenrodAlgebra`. -/
theorem modTwoSteenrodAlgebraMonomial_nil :
    modTwoSteenrodAlgebraMonomial [] = 1 :=
  by simp [modTwoSteenrodAlgebraMonomial]

/-- Appending a leading index multiplies the corresponding generator on the left of the
tail monomial. -/
theorem modTwoSteenrodAlgebraMonomial_cons (i : ℕ) (I : SteenrodMultiIndex) :
    modTwoSteenrodAlgebraMonomial (i :: I) =
      Sq^i * modTwoSteenrodAlgebraMonomial I :=
  by simp [modTwoSteenrodAlgebraMonomial]
