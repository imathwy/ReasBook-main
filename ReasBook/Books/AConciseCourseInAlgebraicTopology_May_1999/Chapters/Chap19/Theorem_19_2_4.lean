import Books.AConciseCourseInAlgebraicTopology_May_1999.BasedCWComplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_4_5

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a canonical library theorem for this
-- determination statement. The file therefore uses the Chapter 19 reduced-theory owner on the
-- underlying graded functor together with its restriction to the Definition 19.2.3 owner on
-- based CW complexes.
attribute [class] ReducedSuspensionCofiberSetup.RestrictsToBasedCWComplexes

local notation "NBasedSpace" => nondegeneratelyBasedSpace

/-- Restrict a graded contravariant functor on nondegenerately based spaces to based CW complexes
along the inclusion induced by `hCWtoN`. -/
abbrev restrictGradedCohomologyToBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0}) :
    ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat.{0} :=
  fun q ↦ (CategoryTheory.ObjectProperty.ιOfLE hCWtoN).op ⋙ E q

private theorem restrictReducedCohomologyTheoryToBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : ReducedSuspensionCofiberSetup)
    (basedCWSetup : BasedCWReducedSuspensionCofiberSetup)
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (hrestrictSetup :
      setup.RestrictsToBasedCWComplexes hCWtoN basedCWSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0})
    [ReducedCohomologyTheory setup E] :
    ReducedCohomologyTheoryOnBasedCWComplexes
      basedCWSetup
      (restrictGradedCohomologyToBasedCWComplexes hCWtoN E) := by
  sorry

namespace ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces

/-- The underlying graded functor of a bundled reduced cohomology theory restricted to based CW
complexes along the inclusion induced by `hCWtoN`. -/
abbrev restrictToBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (E : ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat.{0} :=
  restrictGradedCohomologyToBasedCWComplexes hCWtoN E.cohomology

@[simp] theorem restrictToBasedCWComplexes_def
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup}
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (E : ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    E.restrictToBasedCWComplexes hCWtoN =
      restrictGradedCohomologyToBasedCWComplexes hCWtoN E.cohomology :=
  rfl

/-- The restricted underlying graded functor of a bundled reduced cohomology theory again
satisfies the based-CW reduced cohomology axioms, once the chosen based-CW suspension/cofiber
setup is specified explicitly. -/
instance instRestrictToBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : ReducedSuspensionCofiberSetup}
    (basedCWSetup : BasedCWReducedSuspensionCofiberSetup)
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    [setup.RestrictsToBasedCWComplexes hCWtoN basedCWSetup]
    (E : ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces setup) :
    ReducedCohomologyTheoryOnBasedCWComplexes
      basedCWSetup
      (E.restrictToBasedCWComplexes hCWtoN) :=
  _root_.restrictReducedCohomologyTheoryToBasedCWComplexes
    setup basedCWSetup hCWtoN inferInstance E.cohomology

end ReducedCohomologyTheoryOnNondegeneratelyBasedSpaces

/-- Theorem 19.2.4: reduced cohomology theories on nondegenerately based spaces are determined by
their restrictions to based CW complexes. Concretely, once based CW complexes are viewed as
nondegenerately based spaces via `hCWtoN`, equality of the restricted underlying graded
cohomology functors on based CW complexes forces equality of the original reduced cohomology
theories. -/
theorem reducedCohomologyTheory_eq_of_restrictToBasedCWComplexes_eq
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (E F : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat.{0})
    [ReducedCohomologyTheory setup E]
    [ReducedCohomologyTheory setup F]
    (hrestrict :
      restrictGradedCohomologyToBasedCWComplexes hCWtoN E =
        restrictGradedCohomologyToBasedCWComplexes hCWtoN F) :
    E = F := sorry
