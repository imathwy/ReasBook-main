import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_1

open CategoryTheory Limits
open HomotopicalAlgebra
open SpacePair

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a canonical library equivalence for this
-- theorem. Local precedent from Chapter 18 supplies the source-faithful owner
-- `PairCohomologyTheory`, and Definition 19.2.1 now bundles the reduced side by
-- `NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces`.

local notation "NBasedSpace" => nondegeneratelyBasedSpace

/-- Theorem 19.2.2: for a coefficient group `π`, cohomology theories on pairs with coefficients in
`π` are equivalent to `π`-normalized reduced cohomology theories on nondegenerately based spaces.
For a chosen Chapter 14 reduced suspension/cofiber setup on `NBasedSpace` and a chosen initial
object `pt` modeling the one-point based space, this is stated as the existence of an explicit
equivalence between the source-faithful owner `PairCohomologyTheory π` from Theorem 18.1.1 and
the bundled owner
`NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces π pt setup`. -/
theorem pairCohomologyTheoryEquivReducedCohomologyTheory
    (π : Type) [AddCommGroup π]
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (pt : NBasedSpace) (hpt : Limits.IsInitial pt) :
    Nonempty
      (PairCohomologyTheory π ≃
        NormalizedReducedCohomologyTheoryOnNondegeneratelyBasedSpaces π pt setup) := sorry
