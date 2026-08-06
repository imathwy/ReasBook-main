import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_2_1.Representation

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced only general cohomology and homotopy-group
-- infrastructure. The reusable owner layer for Theorem 22.2.1 now lives in the item-local
-- foundation module `Theorem_22_2_1.Representation`; this file keeps only the source-facing
-- existential statement.

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

/-- Theorem 22.2.1: degree-`n` reduced cohomology with coefficients in `π` on based CW complexes
is representable by some additive `K(π, n)` model, together with a reduced cohomology theory on a
chosen based-CW setup and a natural comparison isomorphism
`H̃^n(-; π) ≅ [−, K(π, n)]`. -/
theorem existsReducedCohomologyEilenbergMacLaneRepresentation
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (π : Type) [AddCommGroup π] (n : ℕ) :
    ∃ (setup : BasedCWReducedSuspensionCofiberSetup)
      (theory : BundledReducedCohomologyTheory setup)
      (K : BasedSpace)
      (comparison : reducedCohomologyToBasedHomotopyClassesIso theory n K),
      IsAdditiveEilenbergMacLaneSpaceAtDegree π n K := sorry
