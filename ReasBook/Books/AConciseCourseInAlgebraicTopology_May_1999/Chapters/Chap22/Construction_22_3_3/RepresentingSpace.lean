import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_2_1.Representation

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

namespace ReducedCohomologyEilenbergMacLaneRepresentation

/-- The representing space carried by an explicit representation datum has the based CW complex
structure needed to evaluate reduced cohomology on it. -/
theorem isBasedCWComplex
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π : Type} [AddCommGroup π] {n : ℕ}
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π n) :
    IsBasedCWComplex R.space := sorry

/-- The representing space carried by an explicit degree-`n` representation datum, bundled as a
based CW complex for evaluating reduced cohomology. -/
noncomputable abbrev basedCWComplex
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π : Type} [AddCommGroup π] {n : ℕ}
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π n) :
    BasedCWComplex :=
  ⟨R.space, R.isBasedCWComplex⟩

end ReducedCohomologyEilenbergMacLaneRepresentation
