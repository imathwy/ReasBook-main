import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Construction_22_3_3.RepresentingSpace

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

-- Semantic recall via `lean_leansearch` surfaced only generic cohomology APIs. The local Chapter
-- 22 owner `ReducedCohomologyEilenbergMacLaneRepresentation` now carries the reduced theory,
-- representing space, and comparison isomorphism used directly for the labeled fundamental class
-- below.

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

/-- The degree-`n` source-facing reduced cohomology group with coefficients in `π`, evaluated at a
based CW complex `K`. -/
abbrev reducedCohomologyWithCoefficientsAt
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (theory : BundledReducedCohomologyTheory setup) (n : ℕ)
    (K : BasedCWComplex) :
    AddCommGrpCat :=
  ((theory.cohomology (n : ℤ)).obj (Opposite.op K))

/-- The inverse image of the identity self-map class under a chosen comparison from degree-`n`
reduced cohomology to based homotopy classes into a fixed `K(π, n)` model `K`. -/
private noncomputable def fundamentalCohomologyClassOfComparison
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (theory : BundledReducedCohomologyTheory setup)
    (n : ℕ) (K : BasedCWComplex)
    (comparison : reducedCohomologyToBasedHomotopyClassesIso theory n K.1) :
    reducedCohomologyWithCoefficientsAt theory n K :=
  (comparison.app (Opposite.op K)).inv.toFun
    (Quotient.mk (basedHomotopySetoid K.1 K.1) (𝟙 K.1))

/-- Construction 22.3.3: the fundamental cohomology class `ι_n` on the based `K(π, n)` model
carried by an explicit representation datum, namely the reduced cohomology class corresponding to
the identity self-map under its representability comparison. -/
noncomputable def fundamentalCohomologyClass
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π : Type} [AddCommGroup π] {n : ℕ}
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π n) :
    reducedCohomologyWithCoefficientsAt
      R.theory
      n
      R.basedCWComplex :=
  fundamentalCohomologyClassOfComparison
    R.theory
    n
    R.basedCWComplex
    (reducedCohomology_isRepresentedByAdditiveEilenbergMacLaneSpace R)

/-- The class `fundamentalCohomologyClass R` represents the identity self-map of the `K(π, n)`
model carried by `R` under its reduced-side comparison. For `0 < n`, this is the source-facing
fundamental class `ι_n ∈ H^n(K(π, n); π)`. -/
theorem fundamentalCohomologyClass_spec
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {π : Type} [AddCommGroup π] {n : ℕ}
    (R : ReducedCohomologyEilenbergMacLaneRepresentation π n) :
    (((reducedCohomology_isRepresentedByAdditiveEilenbergMacLaneSpace R).app
        (Opposite.op R.basedCWComplex)).hom.toFun
      (fundamentalCohomologyClass R)) =
      Quotient.mk
        (basedHomotopySetoid
          R.space
          R.space)
        (𝟙 R.space) := sorry
