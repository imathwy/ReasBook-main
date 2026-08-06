import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_2_5

open CategoryTheory Opposite HomotopicalAlgebra
open scoped ComplexKTheory

universe u

noncomputable section

local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

namespace ComplexKTheoryPrespectrum

variable {KU : Prespectrum.{u, 0}} [ComplexKTheoryPrespectrum KU]

/-- The degree-`0` homotopy-class comparison carried by a complex `K`-theory prespectrum `KU`.
This is the source-facing bridge from the represented pointed set
`[(X : BasedCWComplex), omegaPrespectrumRepresentingBasedSpace KU 0]` to reduced complex
`K`-theory on the underlying based space of `X`. The unreduced group `K(X.obj.right)` is then
recovered from the same prespectrum by the existing canonical owner
`ComplexKTheoryPrespectrum.unreducedComparison X`. -/
noncomputable def reducedHomotopyClassesToReducedKTheory
    (X : BasedCWComplex) :
    (omegaPrespectrumReducedCohomology KU 0).obj (op X) →
      K̃(X.obj.right, underTopBasepoint X.obj) :=
  fun ξ ↦
    reducedComparison X
      ((omegaPrespectrumReducedCohomologyAdditiveComparison KU 0).app (op X) ξ)

/-- `reducedHomotopyClassesToReducedKTheory X` sends the distinguished based homotopy class to the
zero class in reduced complex `K`-theory. -/
theorem reducedHomotopyClassesToReducedKTheory_point
    (X : BasedCWComplex) :
    reducedHomotopyClassesToReducedKTheory X
        ((omegaPrespectrumReducedCohomology KU 0).obj (op X)).point = 0 := by
  change reducedComparison X
      (((omegaPrespectrumReducedCohomologyAdditiveComparison KU 0).app (op X)).toFun
        ((omegaPrespectrumReducedCohomology KU 0).obj (op X)).point) = 0
  rw [((omegaPrespectrumReducedCohomologyAdditiveComparison KU 0).app (op X)).map_point]
  change reducedComparison X 0 = 0
  simpa using (reducedComparison X).map_zero

/-- The explicit comparison map `reducedHomotopyClassesToReducedKTheory X` is bijective. -/
theorem reducedHomotopyClassesToReducedKTheory_bijective
    (X : BasedCWComplex) :
    Function.Bijective
      (reducedHomotopyClassesToReducedKTheory X :
        (omegaPrespectrumReducedCohomology KU 0).obj (op X) →
          K̃(X.obj.right, underTopBasepoint X.obj)) :=
  (reducedComparison X).bijective.comp
    (omegaPrespectrumReducedCohomologyAdditiveComparison_bijective KU 0 X)

/-- Definition 24.1.7. On based CW complexes, the degree-`0` representing space of a complex
`K`-theory prespectrum `KU` realizes reduced complex `K`-theory by based homotopy classes. This
equivalence is carried by the explicit comparison map
`reducedHomotopyClassesToReducedKTheory X`. The unreduced comparison on the underlying space is
the existing additive equivalence `ComplexKTheoryPrespectrum.unreducedComparison X`. -/
noncomputable def reducedHomotopicalDefinition
    (X : BasedCWComplex) :
    (omegaPrespectrumReducedCohomology KU 0).obj (op X) ≃
      K̃(X.obj.right, underTopBasepoint X.obj) :=
  Equiv.ofBijective
    (reducedHomotopyClassesToReducedKTheory X)
    (reducedHomotopyClassesToReducedKTheory_bijective X)

/-- `reducedHomotopyClassesToReducedKTheory X` is induced by the composite of the Chapter 22
degree-`0` comparison into the additive represented theory and the Chapter 24 reduced comparison
for `KU`. -/
theorem reducedHomotopyClassesToReducedKTheory_apply
    (X : BasedCWComplex) (ξ : (omegaPrespectrumReducedCohomology KU 0).obj (op X)) :
    reducedHomotopyClassesToReducedKTheory X ξ =
      reducedComparison X
        ((omegaPrespectrumReducedCohomologyAdditiveComparison KU 0).app (op X) ξ) :=
  rfl

/-- `reducedHomotopicalDefinition X` has underlying forward map
`reducedHomotopyClassesToReducedKTheory X`. -/
theorem reducedHomotopicalDefinition_apply
    (X : BasedCWComplex) (ξ : (omegaPrespectrumReducedCohomology KU 0).obj (op X)) :
    reducedHomotopicalDefinition X ξ = reducedHomotopyClassesToReducedKTheory X ξ :=
  rfl

end ComplexKTheoryPrespectrum
