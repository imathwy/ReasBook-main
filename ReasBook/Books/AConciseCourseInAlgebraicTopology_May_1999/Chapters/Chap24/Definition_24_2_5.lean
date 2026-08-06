import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_2_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_2

open CategoryTheory Opposite HomotopicalAlgebra
open scoped ComplexKTheory

universe u

local notation "BasedCWComplex" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex

/-- Definition 24.2.5. A prespectrum `KU` represents complex `K`-theory when it is an
`Ω`-prespectrum and, for every based CW complex `X`, its degree-`0` represented reduced
cohomology group is identified with the reduced complex `K`-theory group
`K̃(X.obj.right, underTopBasepoint X.obj)`. The unreduced comparison is recovered from the canonical
splitting `complexKTheoryReducedProdIntEquiv`. -/
class ComplexKTheoryPrespectrum (KU : Prespectrum.{u, 0}) extends OmegaPrespectrum KU where
  /-- On every based CW complex `X`, the degree-`0` represented reduced cohomology group of `KU`
  identifies with the reduced complex `K`-theory group of the underlying based space. -/
  reducedComparison (X : BasedCWComplex) :
    (omegaPrespectrumReducedCohomologyAdditive KU 0).obj (op X) ≃+
      K̃(X.obj.right, underTopBasepoint X.obj)

namespace ComplexKTheoryPrespectrum

variable {KU : Prespectrum.{u, 0}} [ComplexKTheoryPrespectrum KU]

/-- For any chosen Chapter 22 reduced-theory setup, the packaged reduced cohomology theory
represented by `KU` has degree-`0` group identified with reduced complex `K`-theory on each
based CW complex. -/
abbrev reducedTheoryComparison
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup)
    (X : BasedCWComplex) :
    ((omegaPrespectrumRepresentsReducedCohomologyTheory setup KU).cohomology 0).obj (op X) ≃+
      K̃(X.obj.right, underTopBasepoint X.obj) :=
  reducedComparison X

/-- The unreduced complex `K`-theory group of a based CW complex is recovered from the degree-`0`
represented reduced cohomology group of `KU` by adjoining the integer dimension summand and using
the canonical Chapter 24 splitting `K(X) ≃ K̃(X, x₀) × ℤ`. -/
noncomputable def unreducedComparison
    (X : BasedCWComplex) :
    ((omegaPrespectrumReducedCohomologyAdditive KU 0).obj (op X) × ℤ) ≃+
      K(X.obj.right) :=
  ((reducedComparison X).prodCongr (AddEquiv.refl ℤ)).trans
    (complexKTheoryReducedProdIntEquiv X.obj.right (underTopBasepoint X.obj)).symm

/-- `unreducedComparison X` is the composition of the degree-`0` reduced comparison with the
canonical splitting equivalence for `K(X.obj.right)`. -/
theorem unreducedComparison_def
    (X : BasedCWComplex) :
    let e : (omegaPrespectrumReducedCohomologyAdditive KU 0).obj (op X) ≃+
        K̃(X.obj.right, underTopBasepoint X.obj) := reducedComparison X
    unreducedComparison X =
      (e.prodCongr (AddEquiv.refl ℤ)).trans
        (complexKTheoryReducedProdIntEquiv X.obj.right (underTopBasepoint X.obj)).symm := by
  rfl

end ComplexKTheoryPrespectrum
