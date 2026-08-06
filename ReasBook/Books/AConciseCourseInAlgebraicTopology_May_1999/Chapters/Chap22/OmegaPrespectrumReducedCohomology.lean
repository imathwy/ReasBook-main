import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.BasedHomotopyClasses
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_4

open BasedHomotopyClasses
open scoped HomotopyClasses

universe u w

/-- The `n`-fold iterated based loop space of a based space. -/
noncomputable abbrev iteratedLoopBasedSpace (n : ℕ) (X : BasedSpace.{w}) : BasedSpace.{w} :=
  Nat.iterate loopBasedSpace n X

/-- The representing based space for the degree-`q` reduced cohomology surface attached to a
prespectrum `T`. In nonnegative degree this is `T q`, and in negative degree it is the
corresponding iterated loop space of `T 0`. -/
noncomputable def omegaPrespectrumRepresentingBasedSpace
    (T : Prespectrum.{u, w}) (q : ℤ) : BasedSpace.{w} :=
  if _ : 0 ≤ q then
    PointedCompactlyGenerated.toBasedSpace (T (Int.toNat q))
  else
    iteratedLoopBasedSpace q.natAbs (PointedCompactlyGenerated.toBasedSpace (T 0))

/-- The source-facing represented graded functor attached to a prespectrum `T`: in degree `q` it
sends a based CW complex `X` to the pointed set of based homotopy classes `[X, R_q(T)]`, where
`R_q(T)` is `T q` for `q ≥ 0` and the corresponding iterated loop space for `q < 0`. -/
noncomputable def omegaPrespectrumReducedCohomology
    (T : Prespectrum.{u, w}) (q : ℤ) :
    CategoryTheory.Functor BasedCWComplexᵒᵖ Pointed :=
  BasedHomotopyClasses.onBasedCWComplexes (omegaPrespectrumRepresentingBasedSpace T q)

/-- Degreewise, the reduced cohomology functor attached to a prespectrum `T` is represented by
based homotopy classes into `omegaPrespectrumRepresentingBasedSpace T q`. -/
@[simp]
theorem omegaPrespectrumReducedCohomology_obj
    (T : Prespectrum.{u, w}) (q : ℤ) (X : BasedCWComplex) :
    (omegaPrespectrumReducedCohomology T q).obj (Opposite.op X) =
      Ho*[X.1, omegaPrespectrumRepresentingBasedSpace T q] :=
  rfl
