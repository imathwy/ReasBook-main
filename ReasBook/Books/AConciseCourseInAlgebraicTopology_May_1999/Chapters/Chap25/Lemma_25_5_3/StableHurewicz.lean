import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_4_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_6.DualAlgebra

open scoped TensorProduct

noncomputable section

universe u w

/-- The source-semantic primitive-image condition from Lemma 25.5.3 for a chosen stable
Hurewicz map, coaction datum, and chosen dual Steenrod algebra owner
`AStar : ModTwoSteenrodAlgebraDualAlgebra` on the fixed linear dual `A_*`. -/
def prespectrumModTwoStableHurewiczPrimitiveImage
    (T : Prespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (AStar : ModTwoSteenrodAlgebraDualAlgebra)
    (map : ∀ n : ℤ, Prespectrum.stableHomotopyGroup T n → homologyPresentation.HStar T)
    (sourceCoaction :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation) : Prop :=
  ∀ n : ℤ,
    ∀ x : Prespectrum.stableHomotopyGroup T n,
      sourceCoaction T (map n x) =
        ((AStar.one ⊗ₜ[ZMod 2] map n x) :
          modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)] homologyPresentation.HStar T)

/-- A chosen source-facing stable Hurewicz owner for `T`, packaging the map
`π_*(T) → H_*(T)` together with a chosen dual Steenrod algebra owner on the fixed graded dual
`A_*` and the coaction datum from Construction 25.4.9.  The compatibility between the Hurewicz
map and this coaction is deliberately *not* a field: it is the conclusion of Lemma 25.5.3. -/
structure PrespectrumModTwoStableHurewicz
    (T : Prespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w}) where
  /-- The chosen source-facing dual Steenrod algebra owner on the fixed linear dual `A_*`. -/
  AStar : ModTwoSteenrodAlgebraDualAlgebra
  /-- The chosen total stable Hurewicz map in degree `n`. -/
  map :
    ∀ n : ℤ,
      Prespectrum.stableHomotopyGroup T n → homologyPresentation.HStar T
  /-- The specific coaction datum from Construction 25.4.9 paired with this stable Hurewicz
  map. -/
  sourceCoaction :
    PrespectrumModTwoSteenrodCoaction
      cohomologyPresentation cohomologyAction homologyPresentation
