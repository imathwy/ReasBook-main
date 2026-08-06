import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_5_2

noncomputable section

universe u w

section ThomComparison

variable
    (TO : RingPrespectrum.{u, w})
    (stableHomotopyRing : StableHomotopyGradedRing TO)
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    [Ring (homologyPresentation.HStar TO.toPrespectrum)]
    [Algebra (ZMod 2) (homologyPresentation.HStar TO.toPrespectrum)]
    (stableHurewicz :
      PrespectrumModTwoStableHurewicz
        TO.toPrespectrum
        cohomologyPresentation
        cohomologyAction
        homologyPresentation)
    (presentationEquiv :
      RingPrespectrumModTwoHomologyPolynomialEquiv
        TO
        (homologyPresentation.homologyPresentation TO.toPrespectrum)
        homologyPresentation.sphereZero)
    (A : ThomUnorientedCobordismPolynomialAlgebra)

include stableHomotopyRing presentationEquiv A

/-- Theorem 25.5.4 (1). For the Chapter 25 comparison map attached to a chosen polynomial
presentation `Ψ` of `H_*(TO)`, the stable Hurewicz map `h : π_*(TO) → H_*(TO)` is injective on
each nonnegative degree. -/
theorem stableHurewicz_injective
    (n : ℕ) :
    Function.Injective (stableHurewicz.map (n : ℤ)) := by
  intro x y hxy
  have hbij :=
    thomComparisonCompositeAddHom_bijective
      TO
      cohomologyPresentation
      cohomologyAction
      homologyPresentation
      stableHurewicz
      presentationEquiv
      A
      stableHomotopyRing
  have hclass :
      TO.piStarClass n x = TO.piStarClass n y := by
    apply hbij.injective
    simp [hxy]
  exact TO.piStarClass_injective n hclass

/-- Theorem 25.5.4 (2). For the Chapter 25 comparison algebra homomorphism
`g : H_*(TO) → N_*` attached to a chosen polynomial presentation `Ψ` of `H_*(TO)`, the composite
`g ∘ h` identifies `π_*(TO)` with `N_*` on the nonnegative stable homotopy object through the
named additive homomorphism `thomComparisonCompositeAddHom`. -/
theorem stableHurewicz_composite_identifies_with_nStar
    :
    Function.Bijective
      (thomComparisonCompositeAddHom
        TO
        cohomologyPresentation
        cohomologyAction
        homologyPresentation
        stableHurewicz
        presentationEquiv
        A) := by
  exact thomComparisonCompositeAddHom_bijective
    TO
    cohomologyPresentation
    cohomologyAction
    homologyPresentation
    stableHurewicz
    presentationEquiv
    A
    stableHomotopyRing

end ThomComparison
