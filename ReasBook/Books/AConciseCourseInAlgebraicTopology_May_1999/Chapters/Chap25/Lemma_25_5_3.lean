import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_5_3.StableHurewicz

universe u w

-- The reusable source-facing stable-Hurewicz owner and primitive-image predicate live in the
-- item-local foundation module `Lemma_25_5_3.StableHurewicz`, so later files can import that
-- API directly without importing this labeled lemma file.

/-- Lemma 25.5.3. For `x ∈ π_*(T)`, the coaction satisfies `γ(h(x)) = 1 ⊗ h(x)`. Here
the packaged owner
`stableHurewicz : PrespectrumModTwoStableHurewicz
  T cohomologyPresentation cohomologyAction homologyPresentation`
stores the chosen stable Hurewicz map `π_*(T) → H_*(T)`, the dual Steenrod algebra owner
`AStar : ModTwoSteenrodAlgebraDualAlgebra`, and the coaction datum from Construction 25.4.9.
The primitive-image equality is the conclusion, not an assumption stored in that owner.
-/
theorem coaction_stableHurewicz_eq_unit_tmul
    (T : Prespectrum.{u, w})
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation.{u, w})
    (stableHurewicz :
      PrespectrumModTwoStableHurewicz
        T cohomologyPresentation cohomologyAction homologyPresentation)
    :
    prespectrumModTwoStableHurewiczPrimitiveImage
      T cohomologyPresentation cohomologyAction homologyPresentation
      stableHurewicz.AStar stableHurewicz.map stableHurewicz.sourceCoaction :=
  by
    sorry
