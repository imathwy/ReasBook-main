import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_3_4

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: `CategoryTheory.Abelian.Ext.contravariantSequence_exact`
-- and `CategoryTheory.ShortComplex.Splitting.shortExact` are the canonical mathlib interfaces
-- behind the cohomological universal-coefficient argument. The current Chapter 17 API already
-- packages the resulting short exact sequence by `UniversalCoefficientCohomologySequence`.

/-- Proof step 17.4.3. For cohomology, after applying `Hom(-, M)` to the split short exact
sequences from Construction 17.4.1 and identifying the resulting extension term with
`Ext¹_R(H_(n - 1)(X), M)`, one obtains a short exact sequence
`0 ⟶ universalCoefficientExtTerm R X M n ⟶ universalCoefficientCohomologyTerm R X M n ⟶
universalCoefficientHomTerm R X M n ⟶ 0`. In the current Chapter 17 API this is packaged as
`UniversalCoefficientCohomologySequence R X M n`, and is the fixed-coefficient specialization of
`universalCoefficientCohomologyShortExact`. -/
theorem universalCoefficientCohomologySequenceOfSplitCycleBoundary
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (hX : ∀ i : ℤ, Module.Free R (X.X i)) :
    Nonempty (UniversalCoefficientCohomologySequence R X M n) := by
  rcases universalCoefficientCohomologyShortExact R X n hX with ⟨S⟩
  exact ⟨S M⟩
