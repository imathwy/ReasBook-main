import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Lemma_20_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Corollary_25_3_7

open scoped ContinuousMap DirectSum

noncomputable section

-- Chapter 23 fixes the Thom-space owner for the tautological real line bundle over
-- `RealProjectiveInfinity`, and Corollary 25.3.7 packages the comparison
-- `Φ(a_i) = b_i` between `H_*(TO)` and `H_*(BO)`.

/-- The degree-shifting Thom homology map from `H_(i+1)(T(γ₁))` into the degree-`i` summand of
`H_*(BO; ZMod 2)`.  The shift by one is essential: `TO(1)` contributes
`H_(i+1)(TO(1))` to stable degree `i`. -/
abbrev universalLineBundleThomToBOGeneratorImage
    {H2 : ModTwoCohomologyTheory}
    (normalizationData : StiefelWhitneyNormalization H2)
    [TopologicalSpace (universalLineBundleThomSpace normalizationData)]
    {BO : Type} [TopologicalSpace BO]
    (thomIsomorphism :
      ∀ i : ℕ,
        rSingularHomology
            (ZMod 2) (i + 1)
            (TopCat.of (universalLineBundleThomSpace normalizationData)) →
          rSingularHomology (ZMod 2) i (TopCat.of BO))
    (i : ℕ) :
    rSingularHomology
        (ZMod 2) (i + 1)
        (TopCat.of (universalLineBundleThomSpace normalizationData)) →
      boModTwoHomology BO :=
  fun y ↦
    DirectSum.lof ℤ ℕ
      (fun n ↦ rSingularHomology (ZMod 2) n (TopCat.of BO))
      i
      (thomIsomorphism i y)

/-- The corresponding stable degree-`i` map from `H_(i+1)(T(γ₁))` into `H_*(TO)`, obtained from
the compatible Thom isomorphism and `Φ.symm`. -/
abbrev universalLineBundleThomToThomPrespectrumGeneratorImage
    {H2 : ModTwoCohomologyTheory}
    (normalizationData : StiefelWhitneyNormalization H2)
    [TopologicalSpace (universalLineBundleThomSpace normalizationData)]
    {BO : Type} [TopologicalSpace BO]
    (BOPoly : BOHomologyPolynomialAlgebra BO)
    (TO : RingPrespectrum)
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing]
    (thomIsomorphism :
      ∀ i : ℕ,
        rSingularHomology
            (ZMod 2) (i + 1)
            (TopCat.of (universalLineBundleThomSpace normalizationData)) →
          rSingularHomology (ZMod 2) i (TopCat.of BO))
    (Φ : ThomHomologyPolynomialAlgEquiv BO BOPoly TO toPresentation sphereZeroModel)
    (i : ℕ) :
    rSingularHomology
        (ZMod 2) (i + 1)
        (TopCat.of (universalLineBundleThomSpace normalizationData)) →
      ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel :=
  letI := BOPoly.toCommRing
  letI := BOPoly.toAlgebra
  fun y ↦
    Φ.symm
      (universalLineBundleThomToBOGeneratorImage
        normalizationData thomIsomorphism i y)

/-- Corollary 25.3.8. Under the compatible Thom isomorphisms for `BO(1)` and `BO`, the canonical
homotopy equivalence `j : RP^∞ → T(γ₁)` sends `x_(i+1)` to the class entering stable degree `i`:
it maps to `a_i` for `i ≥ 1`, and `x_1` maps to the unit `a_0 = 1`.  The hypotheses below name
the preceding compatibility square on the `BO` side; they do not assume that the `a_i` already
lift from `TO(1)`. -/
theorem thomPrespectrumPolynomial_generators_lift_from_universal_line_bundle
    {H2 : ModTwoCohomologyTheory}
    (normalizationData : StiefelWhitneyNormalization H2)
    [TopologicalSpace (universalLineBundleThomSpace normalizationData)]
    {BO : Type} [TopologicalSpace BO]
    (TO : RingPrespectrum)
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    [toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)]
    [toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing]
    (BOPoly : BOHomologyPolynomialAlgebra BO)
    (Φ : ThomHomologyPolynomialAlgEquiv BO BOPoly TO toPresentation sphereZeroModel)
    (j : TopCat.of RealProjectiveInfinity ≃ₕ
      universalLineBundleThomSpace normalizationData)
    (x : ∀ n : ℕ,
      rSingularHomology (ZMod 2) n (TopCat.of RealProjectiveInfinity))
    (hGenerator : ∀ n : ℕ, 0 < n → x n ≠ 0 ∧ ∀ y, y ≠ 0 → y = x n)
    (thomIsomorphism :
      ∀ i : ℕ,
        rSingularHomology
            (ZMod 2) (i + 1)
            (TopCat.of (universalLineBundleThomSpace normalizationData)) →
          rSingularHomology (ZMod 2) i (TopCat.of BO))
    (a : BOHomologyGeneratorIndex →
      ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)
    (hMapGenerators : ∀ i, Φ (a i) = BOPoly.generators i)
    (hThomZero :
      universalLineBundleThomToBOGeneratorImage
          normalizationData thomIsomorphism 0
          ((rSingularHomologyMap (ZMod 2) 1 (TopCat.ofHom j.toFun)) (x 1)) =
        BOPoly.toCommRing.one)
    (hThomGenerators :
      ∀ i : BOHomologyGeneratorIndex,
        universalLineBundleThomToBOGeneratorImage
            normalizationData thomIsomorphism (i : ℕ)
            ((rSingularHomologyMap (ZMod 2) ((i : ℕ) + 1) (TopCat.ofHom j.toFun))
              (x ((i : ℕ) + 1))) =
          BOPoly.generators i) :
    universalLineBundleThomToThomPrespectrumGeneratorImage
        normalizationData BOPoly TO toPresentation sphereZeroModel thomIsomorphism Φ 0
        ((rSingularHomologyMap (ZMod 2) 1 (TopCat.ofHom j.toFun)) (x 1)) =
      (1 : ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel) ∧
    ∀ i : BOHomologyGeneratorIndex,
      universalLineBundleThomToThomPrespectrumGeneratorImage
          normalizationData BOPoly TO toPresentation sphereZeroModel thomIsomorphism Φ (i : ℕ)
          ((rSingularHomologyMap (ZMod 2) ((i : ℕ) + 1) (TopCat.ofHom j.toFun))
            (x ((i : ℕ) + 1))) =
        a i := by
  sorry
