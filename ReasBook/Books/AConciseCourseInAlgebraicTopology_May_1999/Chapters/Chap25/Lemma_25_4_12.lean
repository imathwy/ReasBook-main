import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_12.Coaction

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u w

-- The reusable `RP^∞` coaction API for Lemma 25.4.12 lives in the item-local foundation module
-- `Lemma_25_4_12.Coaction`, so later files can import that API directly without importing this
-- labeled theorem file.

namespace PrespectrumModTwoSteenrodCoaction

variable {H2 : ModTwoCohomologyTheory}
variable {suspension : TopCat ⥤ TopCat}
variable {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}

/-- Lemma 25.4.12. Write the coaction as
`γ(x_i) = ∑_j a_{i,j} ⊗ x_j`. Under the Lemma 25.4.8 `RP^∞` generator setup, the
coefficient `a_{i,1}` is `ξ_r` when `i = 2^r` for some `r ≥ 1`, and is zero otherwise.
The coefficient is expressed invariantly by contraction against the Kronecker-dual class `α`. -/
theorem rpInfinity_coaction_x_one_coefficient
    (A : ModTwoSteenrodAlgebraDualMilnorPresentation)
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (cohomologyAlgebra :
      CanonicalModTwoCohomologyAlgebra H2 (TopCat.of RealProjectiveInfinity))
    (cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w})
    (cohomologyAction :
      PrespectrumModTwoSteenrodAction cohomologyPresentation)
    (homologyPresentation : PrespectrumModTwoHomologyPresentation)
    (coactionDatum :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (presentationObject : Prespectrum.{u, w})
    (cohomologyComparison :
      cohomologyPresentation.HStar presentationObject ≃+
        modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity))
    (generator : ℕ → homologyPresentation.HStar presentationObject)
    (alphaPowers : ℕ → cohomologyPresentation.HStar presentationObject)
    (h_setup : coactionDatum.IsRPInfinityModTwoCohomologyPowerFamily
      Sq normalizationData cohomologyAlgebra
      presentationObject cohomologyComparison generator alphaPowers)
    :
    (∀ r : ℕ+,
      rpInfinityCoactionCoefficient
          (coactionDatum.kroneckerPairing presentationObject)
          (coactionDatum.gamma presentationObject) generator alphaPowers
          (2 ^ (r : ℕ)) 1 =
        A.generators r) ∧
      ∀ i : ℕ,
        (∀ r : ℕ+, i ≠ 2 ^ (r : ℕ)) →
          rpInfinityCoactionCoefficient
              (coactionDatum.kroneckerPairing presentationObject)
              (coactionDatum.gamma presentationObject) generator alphaPowers i 1 = 0 := by
  exact coactionDatum.rpInfinity_spec
    presentationObject cohomologyComparison generator alphaPowers h_setup

end PrespectrumModTwoSteenrodCoaction
