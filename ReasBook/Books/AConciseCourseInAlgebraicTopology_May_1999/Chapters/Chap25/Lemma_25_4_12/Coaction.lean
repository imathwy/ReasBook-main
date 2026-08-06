import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_4_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_7.Milnor

open CategoryTheory
open scoped BigOperators TensorProduct

noncomputable section

universe u w uA uH uK

/-- Contract the right tensor factor against a chosen cohomology class.  When
`y = ∑_j a_j ⊗ x_j` and `x_j` is Kronecker-dual to `alphaPowers j`, applying this map to
`y` at `alphaPowers j` recovers the coefficient `a_j`. -/
def tensorRightKroneckerCoefficient
    {A : Type uA} {H : Type uH} {K : Type uK}
    [AddCommMonoid A] [Module (ZMod 2) A]
    [AddCommMonoid H] [Module (ZMod 2) H]
    [AddCommMonoid K] [Module (ZMod 2) K]
    (pairing : H →ₗ[(ZMod 2)] Module.Dual (ZMod 2) K)
    (phi : K) : A ⊗[(ZMod 2)] H →ₗ[(ZMod 2)] A :=
  (TensorProduct.rid (ZMod 2) A).toLinearMap.comp
    (TensorProduct.map LinearMap.id
      ((Module.Dual.eval (ZMod 2) K phi).comp pairing))

/-- The coefficient `a_{i,j}` in the source notation
`γ(x_i) = ∑_j a_{i,j} ⊗ x_j`, recovered invariantly by Kronecker contraction rather than
by choosing a tensor expansion. -/
def rpInfinityCoactionCoefficient
    {HStar KStar : Type u}
    [AddCommMonoid HStar] [Module (ZMod 2) HStar]
    [AddCommMonoid KStar] [Module (ZMod 2) KStar]
    (pairing : HStar →ₗ[(ZMod 2)] Module.Dual (ZMod 2) KStar)
    (coaction :
      HStar →ₗ[(ZMod 2)] modTwoSteenrodAlgebraGradedDual ⊗[(ZMod 2)] HStar)
    (generator : ℕ → HStar) (alphaPowers : ℕ → KStar)
    (i j : ℕ) : modTwoSteenrodAlgebraGradedDual :=
  tensorRightKroneckerCoefficient pairing (alphaPowers j) (coaction (generator i))

namespace PrespectrumModTwoSteenrodCoaction

variable {A : ModTwoSteenrodAlgebraDualMilnorPresentation}
variable {H2 : ModTwoCohomologyTheory}
variable {suspension : TopCat ⥤ TopCat}
variable {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
variable {Sq : SteenrodSquareFamily H2 suspension suspensionIso}
variable {normalizationData : StandardStiefelWhitneyNormalization H2}
variable {cohomologyAlgebra :
  CanonicalModTwoCohomologyAlgebra H2 (TopCat.of RealProjectiveInfinity)}
variable {cohomologyPresentation : PrespectrumModTwoCohomologyPresentation.{u, w}}
variable {cohomologyAction :
  PrespectrumModTwoSteenrodAction cohomologyPresentation}
variable {homologyPresentation : PrespectrumModTwoHomologyPresentation}

/-- A cohomology family `α^j` on a chosen prespectrum presentation of `RP^∞` realizes the source
setup used for Lemma 25.4.12: under the chosen comparison with canonical `H^*(RP^∞; ZMod 2)`,
the family agrees with the canonical powers `α^j`, the action of admissible Steenrod monomials
on `α = α^1` agrees with the canonical `RP^∞` calculation, and the chosen homology generators
`x_i` pair Kronecker-dually with the family `α^j`. -/
def IsRPInfinityModTwoCohomologyPowerFamily
    (coactionDatum :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (cohomologyAlgebra :
      CanonicalModTwoCohomologyAlgebra H2 (TopCat.of RealProjectiveInfinity))
    (presentationObject : Prespectrum.{u, w})
    (cohomologyComparison :
      cohomologyPresentation.HStar presentationObject ≃+
        modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity))
    (generator : ℕ → homologyPresentation.HStar presentationObject)
    (alphaPowers : ℕ → cohomologyPresentation.HStar presentationObject) : Prop :=
  (∀ j : ℕ,
      cohomologyComparison (alphaPowers j) =
        cohomologyAlgebra.rpInfinityGeneratorPower normalizationData j) ∧
    (∀ I : AdmissibleSteenrodMonomialIndex,
      cohomologyComparison
          (cohomologyAction.actionHom presentationObject
            (admissibleSteenrodMonomial I) (alphaPowers 1)) =
        rpInfinityGeneratorAdmissibleSteenrodMonomial Sq normalizationData I) ∧
      ∀ i j : ℕ,
        coactionDatum.kroneckerPairing presentationObject (generator i) (alphaPowers j) =
          if i = j then 1 else 0

/-- `IsRPInfinityModTwoCohomologyPowerFamily` is exactly the `RP^∞` comparison and Kronecker
duality data used in the source setup for Lemma 25.4.12. -/
@[simp] theorem isRPInfinityModTwoCohomologyPowerFamily_iff
    (coactionDatum :
      PrespectrumModTwoSteenrodCoaction
        cohomologyPresentation cohomologyAction homologyPresentation)
    (presentationObject : Prespectrum.{u, w})
    (cohomologyComparison :
      cohomologyPresentation.HStar presentationObject ≃+
        modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity))
    (generator : ℕ → homologyPresentation.HStar presentationObject)
    (alphaPowers : ℕ → cohomologyPresentation.HStar presentationObject) :
    coactionDatum.IsRPInfinityModTwoCohomologyPowerFamily
        Sq normalizationData cohomologyAlgebra
        presentationObject cohomologyComparison generator alphaPowers ↔
      (∀ j : ℕ,
          cohomologyComparison (alphaPowers j) =
            cohomologyAlgebra.rpInfinityGeneratorPower normalizationData j) ∧
        (∀ I : AdmissibleSteenrodMonomialIndex,
          cohomologyComparison
              (cohomologyAction.actionHom presentationObject
                (admissibleSteenrodMonomial I) (alphaPowers 1)) =
            rpInfinityGeneratorAdmissibleSteenrodMonomial Sq normalizationData I) ∧
        ∀ i j : ℕ,
          coactionDatum.kroneckerPairing presentationObject (generator i) (alphaPowers j) =
            if i = j then 1 else 0 :=
  Iff.rfl

/-- Under the Lemma 25.4.8 generator setup on a chosen `RP^∞` presentation, contraction against
`α = α¹` computes the coefficient `a_{i,1}` in
`γ(x_i) = ∑_j a_{i,j} ⊗ x_j`: it is `ξ_r` when `i = 2^r` and is zero otherwise. -/
theorem rpInfinity_spec
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
      presentationObject cohomologyComparison generator alphaPowers) :
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
  sorry

end PrespectrumModTwoSteenrodCoaction
