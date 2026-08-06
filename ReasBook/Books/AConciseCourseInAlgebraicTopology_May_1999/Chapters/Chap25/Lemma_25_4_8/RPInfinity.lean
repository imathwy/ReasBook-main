import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_5

open CategoryTheory

noncomputable section

/-- The distinguished degree-`1` class `α` on `RP^∞`, viewed in the fixed total mod-`2`
cohomology object `H^*(RP^∞; ZMod 2)`. -/
abbrev rpInfinityGenerator
    {H2 : ModTwoCohomologyTheory}
    (normalizationData : StandardStiefelWhitneyNormalization H2) :
    modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity) :=
  DirectSum.lof ℤ ℕ
    (fun n ↦ modTwoCohomologyGroup H2 n (TopCat.of RealProjectiveInfinity))
    1 normalizationData.degreeOneGenerator

/-- Expanding `rpInfinityGenerator` recovers the direct-sum realization of the degree-`1`
generator on `RP^∞`. -/
@[simp] theorem rpInfinityGenerator_def
    {H2 : ModTwoCohomologyTheory}
    (normalizationData : StandardStiefelWhitneyNormalization H2) :
    rpInfinityGenerator normalizationData =
      DirectSum.lof ℤ ℕ
        (fun n ↦ modTwoCohomologyGroup H2 n (TopCat.of RealProjectiveInfinity))
        1 normalizationData.degreeOneGenerator :=
  rfl

/-- The total-cohomology class obtained by applying the Steenrod operation `Sq^I` to the
distinguished degree-`1` class `α` on `RP^∞` and inserting the result into the homogeneous
summand of degree `1 + I.sum`. -/
abbrev rpInfinityGeneratorSteenrodMonomial
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (I : SteenrodMultiIndex) :
    modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity) :=
  DirectSum.lof ℤ ℕ
    (fun n ↦ modTwoCohomologyGroup H2 n (TopCat.of RealProjectiveInfinity))
    (1 + I.sum)
    (SteenrodSquareFamily.applyMultiIndex Sq.sq 1 I normalizationData.degreeOneGenerator)

/-- Expanding `rpInfinityGeneratorSteenrodMonomial` recovers the direct-sum insertion of `Sq^I α`
on `RP^∞`. -/
@[simp] theorem rpInfinityGeneratorSteenrodMonomial_def
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (I : SteenrodMultiIndex) :
    rpInfinityGeneratorSteenrodMonomial Sq normalizationData I =
      DirectSum.lof ℤ ℕ
        (fun n ↦ modTwoCohomologyGroup H2 n (TopCat.of RealProjectiveInfinity))
        (1 + I.sum)
        (SteenrodSquareFamily.applyMultiIndex Sq.sq 1 I normalizationData.degreeOneGenerator) :=
  rfl

/-- The total-cohomology class obtained by applying the admissible Steenrod basis operation
indexed by `I` to the distinguished degree-`1` class `α` on `RP^∞`. -/
abbrev rpInfinityGeneratorAdmissibleSteenrodMonomial
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (I : AdmissibleSteenrodMonomialIndex) :
    modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity) :=
  rpInfinityGeneratorSteenrodMonomial Sq normalizationData I.1

/-- Expanding `rpInfinityGeneratorAdmissibleSteenrodMonomial` recovers the corresponding
`Sq^I α` insertion in `H^*(RP^∞; ZMod 2)`. -/
@[simp] theorem rpInfinityGeneratorAdmissibleSteenrodMonomial_def
    {H2 : ModTwoCohomologyTheory}
    {suspension : TopCat ⥤ TopCat}
    {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (I : AdmissibleSteenrodMonomialIndex) :
    rpInfinityGeneratorAdmissibleSteenrodMonomial Sq normalizationData I =
      rpInfinityGeneratorSteenrodMonomial Sq normalizationData I.1 :=
  rfl

namespace CanonicalModTwoCohomologyAlgebra

/-- The power `α^n` of the distinguished degree-`1` class on `RP^∞`, expressed in the chosen
canonical total mod-`2` cohomology algebra carried by `A`. -/
abbrev rpInfinityGeneratorPower
    {H2 : ModTwoCohomologyTheory}
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of RealProjectiveInfinity))
    (normalizationData : StandardStiefelWhitneyNormalization H2) (n : ℕ) :
    modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity) :=
  let _ : CommRing (modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity)) := A.toCommRing
  rpInfinityGenerator normalizationData ^ n

/-- Expanding `CanonicalModTwoCohomologyAlgebra.rpInfinityGeneratorPower` recovers the ordinary
power `α^n` in the chosen canonical total mod-`2` cohomology algebra. -/
@[simp] theorem rpInfinityGeneratorPower_def
    {H2 : ModTwoCohomologyTheory}
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of RealProjectiveInfinity))
    (normalizationData : StandardStiefelWhitneyNormalization H2) (n : ℕ) :
    A.rpInfinityGeneratorPower normalizationData n =
      let _ : CommRing (modTwoCohomologyStar H2 (TopCat.of RealProjectiveInfinity)) := A.toCommRing
      rpInfinityGenerator normalizationData ^ n :=
  rfl

end CanonicalModTwoCohomologyAlgebra
