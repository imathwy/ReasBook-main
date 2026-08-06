import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_8.RPInfinity
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_4_7.Milnor

open CategoryTheory

noncomputable section

variable {H2 : ModTwoCohomologyTheory}
variable {suspension : TopCat ⥤ TopCat}
variable {suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q}

-- Semantic recall via `lean_leansearch` surfaced no verified upstream owner for the action of
-- admissible Steenrod monomials on `H^*(RP^∞; ZMod 2)`. This file therefore reuses the local
-- Chapter 22/23/25 owners `SteenrodSquareFamily`,
-- `StandardStiefelWhitneyNormalization`, and the Milnor special admissible multiindices from
-- Theorem 25.4.7.

/-- Lemma 25.4.8 (1): for the distinguished generator `α` on `RP^∞`, the special admissible
Steenrod operation indexed by `[2^(r - 1), 2^(r - 2), ..., 2, 1]` sends `α` to `α ^ (2 ^ r)` in
any chosen canonical total mod-`2` cohomology ring of `RP^∞`. -/
theorem milnorSpecialAdmissibleSteenrodMonomial_apply_rpInfinityGenerator
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of RealProjectiveInfinity))
    (r : ℕ+) :
    rpInfinityGeneratorAdmissibleSteenrodMonomial Sq normalizationData
      (milnorSpecialAdmissibleSteenrodMonomial r) =
      A.rpInfinityGeneratorPower normalizationData (2 ^ (r : ℕ)) := sorry

/-- Lemma 25.4.8 (2): every other positive-degree admissible basis operation acts trivially on
the distinguished generator `α` of `H^1(RP^∞; ZMod 2)`, viewed inside
`H^*(RP^∞; ZMod 2)`. -/
theorem otherAdmissibleSteenrodMonomial_apply_rpInfinityGenerator_eq_zero
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (I : AdmissibleSteenrodMonomialIndex)
    (hIpos : 0 < I.1.sum)
    (hInonspecial :
      ∀ r : ℕ+,
        I ≠ milnorSpecialAdmissibleSteenrodMonomial r) :
    rpInfinityGeneratorAdmissibleSteenrodMonomial Sq normalizationData I = 0 := sorry

/-- Companion form of Lemma 25.4.8 (2): the underlying degree-`1 + I.sum` cohomology class
`Sq^I α` vanishes for every positive-degree admissible basis operation other than the Milnor
special ones. -/
theorem otherAdmissibleSteenrodMonomial_apply_degreeOneGenerator_eq_zero
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (normalizationData : StandardStiefelWhitneyNormalization H2)
    (I : AdmissibleSteenrodMonomialIndex)
    (hIpos : 0 < I.1.sum)
    (hInonspecial :
      ∀ r : ℕ+,
        I ≠ milnorSpecialAdmissibleSteenrodMonomial r) :
    SteenrodSquareFamily.applyMultiIndex Sq.sq 1 I.1
      normalizationData.degreeOneGenerator = 0 := sorry
