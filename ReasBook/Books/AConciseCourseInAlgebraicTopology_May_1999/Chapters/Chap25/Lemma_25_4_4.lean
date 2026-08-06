import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Lemma_25_4_3

open CategoryTheory
open scoped DirectSum

noncomputable section

-- Chapter 25 uses the canonical prespectrum cohomology owner
-- `presentation.HStar hz2 = H^*(HZ_2)` from Lemma 25.4.3. The `HZ_2`-specific input here is the
-- stagewise `K(ZMod 2, n + 1)` hypothesis on the chosen prespectrum model, and the stagewise
-- polynomial description is reused directly from Theorem 22.5.6 rather than repackaged as a new
-- `...Model`/`...Presentation` owner.

/-- Each positive stage of an `HZ_2` prespectrum model is a `K(ZMod 2, q)` space, so the stagewise
mod-`2` cohomology polynomial presentation from Theorem 22.5.6 applies directly to that stage. -/
theorem hz2Stage_modTwoCohomology_isPolynomial
    (H2 : ModTwoCohomologyTheory)
    {suspension : TopCat ⥤ TopCat}
    (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q)
    (Sq : SteenrodSquareFamily H2 suspension suspensionIso)
    (hz2 : Prespectrum.{0, 0})
    (stageIsKZ2 : ∀ n : ℕ, IsAdditiveEilenbergMacLaneSpace (ZMod 2) n (hz2.basedSpace n))
    (q : ℕ+) :
    ∃ (A : CanonicalModTwoCohomologyAlgebra H2 (hz2.basedSpace q.natPred).right)
      (fundamentalClass :
        modTwoCohomologyGroup H2 (q.natPred + 1) (hz2.basedSpace q.natPred).right)
      (algEquiv :
        eilenbergMacLaneModTwoPolynomialEquiv
          H2 q.natPred (hz2.basedSpace q.natPred).right A),
      IsFundamentalClassForAdditiveEilenbergMacLaneSpace
          H2 q.natPred (hz2.basedSpace q.natPred) fundamentalClass ∧
        IsEilenbergMacLaneModTwoPolynomialPresentationOn
          H2 Sq q.natPred (hz2.basedSpace q.natPred).right A fundamentalClass algEquiv := by
  simpa using
    eilenbergMacLaneModTwoCohomology_isPolynomial
      H2 suspensionIso Sq q (hz2.basedSpace q.natPred) (stageIsKZ2 q.natPred)

/-- The degree-`n` cohomology group at the `k`th stage used to form
`H^n(HZ₂) = lim←_k H^(n+k+1)(K(ZMod 2, k+1))`. -/
abbrev hz2StageCohomologyGroup
    (H2 : ModTwoCohomologyTheory) (hz2 : Prespectrum.{0, 0})
    (n k : ℕ) : Type :=
  modTwoCohomologyGroup H2 (n + k + 1) (hz2.basedSpace k).right

/-- The bonding map
`H^(n+k+2)(HZ₂_(k+1)) → H^(n+k+1)(HZ₂_k)` induced by the `k`th prespectrum
structure map and the suspension isomorphism in mod-`2` cohomology. -/
noncomputable def hz2StageCohomologyBonding
    (H2 : ModTwoCohomologyTheory)
    (suspension : TopCat ⥤ TopCat)
    (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q)
    (hz2 : Prespectrum.{0, 0})
    (stageSuspensionIso : ∀ k : ℕ,
      suspension.obj (hz2.basedSpace k).right ≅
        (PointedCompactlyGenerated.toBasedSpace (Σ (hz2 k))).right)
    (n k : ℕ) :
    modTwoCohomologyGroup H2 (n + k + 1 + 1) (hz2.basedSpace (k + 1)).right →+
      hz2StageCohomologyGroup H2 hz2 n k :=
  ((H2.cohomology (n + k + 1 + 1)).map
        ((stageSuspensionIso k).hom ≫
          (PointedCompactlyGenerated.toBasedSpaceMap (hz2.structureMap k)).right).op ≫
      (suspensionIso (n + k + 1)).hom.app (Opposite.op (hz2.basedSpace k).right)).hom

/-- The inverse limit of the stage groups defining degree-`n` cohomology of the
Eilenberg--Mac Lane prespectrum. Its elements are precisely the families compatible with the
bonding maps induced by the prespectrum structure maps. -/
def hz2StageCohomologyInverseLimit
    (H2 : ModTwoCohomologyTheory)
    (suspension : TopCat ⥤ TopCat)
    (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q)
    (hz2 : Prespectrum.{0, 0})
    (stageSuspensionIso : ∀ k : ℕ,
      suspension.obj (hz2.basedSpace k).right ≅
        (PointedCompactlyGenerated.toBasedSpace (Σ (hz2 k))).right)
    (n : ℕ) :
    AddSubgroup (∀ k : ℕ, hz2StageCohomologyGroup H2 hz2 n k) where
  carrier := {x | ∀ k : ℕ,
    hz2StageCohomologyBonding H2 suspension suspensionIso hz2 stageSuspensionIso n k
        (x (k + 1)) =
      x k}
  zero_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry

/-- The nonnegative total stage-limit cohomology of the chosen `HZ₂` prespectrum model. -/
abbrev hz2StageLimitCohomology
    (H2 : ModTwoCohomologyTheory)
    (suspension : TopCat ⥤ TopCat)
    (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q)
    (hz2 : Prespectrum.{0, 0})
    (stageSuspensionIso : ∀ k : ℕ,
      suspension.obj (hz2.basedSpace k).right ≅
        (PointedCompactlyGenerated.toBasedSpace (Σ (hz2 k))).right) : Type :=
  ⨁ n : ℕ,
    hz2StageCohomologyInverseLimit
      H2 suspension suspensionIso hz2 stageSuspensionIso n

/-- A prespectrum cohomology presentation represents `H^*(HZ₂)` when its total cohomology
is additively equivalent to the direct sum of the canonical stagewise inverse limits. This is the
non-circular compatibility condition used by the passage-to-limits argument in May. -/
def PrespectrumModTwoCohomologyPresentation.IsHZ2StageLimit
    (presentation : PrespectrumModTwoCohomologyPresentation.{0, 0})
    (H2 : ModTwoCohomologyTheory)
    (suspension : TopCat ⥤ TopCat)
    (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q)
    (hz2 : Prespectrum.{0, 0})
    (stageSuspensionIso : ∀ k : ℕ,
      suspension.obj (hz2.basedSpace k).right ≅
        (PointedCompactlyGenerated.toBasedSpace (Σ (hz2 k))).right) : Prop :=
  Nonempty
    (hz2StageLimitCohomology
        H2 suspension suspensionIso hz2 stageSuspensionIso ≃+
      presentation.HStar hz2)

/-- The `ZMod 2`-linear comparison type `A ≃ presentation.HStar hz2` for a stage-limit
presentation of `H^*(HZ₂)`. -/
abbrev HZ2CohomologyComparison
    (presentation : PrespectrumModTwoCohomologyPresentation.{0, 0})
    (hz2 : Prespectrum.{0, 0}) : Type _ :=
  ModTwoSteenrodAlgebra ≃ₗ[(ZMod 2)] presentation.HStar hz2

namespace HZ2CohomologyComparison

/-- Lemma 25.4.4. If `hz2` is the Eilenberg--Mac Lane prespectrum with stages
`K(ZMod 2, k + 1)`, then the passage to the inverse limits of the stage cohomology groups gives a
`ZMod 2`-linear isomorphism `A ≃ H^*(HZ₂)`. The admissible-basis assertion belongs to the
following Theorem 25.4.5 and is deliberately not included here. -/
theorem steenrodAlgebra_linearEquiv
    (H2 : ModTwoCohomologyTheory)
    (suspension : TopCat ⥤ TopCat)
    (suspensionIso : ∀ q : ℕ, suspension.op ⋙ H2.cohomology (q + 1) ≅ H2.cohomology q)
    (presentation : PrespectrumModTwoCohomologyPresentation.{0, 0})
    (hz2 : Prespectrum.{0, 0})
    (stageSuspensionIso : ∀ k : ℕ,
      suspension.obj (hz2.basedSpace k).right ≅
        (PointedCompactlyGenerated.toBasedSpace (Σ (hz2 k))).right)
    (stageIsKZ2 : ∀ n : ℕ, IsAdditiveEilenbergMacLaneSpace (ZMod 2) n (hz2.basedSpace n))
    (hPresentation : presentation.IsHZ2StageLimit
      H2 suspension suspensionIso hz2 stageSuspensionIso) :
    Nonempty (HZ2CohomologyComparison presentation hz2) := by
  sorry

end HZ2CohomologyComparison
