import Mathlib.Algebra.Algebra.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_3_6

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u v w

/-- The total mod-`2` homology object `H_*(TO)` attached to a chosen ring prespectrum `TO`,
presented by connective reduced homology and a chosen based CW model of `S⁰`. -/
abbrev ringPrespectrumModTwoHomology
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex) : Type _ :=
  ⨁ n : ℕ,
    ((connectivePrespectrumReducedHomology TO.toPrespectrum toPresentation) (n : ℤ)).obj
      sphereZeroModel

/-- Unfolding `ringPrespectrumModTwoHomology` recovers the direct sum of the degreewise reduced
mod-`2` homology groups used to present `H_*(TO)`. -/
theorem ringPrespectrumModTwoHomology_def
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex) :
    ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel =
      ⨁ n : ℕ,
        ((connectivePrespectrumReducedHomology TO.toPrespectrum toPresentation) (n : ℤ)).obj
          sphereZeroModel := rfl

/-- A `ZMod 2`-algebra structure on the fixed total homology object `H_*(TO)` for a chosen ring
structure. -/
abbrev RingPrespectrumModTwoHomologyModTwoAlgebra
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    (toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)) :=
  letI := toTOHomologyRing
  Algebra (ZMod 2) (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)

/-- The additive commutative group underlying a candidate ring structure on `H_*(TO)` agrees with
the canonical direct-sum additive commutative group. -/
def RingPrespectrumModTwoHomologyAdditiveCompatibility
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    (toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)) :
    Prop :=
  let existingAddCommGroup :
      AddCommGroup (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel) :=
    inferInstance
  letI := toTOHomologyRing
  (inferInstance :
      AddCommGroup (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel)) =
    existingAddCommGroup

/-- A Thom `ZMod 2`-algebra equivalence from the chosen total homology object `H_*(TO)` of a ring
prespectrum `TO` to the fixed total mod-`2` homology object `H_*(BO)`. -/
abbrev ThomHomologyAlgEquiv
    (BO : Type) [TopologicalSpace BO]
    (TO : RingPrespectrum.{u, w})
    (toPresentation : ConnectivePrespectrumReducedHomologyPresentation TO.toPrespectrum)
    (sphereZeroModel : BasedCWComplex)
    (toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel))
    (toTOHomologyAlgebra :
      RingPrespectrumModTwoHomologyModTwoAlgebra
        TO toPresentation sphereZeroModel toTOHomologyRing)
    (toBOHomologyCommRing : CommRing (boModTwoHomology BO))
    (toBOHomologyAlgebra : BOHomologyModTwoAlgebra BO toBOHomologyCommRing) :=
  letI := toTOHomologyRing
  letI := toTOHomologyAlgebra
  letI := toBOHomologyCommRing
  letI := toBOHomologyAlgebra
  ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel ≃ₐ[ZMod 2] boModTwoHomology BO

-- Semantic recall via `lean_leansearch` surfaced only generic `AlgEquiv` APIs. Repo inspection
-- shows that Construction 25.3.4 already fixes the Thom ring-prespectrum owner
-- `TO_ringPrespectrum`. Since the current project has no separate owner for the assembled total
-- Thom homology map `Φ`, this file records the source statement as existence of compatible
-- `ZMod 2`-algebra structures on `H_*(TO)` and `H_*(BO)` together with a Thom algebra
-- equivalence between them.

/-- Proposition 25.3.5. For the Thom ring prespectrum `TO` assembled in Construction 25.3.4 from
the finite-stage universal bundles `γ n` over a stagewise model `BO(n)` of the stable real
classifying space `BO`, there exists a Thom isomorphism
`Φ : H_*(TO) → H_*(BO)` that is an isomorphism of `ZMod 2`-algebras. -/
theorem thom_homology_algEquiv_exists
    (BO : Type) [TopologicalSpace BO]
    (BOStage : ℕ → Type)
    [∀ n, TopologicalSpace (BOStage n)]
    (γ : ∀ n : ℕ, BOStage n → Type)
    [∀ n, TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) (γ n))]
    [∀ n, (b : BOStage n) → TopologicalSpace (γ n b)]
    [∀ n, FiberBundle (Fin n → ℝ) (γ n)]
    [∀ n, (b : BOStage n) → AddCommGroup (γ n b)]
    [∀ n, (b : BOStage n) → Module ℝ (γ n b)]
    [∀ n, RealPlaneBundleClassifyingSpace n (BOStage n) (γ n)]
    [TOStagewiseNormedBundle BOStage γ]
    (bInf : ∀ n : ℕ, BOStage n)
    (structureMap :
      ∀ n : ℕ,
        reducedSuspension
            (TOPointedCompactlyGenerated
              BOStage
              γ
              bInf n) ⟶
          TOPointedCompactlyGenerated
            BOStage
            γ
            bInf (n + 1))
    (unit :
      sphereZero ⟶ (TO_prespectrum BOStage γ bInf structureMap).basedSpace 0)
    (mul :
      ∀ m n : ℕ,
        smashProduct
            ((TO_prespectrum BOStage γ bInf structureMap).basedSpace m)
            ((TO_prespectrum BOStage γ bInf structureMap).basedSpace n) ⟶
          (TO_prespectrum BOStage γ bInf structureMap).basedSpace (m + n))
    (mul_assoc :
      ∀ l m n : ℕ,
        basedHomotopyRel
          (smashProductMap (mul l m)
              (𝟙
                ((TO_prespectrum BOStage γ bInf structureMap).basedSpace n)) ≫
            mul (l + m) n)
          (smashProductAssoc
              ((TO_prespectrum BOStage γ bInf structureMap).basedSpace l)
              ((TO_prespectrum BOStage γ bInf structureMap).basedSpace m)
              ((TO_prespectrum BOStage γ bInf structureMap).basedSpace n) ≫
            smashProductMap
              (𝟙
                ((TO_prespectrum BOStage γ bInf structureMap).basedSpace l))
              (mul m n) ≫
            mul l (m + n) ≫
              (TO_prespectrum BOStage γ bInf structureMap).basedSpaceCast
                (Nat.add_assoc l m n).symm))
    (one_mul :
      ∀ n : ℕ,
        basedHomotopyRel
          (smashProductMap unit
              (𝟙
                ((TO_prespectrum BOStage γ bInf structureMap).basedSpace n)) ≫
            mul 0 n)
          (smashProductLeftUnit
              ((TO_prespectrum BOStage γ bInf structureMap).basedSpace n) ≫
            (TO_prespectrum BOStage γ bInf structureMap).basedSpaceCast
              (Nat.zero_add n).symm))
    (mul_one :
      ∀ n : ℕ,
        basedHomotopyRel
          (smashProductMap
              (𝟙
                ((TO_prespectrum BOStage γ bInf structureMap).basedSpace n))
              unit ≫
            mul n 0)
          (smashProductRightUnit
              ((TO_prespectrum BOStage γ bInf structureMap).basedSpace n) ≫
            (TO_prespectrum BOStage γ bInf structureMap).basedSpaceCast
              (Nat.add_zero n).symm))
    (toPresentation :
      ConnectivePrespectrumReducedHomologyPresentation
        (TO_ringPrespectrum
          BOStage
          γ
          bInf structureMap unit mul mul_assoc one_mul mul_one).toPrespectrum)
    (sphereZeroModel : BasedCWComplex) :
    let TO :=
      TO_ringPrespectrum
        BOStage
        γ
        bInf structureMap unit mul mul_assoc one_mul mul_one
    ∃ (toTOHomologyRing : Ring (ringPrespectrumModTwoHomology TO toPresentation sphereZeroModel))
      (toTOHomologyAlgebra :
        RingPrespectrumModTwoHomologyModTwoAlgebra
          TO toPresentation sphereZeroModel toTOHomologyRing)
      (toBOHomologyCommRing : CommRing (boModTwoHomology BO))
      (toBOHomologyAlgebra : BOHomologyModTwoAlgebra BO toBOHomologyCommRing)
      (Φ :
        ThomHomologyAlgEquiv
          BO TO toPresentation sphereZeroModel
          toTOHomologyRing toTOHomologyAlgebra
          toBOHomologyCommRing toBOHomologyAlgebra),
      RingPrespectrumModTwoHomologyAdditiveCompatibility
          TO toPresentation sphereZeroModel toTOHomologyRing ∧
        BOHomologyAdditiveCompatibility BO toBOHomologyCommRing := by
  sorry
