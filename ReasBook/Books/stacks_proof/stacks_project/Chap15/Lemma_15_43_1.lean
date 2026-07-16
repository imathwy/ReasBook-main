import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_96_3
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Lemma_10_97_6
import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

noncomputable section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-
Domain-style sampling:
* primary domain: local commutative algebra of maximal-ideal adic completion and Krull dimension.
* sampled owner declarations:
  `Ideal.Fiber`,
  `ringKrullDim`,
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_add_ringKrullDim_quotient_of_liesOver_of_hasGoingDown`,
  `adicCompletion_isNoetherianRing`,
  `AdicCompletion.isAdicComplete`,
  `IsAdicComplete.map_algebraMap_iff`,
  `completionIdeal_pow_eq_ker_evalₐ`,
  `IsCompleteLocalRing`.
* owner abstraction: the canonical completion owner `AdicCompletion (maximalIdeal A) A`, together
  with the Chapter 10 faithful-flat completion map and localization/closed-fiber dimension
  formulas.
* primitive data: the Noetherian local ring `A`.
* derived API: the completion is a complete local ring, the completion map is local, the extended
  maximal ideal is the maximal ideal of the completion, and the closed fiber at the maximal ideal
  has Krull dimension `0`.
-/
local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) ACompletion

local instance : IsNoetherianRing ACompletion :=
  adicCompletion_isNoetherianRing (maximalIdeal A)

private theorem completionMap_maximalIdeal_isMaximal :
    Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  letI : Field (A ⧸ (maximalIdeal A) ^ 1) := by
    let e : A ⧸ (maximalIdeal A) ^ 1 ≃+* A ⧸ maximalIdeal A :=
      Ideal.quotEquivOfEq (pow_one (maximalIdeal A))
    exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
  have hker :
      Ideal.map (algebraMap A ACompletion) (maximalIdeal A) =
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1) := by
    simpa [pow_one] using
      completionIdeal_pow_eq_ker_evalₐ (maximalIdeal A)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal A)) 1
  simpa [hker] using
    (RingHom.ker_isMaximal_of_surjective
      (AdicCompletion.evalₐ (maximalIdeal A) 1)
      (AdicCompletion.surjective_evalₐ (maximalIdeal A) 1) : Ideal.IsMaximal
        (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal A) 1)))

private theorem completion_isLocalRing :
    IsLocalRing ACompletion := by
  let hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    completionMap_maximalIdeal_isMaximal A
  letI : Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := hmax
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  letI : IsNoetherianRing (A ⧸ maximalIdeal A) := inferInstance
  let hcomplete :
      IsAdicComplete (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2
  letI : IsAdicComplete (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) ACompletion :=
    hcomplete
  exact @isLocalRing_of_isAdicComplete_maximal ACompletion _
    (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) hmax hcomplete

local instance : IsLocalRing ACompletion := completion_isLocalRing A

private theorem completionMap_maximalIdeal_eq_maximalIdeal :
    Ideal.map (algebraMap A ACompletion) (maximalIdeal A) = maximalIdeal ACompletion := by
  letI :
      Ideal.IsMaximal (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) :=
    completionMap_maximalIdeal_isMaximal A
  exact IsLocalRing.eq_maximalIdeal inferInstance

omit [IsNoetherianRing A] in
instance : IsLocalHom (algebraMap A ACompletion) := by
  let φ : ACompletion →+* A ⧸ maximalIdeal A :=
    (AdicCompletion.evalOneₐ (maximalIdeal A)).toRingHom
  have hcomp : φ.comp (algebraMap A ACompletion) = Ideal.Quotient.mk (maximalIdeal A) := by
    ext x
    simp [φ]
  haveI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (φ.comp (algebraMap A ACompletion)) := by
    simpa [hcomp]
  exact isLocalHom_of_comp (algebraMap A ACompletion) φ

private theorem completion_isAdicComplete_maximalIdeal :
    IsAdicComplete (maximalIdeal ACompletion) ACompletion := by
  haveI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  haveI : IsNoetherianRing (A ⧸ maximalIdeal A) := inferInstance
  simpa [completionMap_maximalIdeal_eq_maximalIdeal A] using
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal A)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal A))).2

instance : IsCompleteLocalRing ACompletion := by
  exact
    { toIsLocalRing := completion_isLocalRing A
      toIsAdicComplete := completion_isAdicComplete_maximalIdeal A }

private noncomputable def closedFiberQuotRingEquiv :
    ClosedFiber ≃+* ACompletion ⧸ maximalIdeal ACompletion :=
  let e :
      ClosedFiber ≃+*
        ACompletion ⧸ Ideal.map (algebraMap A ACompletion) (maximalIdeal A) :=
    ((Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))) .refl).toRingEquiv).trans <|
      ((Algebra.TensorProduct.comm _ _ _).toRingEquiv.trans <|
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ _).symm.toRingEquiv)
  e.trans <| Ideal.quotEquivOfEq (completionMap_maximalIdeal_eq_maximalIdeal A)

/- The canonical closed fiber of the maximal-ideal adic completion map is a field. -/
instance : Field ClosedFiber := by
  letI : Field (ACompletion ⧸ maximalIdeal ACompletion) :=
    Ideal.Quotient.field (maximalIdeal ACompletion)
  exact IsField.toField <|
    (closedFiberQuotRingEquiv A).toMulEquiv.isField (Field.toIsField _)

-- Proof sketch: Lemma `10.97.4` identifies the quotients by powers of the maximal ideal of `A`
-- and of `AdicCompletion (maximalIdeal A) A`. Lemma `10.52.12` then gives equality of their
-- lengths, so the dimension formula of Proposition `10.60.9` yields equality of Krull
-- dimensions; alternatively one can appeal to the dimension formula in Lemma `10.112.7`.
/-- Lemma 15.43.1: a Noetherian local ring and its maximal-ideal adic completion have the same
Krull dimension. -/
@[stacks 07NV]
theorem ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion :
    ringKrullDim A = ringKrullDim ACompletion := by
  letI : RingHom.FaithfullyFlat (algebraMap A ACompletion) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat A
  let q : Ideal ACompletion := maximalIdeal ACompletion
  have hlocalA :
      ringKrullDim (Localization.AtPrime (maximalIdeal A)) = ringKrullDim A := by
    calc
      ringKrullDim (Localization.AtPrime (maximalIdeal A)) = (maximalIdeal A).height :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdeal A) _
      _ = ringKrullDim A := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have hlocalCompletion :
      ringKrullDim (Localization.AtPrime q) = ringKrullDim ACompletion := by
    calc
      ringKrullDim (Localization.AtPrime q) = q.height :=
        IsLocalization.AtPrime.ringKrullDim_eq_height q _
      _ = ringKrullDim ACompletion := by
        change (maximalIdeal ACompletion).height = ringKrullDim ACompletion
        exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have hq : q.LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    simpa [q, Ideal.under_def] using
      (IsLocalRing.maximalIdeal_comap (algebraMap A ACompletion)).symm
  have hclosedFiber :
      ringKrullDim
        ((Localization.AtPrime q) ⧸
          Ideal.map (algebraMap A (Localization.AtPrime q)) (maximalIdeal A)) = 0 := by
    have hmap :
        Ideal.map (algebraMap A (Localization.AtPrime q)) (maximalIdeal A) =
          maximalIdeal (Localization.AtPrime q) := by
      calc
        Ideal.map (algebraMap A (Localization.AtPrime q)) (maximalIdeal A) =
            Ideal.map (algebraMap ACompletion (Localization.AtPrime q))
              (Ideal.map (algebraMap A ACompletion) (maximalIdeal A)) := by
              rw [show algebraMap A (Localization.AtPrime q) =
                  (algebraMap ACompletion (Localization.AtPrime q)).comp (algebraMap A ACompletion) by
                    ext x
                    rfl, Ideal.map_map]
        _ = Ideal.map (algebraMap ACompletion (Localization.AtPrime q)) q := by
              simpa [q] using
                congrArg (Ideal.map (algebraMap ACompletion (Localization.AtPrime q)))
                  (completionMap_maximalIdeal_eq_maximalIdeal A)
        _ = maximalIdeal (Localization.AtPrime q) := by
              simpa [q] using
        (IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q))
    rw [hmap]
    letI : Field (Localization.AtPrime q ⧸ maximalIdeal (Localization.AtPrime q)) :=
      Ideal.Quotient.field (maximalIdeal (Localization.AtPrime q))
    have hfield : IsField (Localization.AtPrime q ⧸ maximalIdeal (Localization.AtPrime q)) := by
      exact Field.toIsField _
    exact ringKrullDim_eq_zero_of_isField hfield
  calc
    ringKrullDim A = ringKrullDim (Localization.AtPrime (maximalIdeal A)) := hlocalA.symm
    _ = ringKrullDim (Localization.AtPrime q) := by
      have hdim :=
        ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_add_ringKrullDim_quotient_of_liesOver_of_hasGoingDown
          (maximalIdeal A) q hq
      rw [hclosedFiber, add_zero] at hdim
      exact hdim.symm
    _ = ringKrullDim ACompletion := hlocalCompletion

end
