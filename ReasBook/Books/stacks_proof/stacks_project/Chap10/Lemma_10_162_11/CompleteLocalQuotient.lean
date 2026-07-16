import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_160_1

universe u

open IsLocalRing AdicCompletion
open scoped TensorProduct

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- Helper for Chap10 Lemma 10 162 11: the quotient of a local ring by a proper ideal is local. -/
lemma completeLocalQuotient_isLocalRing (I : Ideal R) (hI : I ≠ ⊤) : IsLocalRing (R ⧸ I) := by
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Lemma 10 162 11: for a proper quotient of a local ring, the maximal ideal
of the quotient is the image of the maximal ideal of the source. -/
lemma completeLocalQuotient_maximalIdeal_eq_map (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) := by
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Lemma 10 162 11: the `maximalIdeal R`-adic completion of a quotient,
viewed as an `R`-module, identifies canonically with the quotient itself. -/
noncomputable def completeLocalQuotient_completionLinearEquiv (I : Ideal R) :
    AdicCompletion (maximalIdeal R) (R ⧸ I) ≃ₗ[R] R ⧸ I :=
  let eCompletion :
      AdicCompletion (maximalIdeal R) (R ⧸ I) ≃ₗ[R]
        AdicCompletion (maximalIdeal R) R ⊗[R] (R ⧸ I) :=
    (LinearEquiv.restrictScalars R
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) (R ⧸ I))).symm
  let eTensor :
      (R ⧸ I) ≃ₐ[R] AdicCompletion (maximalIdeal R) R ⊗[R] (R ⧸ I) :=
    (Algebra.TensorProduct.lid R (R ⧸ I)).symm.trans
      (Algebra.TensorProduct.congr
        (AdicCompletion.ofAlgEquiv (maximalIdeal R))
        (show (R ⧸ I) ≃ₐ[R] (R ⧸ I) from AlgEquiv.refl))
  eCompletion.trans eTensor.symm.toLinearEquiv

/-- Helper for Chap10 Lemma 10 162 11: the quotient-completion equivalence sends the canonical
completion class of `x` back to `x`. -/
lemma completeLocalQuotient_completionLinearEquiv_of (I : Ideal R) (x : R ⧸ I) :
    completeLocalQuotient_completionLinearEquiv (R := R) I
        (AdicCompletion.of (maximalIdeal R) (R ⧸ I) x) = x := by
  simp [completeLocalQuotient_completionLinearEquiv]

/-- Helper for Chap10 Lemma 10 162 11: as an `R`-module, the quotient `R ⧸ I` is complete for
the `maximalIdeal R`-adic topology. -/
lemma completeLocalQuotient_isAdicComplete_maximalIdeal (I : Ideal R) :
    IsAdicComplete (maximalIdeal R) (R ⧸ I) := by
  have hof_eq :
      (AdicCompletion.of (maximalIdeal R) (R ⧸ I) :
          (R ⧸ I) →ₗ[R] AdicCompletion (maximalIdeal R) (R ⧸ I)) =
        (completeLocalQuotient_completionLinearEquiv (R := R) I).symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply (completeLocalQuotient_completionLinearEquiv (R := R) I).injective
    simp [completeLocalQuotient_completionLinearEquiv_of]
  exact (AdicCompletion.of_bijective_iff).mp <| by
    simpa [hof_eq] using
      (completeLocalQuotient_completionLinearEquiv (R := R) I).symm.bijective

/-- Helper for Chap10 Lemma 10 162 11: a quotient of a complete local ring is complete for the
image of the source maximal ideal. -/
lemma completeLocalQuotient_isAdicComplete_mappedMaximalIdeal (I : Ideal R) (_hI : I ≠ ⊤) :
    IsAdicComplete (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) (R ⧸ I) := by
  exact
    (IsAdicComplete.map_algebraMap_iff
      (R := R) (S := R ⧸ I) (I := maximalIdeal R) (M := R ⧸ I)).2 <|
      completeLocalQuotient_isAdicComplete_maximalIdeal (R := R) I

/-- Helper for Chap10 Lemma 10 162 11: a proper quotient of a Noetherian complete local ring is
again a complete local ring. -/
theorem completeLocalQuotient_isCompleteLocalRing (I : Ideal R) (hI : I ≠ ⊤) :
    IsCompleteLocalRing (R ⧸ I) := by
  letI : IsLocalRing (R ⧸ I) := completeLocalQuotient_isLocalRing I hI
  have hcomplete : IsAdicComplete (maximalIdeal (R ⧸ I)) (R ⧸ I) := by
    rw [← completeLocalQuotient_maximalIdeal_eq_map (R := R) I]
    exact completeLocalQuotient_isAdicComplete_mappedMaximalIdeal (R := R) I hI
  exact
    { toIsLocalRing := completeLocalQuotient_isLocalRing I hI
      toIsAdicComplete := hcomplete }

end
