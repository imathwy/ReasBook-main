import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_82_13
import stacks_proof.stacks_project.Chap15.Lemma_15_3_3

universe u

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {m n : ℕ}

/-- Helper for Lemma 15.15.6: quotienting the localized matrix map by the maximal ideal and then
identifying the free quotients coordinatewise gives the concrete closed-fiber matrix map. -/
private theorem free_pi_quotient_equiv_apply_mkQ
    {S : Type*} [CommRing S] (I : Ideal S) (r : ℕ) (x : Fin r → S) :
    free_pi_quotient_equiv (R := S) (I := I) r ((I • (⊤ : Submodule S (Fin r → S))).mkQ x) =
      fun i ↦ Ideal.Quotient.mk I (x i) := by
  -- Unfold the fixed quotient comparison only on a quotient representative.
  simp [free_pi_quotient_equiv, free_pi_quotient_map]

/-- Helper for Lemma 15.15.6: quotienting the localized matrix map by the maximal ideal and then
identifying the free quotients coordinatewise gives the concrete closed-fiber matrix map. -/
private theorem quotient_toLin'_eq_conjugated_closedFiber_map
    {S : Type*} [CommRing S] (I : Ideal S) (B : Matrix (Fin n) (Fin m) S) :
    (free_pi_quotient_equiv (R := S) (I := I) n).toLinearMap.comp
        ((B.toLin').quotientMapByIdeal I) =
      (LinearMap.restrictScalars S ((B.map (Ideal.Quotient.mk I)).toLin')).comp
        (free_pi_quotient_equiv (R := S) (I := I) m).toLinearMap := by
  classical
  apply DFunLike.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule S (Fin m → S))) x
  ext i
  -- Evaluate both quotient-side maps on a quotient representative and compare coordinatewise.
  rw [LinearMap.comp_apply, LinearMap.comp_apply, quotientMapByIdeal_apply_mkQ]
  rw [free_pi_quotient_equiv_apply_mkQ I n, free_pi_quotient_equiv_apply_mkQ I m]
  simp [Matrix.toLin'_apply, dotProduct]

/-- Helper for Lemma 15.15.6: universal injectivity of the localized matrix map forces the
corresponding closed-fiber matrix map to be injective. -/
theorem injective_closedFiber_matrix_map_of_localized_universallyInjective
    {p : Ideal R} [p.IsPrime]
    (A : Matrix (Fin n) (Fin m) R)
    (huLoc : UniversallyInjective ((A.map (algebraMap R (Localization.AtPrime p))).toLin')) :
    Function.Injective
      ((A.map
          ((Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime p))).comp
            (algebraMap R (Localization.AtPrime p)))).toLin') := by
  let Rp := Localization.AtPrime p
  let I : Ideal Rp := maximalIdeal Rp
  let θ : R →+* Rp ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R Rp)
  let uLoc : (Fin m → Rp) →ₗ[Rp] (Fin n → Rp) := (A.map (algebraMap R Rp)).toLin'
  have hquot : Function.Injective (uLoc.quotientMapByIdeal I) :=
    injective_quotientMapByIdeal_of_universallyInjective uLoc huLoc I
  have hintertwine :
      (free_pi_quotient_equiv (R := Rp) (I := I) n).toLinearMap.comp (uLoc.quotientMapByIdeal I) =
        (LinearMap.restrictScalars Rp ((A.map θ).toLin')).comp
          (free_pi_quotient_equiv (R := Rp) (I := I) m).toLinearMap :=
    by
      -- Route correction: specialize the generic quotient conjugation statement to the localized
      -- matrix `A.map (algebraMap R Rp)` instead of elaborating a localization-specific `let` tower.
      simpa [uLoc, θ] using
        quotient_toLin'_eq_conjugated_closedFiber_map
          (I := I) (B := A.map (algebraMap R Rp))
  have hconj :
      LinearMap.restrictScalars Rp ((A.map θ).toLin') =
        ((free_pi_quotient_equiv (R := Rp) (I := I) n).toLinearMap.comp
          (uLoc.quotientMapByIdeal I)).comp
            (free_pi_quotient_equiv (R := Rp) (I := I) m).symm.toLinearMap := by
    -- Rewrite the intertwining identity in conjugation form.
    ext x
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun hintertwine ((free_pi_quotient_equiv (R := Rp) (I := I) m).symm x)
  have hInjectiveRestrict :
      Function.Injective (LinearMap.restrictScalars Rp ((A.map θ).toLin')) := by
    rw [hconj]
    exact
      (free_pi_quotient_equiv (R := Rp) (I := I) n).injective.comp
        (hquot.comp (free_pi_quotient_equiv (R := Rp) (I := I) m).symm.injective)
  exact hInjectiveRestrict

end

end LinearMap
