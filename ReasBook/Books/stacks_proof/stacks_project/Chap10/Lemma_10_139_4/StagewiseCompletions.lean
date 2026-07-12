import Mathlib
import StacksProject_2024.Chap10.Lemma_10_139_4.TruncationKernels

open Algebra
open scoped TensorProduct
open KaehlerDifferential

universe u v

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

section SmoothSection

variable [Algebra.Smooth R S] (σ : S →ₐ[R] R)
  (hσ : Function.LeftInverse σ (algebraMap R S))

include hσ

/-- Helper for Lemma 10.139.4: the stage-`1` inverse `σ₁` is the canonical transport
`S / I ≃ R ≃ P / J`, where `I = ker σ` and `J` is the variable ideal. -/
noncomputable def smooth_section_stageOne_inverse {d : ℕ} :
    S ⧸ RingHom.ker σ →ₐ[R]
      MvPolynomial (Fin d) R ⧸ MvPolynomial.idealOfVars (Fin d) R :=
  ((idealOfVars_quotientAlgEquiv (R := R) (d := d)).symm.toAlgHom).comp
    ((smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ).toAlgHom)

/-- Helper for Lemma 10.139.4: the first power of the variable ideal is the variable ideal itself. -/
theorem idealOfVars_pow_one_eq {d : ℕ} :
    (MvPolynomial.idealOfVars (Fin d) R) ^ 1 = MvPolynomial.idealOfVars (Fin d) R := by
  simp

/-- Helper for Lemma 10.139.4: the first power of `ker σ` is `ker σ` itself. -/
theorem smooth_section_ker_pow_one_eq :
    (RingHom.ker σ) ^ 1 = RingHom.ker σ := by
  simp

/-- Helper for Lemma 10.139.4: the source level-`1` quotient `P / J^1` is canonically identified
with `P / J`. -/
noncomputable def idealOfVars_powOneQuotientAlgEquiv {d : ℕ} :
    (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1) ≃ₐ[R]
      (MvPolynomial (Fin d) R ⧸ MvPolynomial.idealOfVars (Fin d) R) :=
  Ideal.quotientEquivAlgOfEq (R₁ := R) (A := MvPolynomial (Fin d) R)
    (idealOfVars_pow_one_eq (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))

/-- Helper for Lemma 10.139.4: the target level-`1` quotient `S / I^1` is canonically identified
with `S / I`. -/
noncomputable def smooth_section_kerPowOneQuotientAlgEquiv :
    (S ⧸ (RingHom.ker σ) ^ 1) ≃ₐ[R] (S ⧸ RingHom.ker σ) :=
  Ideal.quotientEquivAlgOfEq (R₁ := R) (A := S)
    (smooth_section_ker_pow_one_eq (R := R) (S := S) (σ := σ) (hσ := hσ))

/-- Helper for Lemma 10.139.4: after transporting both source and target level-`1` quotients along
`pow_one`, the first truncation map is exactly the canonical quotient transport `P / J ≃ R ≃ S / I`.
-/
theorem truncation_one_eq_canonical_transport {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    (smooth_section_kerPowOneQuotientAlgEquiv (R := R) (S := S) (σ := σ) (hσ := hσ)).toAlgHom.comp
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1) =
      (((smooth_section_quotientKerAlgEquiv
            (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom).comp
          (idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom).comp
        (idealOfVars_powOneQuotientAlgEquiv
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).toAlgHom := by
  -- Compare the transported level-`1` maps after precomposing with the quotient map from the
  -- polynomial ring; then quotient extensionality reduces the proof to the variable classes.
  refine Ideal.Quotient.algHom_ext _ ?_
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  -- On each variable, the left side is the quotient class of `f i`, hence zero in `S / ker σ`,
  -- while the right side is zero because `idealOfVars_quotientAlgEquiv` comes from zero evaluation.
  calc
    ((((smooth_section_kerPowOneQuotientAlgEquiv
        (R := R) (S := S) (σ := σ) (hσ := hσ)).toAlgHom).comp
          (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1)).comp
          (Ideal.Quotient.mkₐ R ((MvPolynomial.idealOfVars (Fin d) R) ^ 1)))
        (MvPolynomial.X i) =
      Ideal.Quotient.mk (RingHom.ker σ) ((f i : RingHom.ker σ) : S) := by
        simp [cotangent_lift_truncated_map, cotangent_lift_polynomial_map,
          smooth_section_kerPowOneQuotientAlgEquiv]
    _ = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (f i).property
    _ = ((smooth_section_quotientKerAlgEquiv
        (R := R) (S := S) (σ := σ) hσ).symm) (0 : R) := by
      simpa using
        (map_zero ((smooth_section_quotientKerAlgEquiv
          (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom)).symm
    _ =
      ((((smooth_section_quotientKerAlgEquiv
          (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom).comp
            (idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom).comp
            (idealOfVars_powOneQuotientAlgEquiv
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).toAlgHom).comp
            (Ideal.Quotient.mkₐ R ((MvPolynomial.idealOfVars (Fin d) R) ^ 1))
            (MvPolynomial.X i) := by
        symm
        change
          ((smooth_section_quotientKerAlgEquiv
              (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom)
              (((((idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom).comp
                  (idealOfVars_powOneQuotientAlgEquiv
                    (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).toAlgHom).comp
                    (Ideal.Quotient.mkₐ R ((MvPolynomial.idealOfVars (Fin d) R) ^ 1)))
                (MvPolynomial.X i)) =
            ((smooth_section_quotientKerAlgEquiv
              (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom) 0
        congr 1
        calc
          ((((idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom).comp
              (idealOfVars_powOneQuotientAlgEquiv
                (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).toAlgHom).comp
                (Ideal.Quotient.mkₐ R ((MvPolynomial.idealOfVars (Fin d) R) ^ 1)))
              (MvPolynomial.X i) =
            (idealOfVars_quotientAlgEquiv (R := R) (d := d))
              (Ideal.Quotient.mk (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial.X i)) := by
                simp [idealOfVars_powOneQuotientAlgEquiv]
          _ = (idealOfVars_quotientAlgEquiv (R := R) (d := d)) 0 := by
            congr 1
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (idealOfVars_variable_mem (R := R) i)
          _ = 0 := by
            simpa using map_zero ((idealOfVars_quotientAlgEquiv (R := R) (d := d)).toAlgHom)

/-- Helper for Lemma 10.139.4: the canonical stage-`1` inverse transported back to the
`pow_one` quotients. This is the level-`1` inverse used to normalize the successor lift. -/
noncomputable def smooth_section_stageOne_inverse_powOne {d : ℕ} :
    S ⧸ (RingHom.ker σ) ^ 1 →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1 :=
  (((idealOfVars_powOneQuotientAlgEquiv
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).symm).toAlgHom).comp
    ((smooth_section_stageOne_inverse (R := R) (S := S) (σ := σ) hσ).comp
      (smooth_section_kerPowOneQuotientAlgEquiv
        (R := R) (S := S) (σ := σ) (hσ := hσ)).toAlgHom)

/-- Helper for Lemma 10.139.4: the transported stage-`1` inverse is indeed inverse to the first
truncation map. This is the exact level-`1` normalization used in the textbook induction. -/
theorem smooth_section_stageOne_inverse_powOne_spec {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    (smooth_section_stageOne_inverse_powOne (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1) =
      AlgHom.id R
        (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1) := by
  -- Route correction: normalize the level-`1` inverse on the `pow_one` quotients first, so later
  -- successor lifts can be compared to the canonical stage-`1` inverse without ad hoc transports.
  let eJ1 :=
    idealOfVars_powOneQuotientAlgEquiv (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)
  let eP1 := idealOfVars_quotientAlgEquiv (R := R) (d := d)
  let eS1 := smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ
  have htransport :=
    truncation_one_eq_canonical_transport (R := R) (S := S) (σ := σ) hσ f
  have hcomp :=
    congrArg
      (fun β =>
        (((eJ1.symm.toAlgHom).comp (eP1.symm.toAlgHom)).comp eS1.toAlgHom).comp β)
      htransport
  have hcancel :
      ((((eJ1.symm.toAlgHom).comp (eP1.symm.toAlgHom)).comp eS1.toAlgHom).comp
          (((eS1.symm.toAlgHom).comp eP1.toAlgHom).comp eJ1.toAlgHom)) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 1) := by
    ext x
    simp
  simpa [smooth_section_stageOne_inverse_powOne, smooth_section_stageOne_inverse,
    AlgHom.comp_assoc] using hcomp.trans hcancel

/-- Helper for Lemma 10.139.4: the transported stage-`1` inverse is inverse to the first
truncation map in the opposite direction as well. This closes the entire level-`1` base case for
the source-faithful induction. -/
theorem smooth_section_stageOne_inverse_powOne_spec_symm {d : ℕ}
    (f : Fin d → RingHom.ker σ) :
    (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1).comp
        (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)) =
      AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 1) := by
  -- Apply the canonical quotient transport to the composite and cancel the stage-`1` source and
  -- target identifications explicitly.
  let eJ1 :=
    idealOfVars_powOneQuotientAlgEquiv (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)
  let eP1 := idealOfVars_quotientAlgEquiv (R := R) (d := d)
  let eS1 := smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ
  let eI1 :=
    smooth_section_kerPowOneQuotientAlgEquiv (R := R) (S := S) (σ := σ) (hσ := hσ)
  have htransport :=
    truncation_one_eq_canonical_transport (R := R) (S := S) (σ := σ) hσ f
  ext x
  apply eI1.injective
  -- Evaluate the transported first truncation at the canonical stage-`1` inverse and simplify
  -- through the quotient equivalences.
  calc
    eI1
        (((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1).comp
          (smooth_section_stageOne_inverse_powOne
            (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))) x) =
      ((((eS1.symm.toAlgHom).comp eP1.toAlgHom).comp eJ1.toAlgHom)
        ((smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)) x)) := by
            exact AlgHom.congr_fun htransport
              ((smooth_section_stageOne_inverse_powOne
                (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)) x)
    _ = eI1 x := by
      simp [smooth_section_stageOne_inverse_powOne, smooth_section_stageOne_inverse,
        AlgHom.comp_assoc, eJ1, eP1, eS1, eI1]


/-- Helper for Lemma 10.139.4: any actual inverse `σₙ` to `Ψtrunc n` reduces to the transported
stage-`1` inverse after passing from `n`th-order quotients to first-order quotients. -/
theorem truncation_inverse_reduces_to_stage_one {d n : ℕ}
    (hn : 0 < n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn))).comp σn =
      (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn))) := by
  -- Evaluate both maps at a stage-`n` class, reduce via compatibility of `Ψtrunc`, and then use
  -- the verified stage-`1` inverse to close the comparison.
  ext x
  calc
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)) (σn x) =
      (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))
        ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 1)
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)) (σn x))) := by
          symm
          exact AlgHom.congr_fun
            (smooth_section_stageOne_inverse_powOne_spec
              (R := R) (S := S) (σ := σ) hσ (d := d) f)
            (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)) (σn x))
    _ =
      (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn))
          ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) (σn x))) := by
          congr 1
          exact (AlgHom.congr_fun
            (cotangent_lift_truncated_map_compatible
              (R := R) (S := S) (σ := σ) f (m := 1) (n := n)
              (Nat.succ_le_of_lt hn))
            (σn x)).symm
    _ =
      (smooth_section_stageOne_inverse_powOne
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d))
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)) x) := by
          congr 1
          exact congrArg
            (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.succ_le_of_lt hn)))
            (AlgHom.congr_fun hΨσ x)

/-- Helper for Lemma 10.139.4: once an inverse `σₙ` to `Ψtrunc n` has been constructed, formal
smoothness lifts it one stage further and the lift descends to
`S / (ker σ)^(n + 1) → P / J^(n + 1)`. This restores the textbook successor-lift step before the
variable-shift correction. -/
theorem formally_smooth_lift_of_truncation_inverse_descends {d n : ℕ}
    (hn : 2 ≤ n)
    (f : Fin d → RingHom.ker σ)
    (σn : S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσΨ :
      σn.comp (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ :
      (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f n).comp σn =
        AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    ∃ τbar : S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp τbar =
        σn.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))) := by
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let qJ :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  let qI :
      S ⧸ I ^ (n + 1) →ₐ[R] S ⧸ I ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  let σlift : S →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ n :=
    σn.comp (Ideal.Quotient.mkₐ R (I ^ n))
  have hqJ_surj : Function.Surjective qJ := by
    intro x
    rcases Ideal.Quotient.factor_surjective
        (by simpa using (Ideal.pow_le_pow_right (I := J) (Nat.le_succ n))) x with ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have hn0 : 0 < n := lt_of_lt_of_le (by simp) hn
  have hqJ_nilpotent : IsNilpotent (RingHom.ker qJ.toRingHom) := by
    change IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow J (Nat.le_succ n)))
    exact factorPow_transition_kernel_isNilpotent
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R) (K := J) (n := n) hn0
  let τ : S →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Algebra.FormallySmooth.liftOfSurjective σlift qJ hqJ_surj hqJ_nilpotent
  have hqJτ : qJ.comp τ = σlift := by
    simpa [τ, σlift] using
      (Algebra.FormallySmooth.comp_liftOfSurjective σlift qJ hqJ_surj hqJ_nilpotent)
  let qJ1 :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ 1 :=
    Ideal.Quotient.factorₐ R <| by
      simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 1 by simp))
  let qJn1 :
      MvPolynomial (Fin d) R ⧸ J ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ 1 :=
    Ideal.Quotient.factorₐ R <| by
      simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n by omega))
  let qIn1 :
      S ⧸ I ^ n →ₐ[R] S ⧸ I ^ 1 :=
    Ideal.Quotient.factorₐ R <| by
      simpa using (Ideal.pow_le_pow_right (I := I) (show 1 ≤ n by omega))
  let σ1lift : S →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ 1 :=
    (smooth_section_stageOne_inverse_powOne
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp
      (Ideal.Quotient.mkₐ R (I ^ 1))
  have hqJ1 :
      qJ1 = qJn1.comp qJ := by
    symm
    simpa [qJ1, qJn1, qJ] using
      (Ideal.Quotient.factorₐ_comp (R₁ := R)
        (I := J ^ (n + 1)) (J := J ^ n) (K := J ^ 1)
        (hIJ := Ideal.pow_le_pow_right (Nat.le_succ n))
        (hJK := by simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n by omega))))
  have hqIn1_mk :
      qIn1.comp (Ideal.Quotient.mkₐ R (I ^ n)) = Ideal.Quotient.mkₐ R (I ^ 1) := by
    simpa [qIn1] using
      (Ideal.Quotient.factorₐ_comp_mk (R₁ := R)
        (I := I ^ n) (J := I ^ 1)
        (hIJ := by simpa using (Ideal.pow_le_pow_right (I := I) (show 1 ≤ n by omega))))
  have hqJ1τ : qJ1.comp τ = σ1lift := by
    -- Reduce the formal smooth lift all the way to level `1` and compare with the canonical
    -- stage-`1` inverse provided by the previously constructed inverse `σₙ`.
    calc
      qJ1.comp τ = (qJn1.comp qJ).comp τ := by rw [hqJ1]
      _ = qJn1.comp (qJ.comp τ) := by rw [AlgHom.comp_assoc]
      _ = qJn1.comp σlift := by rw [hqJτ]
      _ = (qJn1.comp σn).comp (Ideal.Quotient.mkₐ R (I ^ n)) := by
            change qJn1.comp (σn.comp (Ideal.Quotient.mkₐ R (I ^ n))) =
              (qJn1.comp σn).comp (Ideal.Quotient.mkₐ R (I ^ n))
            rw [AlgHom.comp_assoc]
      _ =
          ((smooth_section_stageOne_inverse_powOne
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp qIn1).comp
            (Ideal.Quotient.mkₐ R (I ^ n)) := by
              rw [truncation_inverse_reduces_to_stage_one
                (R := R) (S := S) (σ := σ) (hσ := hσ)
                (d := d) (n := n) hn0 f σn hσΨ hΨσ]
      _ =
          (smooth_section_stageOne_inverse_powOne
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d)).comp
            (qIn1.comp (Ideal.Quotient.mkₐ R (I ^ n))) := by
              rw [AlgHom.comp_assoc]
      _ = σ1lift := by
            rw [hqIn1_mk]
  have hmapI :
      Ideal.map τ.toRingHom I ≤ Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hx0 : qJ1 (τ x) = 0 := by
      calc
        qJ1 (τ x) = σ1lift x := by
          exact AlgHom.congr_fun hqJ1τ x
        _ = 0 := by
          have hxquot : Ideal.Quotient.mk (I ^ 1) x = 0 := by
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [pow_one, I] using hx)
          simpa [σ1lift, hxquot]
    have hxker : τ x ∈ RingHom.ker qJ1.toRingHom := RingHom.mem_ker.mpr hx0
    rwa [show RingHom.ker qJ1.toRingHom =
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J by
          simpa [qJ1, pow_one, J] using
            (factorPow_to_one_kernel_eq_map
              (R := R) (S := S) (σ := σ) (hσ := hσ)
              (A := MvPolynomial (Fin d) R) (K := J) n)] at hxker
  have hpowI :
      Ideal.map τ.toRingHom (I ^ (n + 1)) ≤
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
    -- Once the lift carries `I` into the visible image of `J`, the same holds for all powers.
    simpa [Ideal.map_pow] using Ideal.pow_right_mono hmapI (n + 1)
  have hτ_zero :
      ∀ x : S, x ∈ I ^ (n + 1) → τ x = 0 := by
    intro x hx
    have hJpow_bot :
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) = ⊥ := by
      calc
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) =
          Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ (n + 1)) := by
            rw [Ideal.map_pow]
        _ = ⊥ := Ideal.map_quotient_self _
    have hxpow :
        τ x ∈ (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
      exact hpowI <| Ideal.mem_map_of_mem _ hx
    have hxbot :
        τ x ∈
          (⊥ :
            Ideal (MvPolynomial (Fin d) R ⧸ J ^ (n + 1))) := by
      simpa [hJpow_bot] using hxpow
    simpa using hxbot
  let τbar :
      S ⧸ I ^ (n + 1) →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Ideal.Quotient.liftₐ (I ^ (n + 1)) τ hτ_zero
  refine ⟨τbar, ?_⟩
  refine Ideal.Quotient.algHom_ext _ ?_
  ext x
  -- After precomposing with the quotient map from `S`, the descended lift is the original
  -- formally smooth lift `τ`, and `qI` reduces the quotient class of `x` modulo `I^n`.
  calc
    (((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp τbar).comp
        (Ideal.Quotient.mkₐ R (I ^ (n + 1)))) x =
      qJ (τ x) := by
        simp [τbar, qJ, AlgHom.comp_assoc]
    _ = σn (Ideal.Quotient.mk (I ^ n) x) := by
        exact AlgHom.congr_fun hqJτ x
    _ =
      ((σn.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n)))).comp
        (Ideal.Quotient.mkₐ R (I ^ (n + 1)))) x := by
          have hmk :
              ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
                (Ideal.Quotient.mkₐ R (I ^ (n + 1)))) x =
                Ideal.Quotient.mk (I ^ n) x := by
            simpa using
              AlgHom.congr_fun
                (Ideal.Quotient.factorₐ_comp_mk (R₁ := R)
                  (I := I ^ (n + 1)) (J := I ^ n)
                  (hIJ := Ideal.pow_le_pow_right (Nat.le_succ n)))
                x
          rw [← hmk]
          rfl

/-- Helper for Lemma 10.139.4: the formally-smooth lift of the canonical stage-`1` inverse to
`P / J^(n + 1)` sends `(ker σ)^(n + 1)` to zero, so it descends to a map
`S / (ker σ)^(n + 1) → P / J^(n + 1)`. -/
theorem stage_one_formally_smooth_lift_descends_to_quotient_pow {d : ℕ} (n : ℕ) :
    Nonempty
      (S ⧸ (RingHom.ker σ) ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) := by
  let I : Ideal S := RingHom.ker σ
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let σ1lift : S →ₐ[R] MvPolynomial (Fin d) R ⧸ J :=
    (smooth_section_stageOne_inverse (R := R) (S := S) (σ := σ) hσ).comp
      (Ideal.Quotient.mkₐ R I)
  let q1 :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J :=
    Ideal.Quotient.factorₐ R <| by
      simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 1 by simp))
  have hq1_surj : Function.Surjective q1 := by
    intro x
    rcases Ideal.Quotient.factor_surjective
        (by
          simpa using
            (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 1 by simp))) x with ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have hq1_ker :
      RingHom.ker q1.toRingHom =
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J := by
    simpa [q1] using
      (Ideal.Quotient.factor_ker (I := J ^ (n + 1)) (J := J) <| by
        simpa using (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 1 by simp)))
  have hq1_nilpotent : IsNilpotent (RingHom.ker q1.toRingHom) := by
    refine ⟨n + 1, ?_⟩
    -- The image of `J` in `P / J^(n + 1)` has `(n + 1)`st power zero.
    rw [hq1_ker]
    calc
      (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) =
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ (n + 1)) := by
          rw [Ideal.map_pow]
      _ = ⊥ := Ideal.map_quotient_self _
  let τ :
      S →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Algebra.FormallySmooth.liftOfSurjective σ1lift q1 hq1_surj hq1_nilpotent
  have hq1τ : q1.comp τ = σ1lift := by
    simpa [τ] using
      (Algebra.FormallySmooth.comp_liftOfSurjective σ1lift q1 hq1_surj hq1_nilpotent)
  have hmapI :
      Ideal.map τ.toRingHom I ≤ Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    -- Reducing the lift modulo `J` matches the stage-`1` inverse, so every element of `ker σ`
    -- lands in the kernel of `q1`, i.e. in the image of `J`.
    have hx0 :
        q1 (τ x) = 0 := by
      calc
        q1 (τ x) = σ1lift x := by
          exact AlgHom.congr_fun hq1τ x
        _ = 0 := by
          have hxquot : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
          simpa [σ1lift, hxquot]
    have hxker : τ x ∈ RingHom.ker q1.toRingHom := RingHom.mem_ker.mpr hx0
    rwa [hq1_ker] at hxker
  have hpowI :
      Ideal.map τ.toRingHom (I ^ (n + 1)) ≤
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
    -- Once `τ(I)` lies in the image of `J`, the same holds for `(n + 1)`st powers.
    simpa [Ideal.map_pow] using Ideal.pow_right_mono hmapI (n + 1)
  have hτ_zero :
      ∀ x : S, x ∈ I ^ (n + 1) → τ x = 0 := by
    intro x hx
    have hJpow_bot :
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) = ⊥ := by
      calc
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) =
          Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ (n + 1)) := by
            rw [Ideal.map_pow]
        _ = ⊥ := Ideal.map_quotient_self _
    have hxpow :
        τ x ∈ (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
      exact hpowI <| Ideal.mem_map_of_mem _ hx
    have hxbot :
        τ x ∈
          (⊥ :
            Ideal (MvPolynomial (Fin d) R ⧸ J ^ (n + 1))) := by
      simpa [hJpow_bot] using hxpow
    simpa using hxbot
  let τbar :
      S ⧸ I ^ (n + 1) →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Ideal.Quotient.liftₐ (I ^ (n + 1)) τ hτ_zero
  exact ⟨τbar⟩

/-- Helper for Lemma 10.139.4: a compatible family of quotient inverses packages into an
`R`-algebra equivalence between the corresponding adic completions. -/
noncomputable def completion_algEquiv_of_truncation_inverses {d : ℕ}
    (Ψtrunc : (n : ℕ) →
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n →ₐ[R]
        S ⧸ (RingHom.ker σ) ^ n)
    (hΨtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (Ψtrunc n) =
          (Ψtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)))
    (σtrunc : (n : ℕ) →
      S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
          (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)))
    (hσΨ : ∀ n,
      (σtrunc n).comp (Ψtrunc n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ : ∀ n, (Ψtrunc n).comp (σtrunc n) = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    AdicCompletion (RingHom.ker σ) S ≃ₐ[R]
      AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) := by
  let toCompletionFamily : (n : ℕ) →
      AdicCompletion (RingHom.ker σ) S →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n :=
    fun n ↦ (σtrunc n).comp ((AdicCompletion.evalₐ (RingHom.ker σ) n).restrictScalars R)
  have htoCompletionFamily :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
            (toCompletionFamily n) =
          toCompletionFamily m := by
    intro m n hmn
    ext x
    let p : AdicCompletion (RingHom.ker σ) S → Prop := fun y ↦
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
          (toCompletionFamily n) y =
        toCompletionFamily m y
    change p x
    -- Reduce the compatibility check to a representative of the source completion.
    refine AdicCompletion.induction_on (I := RingHom.ker σ) (M := S) x ?_
    intro s
    dsimp [p, toCompletionFamily]
    have hs :
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (AdicCompletion.evalₐ (RingHom.ker σ) n ((AdicCompletion.mk (RingHom.ker σ) S) s)) =
          AdicCompletion.evalₐ (RingHom.ker σ) m ((AdicCompletion.mk (RingHom.ker σ) S) s) := by
      simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorₐ_comp_mk] using
        (AdicCompletion.Ideal.mk_eq_mk (I := RingHom.ker σ) (m := m) (n := n) hmn s)
    -- On a concrete representative, the target equality is exactly the stagewise compatibility
    -- of `σtrunc`, together with the canonical quotient transition on `evalₐ`.
    calc
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
          ((σtrunc n)
            (AdicCompletion.evalₐ (RingHom.ker σ) n
              ((AdicCompletion.mk (RingHom.ker σ) S) s))) =
        (σtrunc m)
          ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (AdicCompletion.evalₐ (RingHom.ker σ) n
              ((AdicCompletion.mk (RingHom.ker σ) S) s))) := by
            exact AlgHom.congr_fun (hσtrunc hmn)
              (AdicCompletion.evalₐ (RingHom.ker σ) n
                ((AdicCompletion.mk (RingHom.ker σ) S) s))
      _ = (σtrunc m)
          (AdicCompletion.evalₐ (RingHom.ker σ) m
            ((AdicCompletion.mk (RingHom.ker σ) S) s)) := by
            exact congrArg (σtrunc m) hs
  let toCompletion :
      AdicCompletion (RingHom.ker σ) S →ₐ[R]
        AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) :=
    AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars (Fin d) R)
      toCompletionFamily htoCompletionFamily
  let fromCompletionFamily : (n : ℕ) →
      AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) →ₐ[R]
        S ⧸ (RingHom.ker σ) ^ n :=
    fun n ↦ (Ψtrunc n).comp
      ((AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n).restrictScalars R)
  have hfromCompletionFamily :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
            (fromCompletionFamily n) =
          fromCompletionFamily m := by
    intro m n hmn
    ext x
    let q :
        AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) → Prop :=
      fun y ↦
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
            (fromCompletionFamily n) y =
          fromCompletionFamily m y
    change q x
    -- The same quotientwise reduction works on the polynomial completion side.
    refine AdicCompletion.induction_on (I := MvPolynomial.idealOfVars (Fin d) R)
      (M := MvPolynomial (Fin d) R) x ?_
    intro p
    dsimp [q, fromCompletionFamily]
    have hp :
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
              ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
                (MvPolynomial (Fin d) R)) p)) =
          AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) m
            ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
              (MvPolynomial (Fin d) R)) p) := by
      simpa [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorₐ_comp_mk] using
        (AdicCompletion.Ideal.mk_eq_mk (I := MvPolynomial.idealOfVars (Fin d) R)
          (m := m) (n := n) hmn p)
    -- The polynomial-side compatibility reduces to `hΨtrunc` on the quotient class of `p`.
    calc
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
          ((Ψtrunc n)
            (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
              ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
                (MvPolynomial (Fin d) R)) p))) =
        (Ψtrunc m)
          ((Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))
            (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
              ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
                (MvPolynomial (Fin d) R)) p))) := by
            exact AlgHom.congr_fun (hΨtrunc hmn)
              (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
                ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
                  (MvPolynomial (Fin d) R)) p))
      _ = (Ψtrunc m)
          (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) m
            ((AdicCompletion.mk (MvPolynomial.idealOfVars (Fin d) R)
              (MvPolynomial (Fin d) R)) p)) := by
            exact congrArg (Ψtrunc m) hp
  let fromCompletion :
      AdicCompletion (MvPolynomial.idealOfVars (Fin d) R) (MvPolynomial (Fin d) R) →ₐ[R]
        AdicCompletion (RingHom.ker σ) S :=
    AdicCompletion.liftAlgHom (RingHom.ker σ) fromCompletionFamily hfromCompletionFamily
  -- Compare the two lifted completion maps quotientwise at every stage.
  refine AlgEquiv.ofAlgHom toCompletion fromCompletion ?_ ?_
  · apply AlgHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    -- After evaluating at stage `n`, the composite reduces to `σtrunc n ≫ Ψtrunc n`.
    calc
      AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n
          (toCompletion (fromCompletion x)) =
            toCompletionFamily n (fromCompletion x) := by
              simpa [toCompletion] using
                (AdicCompletion.evalₐ_liftAlgHom (MvPolynomial.idealOfVars (Fin d) R)
                  toCompletionFamily htoCompletionFamily n (fromCompletion x))
      _ = σtrunc n (fromCompletionFamily n x) := by
            exact congrArg (σtrunc n) <| by
              simpa [fromCompletion] using
                (AdicCompletion.evalₐ_liftAlgHom (RingHom.ker σ)
                  fromCompletionFamily hfromCompletionFamily n x)
      _ = σtrunc n
          (Ψtrunc n (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n x)) := by rfl
      _ = AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n x := by
            simpa using
              AlgHom.congr_fun (hσΨ n)
                (AdicCompletion.evalₐ (MvPolynomial.idealOfVars (Fin d) R) n x)
  · apply AlgHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    -- The opposite composite reduces to `Ψtrunc n ≫ σtrunc n` on the `n`th quotient.
    calc
      AdicCompletion.evalₐ (RingHom.ker σ) n (fromCompletion (toCompletion x)) =
          fromCompletionFamily n (toCompletion x) := by
            simpa [fromCompletion] using
              (AdicCompletion.evalₐ_liftAlgHom (RingHom.ker σ)
                fromCompletionFamily hfromCompletionFamily n (toCompletion x))
      _ = Ψtrunc n (toCompletionFamily n x) := by
            exact congrArg (Ψtrunc n) <| by
              simpa [toCompletion] using
                (AdicCompletion.evalₐ_liftAlgHom (MvPolynomial.idealOfVars (Fin d) R)
                  toCompletionFamily htoCompletionFamily n x)
      _ = Ψtrunc n (σtrunc n (AdicCompletion.evalₐ (RingHom.ker σ) n x)) := by rfl
      _ = AdicCompletion.evalₐ (RingHom.ker σ) n x := by
            simpa using
              AlgHom.congr_fun (hΨσ n) (AdicCompletion.evalₐ (RingHom.ker σ) n x)

/-- Helper for Lemma 10.139.4: once the source-faithful induction supplies compatible quotient
inverses, the final power-series presentation follows by passing to adic completions. -/
theorem completion_equiv_of_truncation_inverses {d : ℕ}
    (Ψtrunc : (n : ℕ) →
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n →ₐ[R]
        S ⧸ (RingHom.ker σ) ^ n)
    (hΨtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (Ψtrunc n) =
          (Ψtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)))
    (σtrunc : (n : ℕ) →
      S ⧸ (RingHom.ker σ) ^ n →ₐ[R]
        MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (hσtrunc :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (σtrunc n) =
          (σtrunc m).comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)))
    (hσΨ : ∀ n,
      (σtrunc n).comp (Ψtrunc n) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ n))
    (hΨσ : ∀ n, (Ψtrunc n).comp (σtrunc n) = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ n)) :
    Nonempty ((AdicCompletion (RingHom.ker σ) S) ≃ₐ[R] MvPowerSeries (Fin d) R) := by
  let eCompletion :=
    completion_algEquiv_of_truncation_inverses (R := R) (S := S) (σ := σ)
      Ψtrunc hΨtrunc σtrunc hσtrunc hσΨ hΨσ
  -- Compose the completion comparison with the canonical power-series/completion equivalence.
  exact ⟨eCompletion.trans
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin d) R).symm.restrictScalars R)⟩

end SmoothSection

end
