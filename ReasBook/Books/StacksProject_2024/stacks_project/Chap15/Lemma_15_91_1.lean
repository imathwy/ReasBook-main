import StacksProject_2024.Chap10.Lemma_10_96_3
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-
Domain-style sampling:
* primary domain: principal-power quotient comparison maps in commutative algebra, specialized
  later to principal adic completion.
* sampled owner declarations:
  `principalIdeal`,
  `principalPowerIdealQuotientMap`,
  `principalPowerIdeal`,
  `AdicCompletion`,
  `adicCompletion_quotientMap_bijective`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`.
* owner abstraction: the source-facing quotient map is the chapter owner
  `principalPowerIdealQuotientMap`, while its completion comparison is supplied canonically by
  `adicCompletion_quotientMap_bijective` after specializing to `AdicCompletion (principalIdeal f) R`.
* primitive data: the ring `R`, the principal ideal `principalIdeal f`, and the exponent `n : ℕ`.
* derived API: bijectivity of the induced quotient maps, and the completion specialization below.
* triage: `core/canonical` owner = `adicCompletion_quotientMap_bijective` for the ideal powers
  `((Ideal.map _ (principalIdeal f))^n)` on the completion side; the Beauville-Laszlo completion
  statement below is the positive-integer specialization to the principal ideal `(f)`.
-/

section

variable {R : Type u} [CommRing R] (f : R)

-- Proof sketch: this is the canonical adic-completion quotient-map bijectivity theorem applied to
-- the finitely generated principal ideal `(f)`, then specialized through the chapter owner
-- `AdicCompletion (principalIdeal f) R`.
/-- Lemma 15.91.1: for every positive integer `n`, the canonical map
`R / (f)^n → R^∧ / (f)^n R^∧` for the `(f)`-adic completion is bijective. This is the thin
completion-specialized bridge to the canonical `Ideal.quotientMap` owner used by the later
base-change API. -/
theorem principalAdicCompletion_quotientMap_bijective (n : ℕ+) :
    Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R (principalAdicCompletion f)) f n) := by
  let I : Ideal R := principalIdeal f
  let σ : R →+* principalAdicCompletion f := algebraMap R (principalAdicCompletion f)
  let e :
      (principalAdicCompletion f ⧸ Ideal.map σ (I ^ (n : ℕ))) ≃ₐ[R] (R ⧸ I ^ (n : ℕ)) :=
    (Ideal.quotientEquivAlgOfEq R
      (completionIdeal_pow_eq_ker_evalₐ (I := I) (principalIdeal_fg f) n)).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := AdicCompletion.evalₐ I n)
        (AdicCompletion.surjective_evalₐ I n))
  have hmap :
      Ideal.map σ (I ^ (n : ℕ)) = principalPowerIdeal (σ f) n := by
    simp [I, σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
      Set.image_singleton]
  have hq :
      Ideal.quotientMap
        (Ideal.map σ (I ^ (n : ℕ)))
        σ
        Ideal.le_comap_map =
        e.symm.toRingHom := by
    -- Identify the quotient map on generators with the inverse completion quotient equivalence.
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [e, σ]
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (principalAdicCompletion f)) (I ^ (n : ℕ)))
          ((algebraMap R (principalAdicCompletion f)) r) =
        (Ideal.quotientEquivAlgOfEq R
          (completionIdeal_pow_eq_ker_evalₐ (I := I) (principalIdeal_fg f) n).symm)
          ((Ideal.quotientKerAlgEquivOfSurjective
              (f := AdicCompletion.evalₐ I n)
              (AdicCompletion.surjective_evalₐ I n)).symm
            ((Ideal.Quotient.mk (I ^ (n : ℕ))) r))
    rw [← AdicCompletion.evalₐ_of (I := I) n r]
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply
      (hf := AdicCompletion.surjective_evalₐ I n)
      (a := AdicCompletion.of I R r)]
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ (n : ℕ)))
          (AdicCompletion.of I R r) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ (n : ℕ)))
          (AdicCompletion.of I R r)
    rfl
  -- Rewrite the generic completion comparison for `I = (f)` into the principal-power map.
  have htransport :
      principalPowerIdealImageQuotientMap σ f n =
        (Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap (Ideal.map σ (I ^ (n : ℕ))) σ Ideal.le_comap_map) := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap]
    simpa [I, principalPowerIdeal, Ideal.quotientMap_mk] using
      (Ideal.quotientEquivAlgOfEq_mk (R₁ := R) (h := hmap) (x := σ r))
  rw [htransport, hq]
  simpa [RingHom.comp_apply] using
    (Ideal.quotientEquivAlgOfEq R hmap).bijective.comp e.symm.bijective

end
