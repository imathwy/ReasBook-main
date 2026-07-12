import Mathlib
import StacksProject_2024.Chap10.Lemma_10_17_6
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap15.Lemma_15_91_1

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped PrimeSpectrum

universe u v

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
* primary domain: commutative algebra of prime spectra under quotient and localization;
* sampled owner declarations:
  `principalIdealQuotientMap`,
  `PrimeSpectrum.comap`,
  `PrimeSpectrum.localization_away_comap_range`,
  `principalAdicCompletion_quotientMap_bijective`;
* best owner abstraction: the chapter owner `principalIdealQuotientMap` for reduction modulo
  `(f)`, together with the canonical prime-spectrum maps `PrimeSpectrum.comap`;
* primitive data: a ring map `R → R'` and an element `f : R`;
* derived API: the surjectivity of
  `Spec R' ⊔ Spec R_f → Spec R` under the quotient-map bijectivity hypothesis;
* triage: `source-facing` = the surjectivity statement below, `core/canonical` =
  `principalIdealQuotientMap` and `PrimeSpectrum.comap`, `bridge/view` =
  the completion specialization.
-/

-- Proof sketch: decompose `Spec(R)` as `V(f) ∪ D(f)`. The quotient-bijectivity hypothesis
-- identifies the image of `Spec(R')` with `V(f)` via the canonical quotient map
-- `principalIdealQuotientMap (algebraMap R R') f rfl : R ⧸ (f) →+* R' ⧸ (f R')`,
-- while `PrimeSpectrum.localization_away_comap_range` identifies the localization summand with
-- `D(f)`.
/-- Helper for Lemma 15.91.3: the quotient-bijectivity hypothesis lifts every prime in `V(f)` to
`Spec(R')`. -/
theorem exists_prime_over_zeroLocus_of_principalIdealQuotientMap_bijective
    {R' : Type v} [CommRing R'] [Algebra R R']
    (f : R)
    (hquot : Function.Bijective (principalIdealQuotientMap (algebraMap R R') f rfl))
    {p : PrimeSpectrum R}
    (hp : p ∈ PrimeSpectrum.zeroLocus (principalIdeal f : Set R)) :
    ∃ q : PrimeSpectrum R', PrimeSpectrum.comap (algebraMap R R') q = p := by
  let qmap := principalIdealQuotientMap (algebraMap R R') f rfl
  let x : PrimeSpectrum (R ⧸ principalIdeal f) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (principalIdeal f)).symm ⟨p, hp⟩
  have hsurj : Function.Surjective (PrimeSpectrum.comap qmap) :=
    (PrimeSpectrum.isHomeomorph_comap_of_bijective hquot).bijective.surjective
  obtain ⟨x', hx'⟩ := hsurj x
  let q : PrimeSpectrum R' :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
      (principalIdeal (algebraMap R R' f)) x').1
  -- Compare the two ways of passing from `R` to the quotient `R' / (f)R'`.
  have hq :
      PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal (algebraMap R R' f))) x' = q := by
    simpa [q] using
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply
        (principalIdeal (algebraMap R R' f)) x').symm
  have hp' :
      PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal f)) x = p := by
    have hx :
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (principalIdeal f) x).1 = p := by
      simpa [x] using congrArg Subtype.val
        ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
          (principalIdeal f)).apply_symm_apply ⟨p, hp⟩)
    rwa [Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply] at hx
  have hcomp :
      (Ideal.Quotient.mk (principalIdeal (algebraMap R R' f))).comp (algebraMap R R') =
        qmap.comp (Ideal.Quotient.mk (principalIdeal f)) := by
    ext r
    simp [qmap, principalIdealQuotientMap]
  refine ⟨q, ?_⟩
  -- Functoriality of `Spec` reduces the claim to the lifted quotient prime `x'`.
  calc
    PrimeSpectrum.comap (algebraMap R R') q
        = PrimeSpectrum.comap (algebraMap R R')
            (PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal (algebraMap R R' f))) x') := by
            rw [hq]
    _ = PrimeSpectrum.comap
          ((Ideal.Quotient.mk (principalIdeal (algebraMap R R' f))).comp (algebraMap R R')) x' := by
          rw [← PrimeSpectrum.comap_comp_apply]
    _ = PrimeSpectrum.comap (qmap.comp (Ideal.Quotient.mk (principalIdeal f))) x' := by
          rw [hcomp]
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal f))
          (PrimeSpectrum.comap qmap x') := by
          rw [PrimeSpectrum.comap_comp_apply]
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal f)) x := by
          rw [hx']
    _ = p := hp'

/-- Lemma 15.91.3: if `R → R'` induces an isomorphism `R / (f) → R' / (f)R'`, then the induced
map `Spec(R') ⊔ Spec(R_f) → Spec(R)` is surjective. -/
theorem primeSpectrum_sum_surjective_of_quotientByPrincipalIdeal_bijective
    {R' : Type v} [CommRing R'] [Algebra R R']
    (f : R)
    (hquot : Function.Bijective (principalIdealQuotientMap (algebraMap R R') f rfl)) :
    Function.Surjective
      (Sum.elim
        (comap (algebraMap R R'))
        (comap (algebraMap R (Localization.Away f)))) := by
  intro p
  by_cases hf : f ∈ p.asIdeal
  · -- On the closed part `V(f)`, lift `p` through the quotient comparison hypothesis.
    have hp_zero : p ∈ PrimeSpectrum.zeroLocus (principalIdeal f : Set R) := by
      exact (PrimeSpectrum.mem_zeroLocus p (principalIdeal f : Set R)).2 <| by
        simpa [principalIdeal] using (Ideal.span_singleton_le_iff_mem p.asIdeal).2 hf
    obtain ⟨q, hq⟩ :=
      exists_prime_over_zeroLocus_of_principalIdealQuotientMap_bijective
        (R := R) (R' := R') f hquot hp_zero
    exact ⟨Sum.inl q, hq⟩
  · -- On the open part `D(f)`, use the localization-away homeomorphism.
    let p' : PrimeSpectrum (Localization.Away f) :=
      (primeSpectrum_localizationAway_homeomorph_D f).symm
        ⟨p, (PrimeSpectrum.mem_basicOpen f p).2 hf⟩
    refine ⟨Sum.inr p', ?_⟩
    have hp' :
        (primeSpectrum_localizationAway_homeomorph_D f p').1 = p := by
      simpa [p'] using congrArg Subtype.val
        ((primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply
          ⟨p, (PrimeSpectrum.mem_basicOpen f p).2 hf⟩)
    simpa [primeSpectrum_localizationAway_homeomorph_D_apply] using hp'

-- Proof sketch: apply
-- `primeSpectrum_sum_surjective_of_quotientByPrincipalIdeal_bijective` with
-- `R' = principalAdicCompletion f`; Lemma `15.91.1` supplies the quotient
-- bijectivity assumption.
/-- Helper for Lemma 15.91.3: the first principal-power ideal is the principal ideal itself. -/
theorem principalPowerIdeal_one_eq_principalIdeal (x : R) :
    principalPowerIdeal x 1 = principalIdeal x := by
  -- Normalize the first power so later quotient transports use a canonical ideal equality.
  simp [principalPowerIdeal]

/-- Helper for Lemma 15.91.3: quotienting modulo `(x)` is the conjugate of quotienting modulo
`(x)^1` by the canonical quotient equivalences. -/
theorem principalIdealQuotientMap_eq_conj_principalPowerIdealImageQuotientMap_one
    {S : Type v} [CommRing S] (σ : R →+* S) (x : R) :
    principalIdealQuotientMap σ x rfl =
      ((Ideal.quotEquivOfEq
          (principalPowerIdeal_one_eq_principalIdeal (R := S) (σ x))).toRingHom).comp
        ((principalPowerIdealImageQuotientMap σ x 1).comp
          ((Ideal.quotEquivOfEq
            (principalPowerIdeal_one_eq_principalIdeal (R := R) x).symm).toRingHom)) := by
  -- Compare both quotient maps after precomposing with the source quotient generator.
  apply Ideal.Quotient.ringHom_ext
  ext r
  -- The source generator first moves across the source equivalence, then across the powered
  -- quotient map, and finally across the target equivalence.
  simp [principalIdealQuotientMap, principalPowerIdealImageQuotientMap,
    principalPowerIdealQuotientMap, Ideal.quotientMap_mk, RingHom.comp_apply]

/-- Helper for Lemma 15.91.3: the completion comparison on principal-power quotients at exponent
`1` is exactly the quotient map modulo `(f)`. -/
theorem completion_principalIdealQuotientMap_bijective (f : R) :
    Function.Bijective
      (principalIdealQuotientMap (algebraMap R (principalAdicCompletion f)) f rfl) := by
  -- Route correction: avoid heterogeneous transport inside `Function.Bijective` by conjugating
  -- the `n = 1` powered quotient map with quotient equivalences on source and target.
  let eR : R ⧸ principalPowerIdeal f 1 ≃+* R ⧸ principalIdeal f :=
    Ideal.quotEquivOfEq (principalPowerIdeal_one_eq_principalIdeal (R := R) f)
  let eS :
      principalAdicCompletion f ⧸
          principalPowerIdeal ((algebraMap R (principalAdicCompletion f)) f) 1 ≃+*
        principalAdicCompletion f ⧸
          principalIdeal ((algebraMap R (principalAdicCompletion f)) f) :=
    Ideal.quotEquivOfEq
      (principalPowerIdeal_one_eq_principalIdeal
        (R := principalAdicCompletion f) ((algebraMap R (principalAdicCompletion f)) f))
  have hpow :
      Function.Bijective
        (principalPowerIdealImageQuotientMap
          (algebraMap R (principalAdicCompletion f)) f 1) :=
    principalAdicCompletion_quotientMap_bijective (R := R) (f := f) 1
  -- Rewrite the desired quotient map as the conjugate of the powered `n = 1` map.
  rw [principalIdealQuotientMap_eq_conj_principalPowerIdealImageQuotientMap_one
    (R := R) (S := principalAdicCompletion f) (σ := algebraMap R (principalAdicCompletion f))
    (x := f)]
  -- Bijectivity is preserved under composition with quotient equivalences.
  simpa [eR, eS, RingHom.comp_apply] using
    eS.bijective.comp (hpow.comp eR.symm.bijective)

/-- The `(f)`-adic completion and the localization away from `f` cover `Spec(R)`. -/
theorem primeSpectrum_completion_sum_surjective (f : R) :
    Function.Surjective
      (Sum.elim
        (comap (algebraMap R (principalAdicCompletion f)))
        (comap (algebraMap R (Localization.Away f)))) := by
  -- Apply the general surjectivity statement to the completion ring.
  exact primeSpectrum_sum_surjective_of_quotientByPrincipalIdeal_bijective
    (R := R) (R' := principalAdicCompletion f) f
    (completion_principalIdealQuotientMap_bijective (R := R) f)

end
