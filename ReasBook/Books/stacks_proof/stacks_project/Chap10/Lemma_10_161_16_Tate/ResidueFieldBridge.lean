import stacks_proof.stacks_project.Chap10.Lemma_10_161_16_Tate.PrincipalPrimeRoot
import stacks_proof.stacks_project.Chap10.Lemma_10_119_10
import stacks_proof.stacks_project.Chap10.Lemma_10_25_3
universe u

open Ideal
open IsLocalRing
open IntermediateField Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): the residue field at a local ring's maximal ideal agrees
with its ordinary residue field. -/
noncomputable def localMaximalIdealResidueFieldEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): the local maximal-ideal residue-field equivalence sends a
base element to its ordinary residue class. -/
theorem localMaximalIdealResidueFieldEquiv_apply_algebraMap
    (A : Type*) [CommRing A] [IsLocalRing A] (a : A) :
    localMaximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a := by
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (residue A a) by rfl]
  exact (localMaximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): the local maximal-ideal residue-field equivalence is
compatible with the residue-field map induced by a local homomorphism. -/
theorem localMaximalIdealResidueFieldEquiv_comp_residueFieldMap
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (localMaximalIdealResidueFieldEquiv B).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (localMaximalIdealResidueFieldEquiv A).toRingHom := by
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    localMaximalIdealResidueFieldEquiv B
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm (algebraMap A (maximalIdeal A).ResidueField a)) =
      ResidueField.map f
        (localMaximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, localMaximalIdealResidueFieldEquiv_apply_algebraMap,
    localMaximalIdealResidueFieldEquiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: finite generation over maximal-ideal residue
fields transports across a local ring equivalence compatible with the two local maps. -/
lemma moduleFinite_maximalIdealResidueField_of_localEquiv
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    (fB : A →+* B) (fC : A →+* C) [IsLocalHom fB] [IsLocalHom fC]
    (e : B ≃+* C) (hcomp : (e : B →+* C).comp fB = fC)
    (hfin :
      letI : Algebra (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField :=
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) fB
          (IsLocalRing.maximalIdeal_comap fB).symm).toAlgebra
      Module.Finite (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField) :
    letI : Algebra (maximalIdeal A).ResidueField (maximalIdeal C).ResidueField :=
      (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal C) fC
        (IsLocalRing.maximalIdeal_comap fC).symm).toAlgebra
    Module.Finite (maximalIdeal A).ResidueField (maximalIdeal C).ResidueField := by
  letI : Algebra (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField :=
    (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) fB
      (IsLocalRing.maximalIdeal_comap fB).symm).toAlgebra
  letI : Algebra (maximalIdeal A).ResidueField (maximalIdeal C).ResidueField :=
    (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal C) fC
      (IsLocalRing.maximalIdeal_comap fC).symm).toAlgebra
  letI : IsLocalHom (e : B →+* C) := Function.Surjective.isLocalHom _ e.surjective
  let eB : (maximalIdeal B).ResidueField ≃+* ResidueField B :=
    localMaximalIdealResidueFieldEquiv B
  let eC : (maximalIdeal C).ResidueField ≃+* ResidueField C :=
    localMaximalIdealResidueFieldEquiv C
  let eBC : (maximalIdeal B).ResidueField ≃+* (maximalIdeal C).ResidueField :=
    eB.trans ((IsLocalRing.ResidueField.mapEquiv e).trans eC.symm)
  have hcompat :
      RingHom.comp (algebraMap (maximalIdeal A).ResidueField (maximalIdeal C).ResidueField)
          ↑(RingEquiv.refl (maximalIdeal A).ResidueField) =
        RingHom.comp ↑eBC
          (algebraMap (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField) := by
    -- Proof comment: compare the transported scalar maps on residue classes from the source
    -- local ring, where the compatibility hypothesis identifies the two composites.
    apply Ideal.ResidueField.ringHom_ext
    ext a
    change algebraMap (maximalIdeal A).ResidueField (maximalIdeal C).ResidueField
        (algebraMap A (maximalIdeal A).ResidueField a) =
      eBC (algebraMap (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField
        (algebraMap A (maximalIdeal A).ResidueField a))
    apply eC.injective
    have hc : fC a = e (fB a) :=
      (congrArg (fun g : A →+* C => g a) hcomp).symm
    calc
      eC (algebraMap (maximalIdeal A).ResidueField (maximalIdeal C).ResidueField
          (algebraMap A (maximalIdeal A).ResidueField a)) =
          eC (algebraMap C (maximalIdeal C).ResidueField (fC a)) := by
            exact congrArg eC
              (Ideal.ResidueField.map_algebraMap (maximalIdeal A) (maximalIdeal C)
                fC (IsLocalRing.maximalIdeal_comap fC).symm a)
      _ = residue C (fC a) := by
            rw [localMaximalIdealResidueFieldEquiv_apply_algebraMap]
      _ = residue C (e (fB a)) := by
            rw [hc]
      _ = ResidueField.map (e : B →+* C) (residue B (fB a)) := by
            exact (IsLocalRing.ResidueField.map_residue (e : B →+* C) (fB a)).symm
      _ = ResidueField.map (e : B →+* C)
            (eB (algebraMap B (maximalIdeal B).ResidueField (fB a))) := by
            rw [localMaximalIdealResidueFieldEquiv_apply_algebraMap]
      _ = ResidueField.map (e : B →+* C)
            (eB (algebraMap (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField
              (algebraMap A (maximalIdeal A).ResidueField a))) := by
            exact congrArg (fun y : (maximalIdeal B).ResidueField =>
              ResidueField.map (e : B →+* C) (eB y))
              (Ideal.ResidueField.map_algebraMap (maximalIdeal A) (maximalIdeal B)
                fB (IsLocalRing.maximalIdeal_comap fB).symm a).symm
      _ = eC (eBC (algebraMap (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField
          (algebraMap A (maximalIdeal A).ResidueField a))) := by
            simp [eBC, eB, eC]
  letI : Module.Finite (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField := hfin
  -- Proof comment: after the scalar maps are compatible, finite generation transfers across the
  -- identity equivalence on the base residue field and the induced target residue-field equivalence.
  exact Module.Finite.of_equiv_equiv (RingEquiv.refl (maximalIdeal A).ResidueField) eBC hcompat

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: a finite fraction-field extension over a
one-dimensional Noetherian local domain gives a finite maximal-ideal residue-field extension. -/
lemma moduleFinite_maximalIdealResidueField_of_finite_fractionField_extension
    {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
    [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    [IsLocalHom (algebraMap A B)] (hdim : ringKrullDim A = 1) :
    Module.Finite (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField := by
  letI : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨by
      simpa [Ideal.under_def] using
        (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  let P : (maximalIdeal A).primesOver B :=
    Ideal.primesOver.mk (p := maximalIdeal A) (B := B) (maximalIdeal B)
  -- Proof comment: the existing closed-fiber theorem applies to the maximal ideal of `B`,
  -- because locality says it lies over the maximal ideal of `A`.
  simpa [P] using
    (moduleFinite_residueField_of_primeOver_maximalIdeal_of_finite_fractionField_extension
      (R := A) (S := B) hdim P)

omit [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): a prime minimal over a nonzero principal ideal in a
Noetherian domain has prime height `1`. -/
lemma primeHeight_eq_one_of_minimalPrimes_span_singleton_of_nonzero
    {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    {x : S} (hx : x ≠ 0) (q : Ideal S) [q.IsPrime]
    (hq : q ∈ (Ideal.span ({x} : Set S)).minimalPrimes) :
    q.primeHeight = 1 := by
  have hq_le : q.primeHeight ≤ 1 := by
    rw [← Ideal.height_eq_primeHeight]
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span ({x} : Set S)) q hq
  have hq_ne_bot : q ≠ ⊥ := by
    intro hq_bot
    have hxq : x ∈ q := hq.1.2 (Ideal.subset_span (by simp))
    rw [hq_bot, Ideal.mem_bot] at hxq
    exact hx hxq
  have hbot_lt : (⊥ : Ideal S) < q := bot_lt_iff_ne_bot.mpr hq_ne_bot
  have hbot_height : (⊥ : Ideal S).primeHeight = 0 := by
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    simp
  have hq_ge : (1 : ℕ∞) ≤ q.primeHeight := by
    simpa [hbot_height] using
      Ideal.primeHeight_add_one_le_of_lt (I := (⊥ : Ideal S)) (J := q) hbot_lt
  exact le_antisymm hq_le hq_ge

/-- Helper for Lemma 10.161.16 (Tate): after identifying the closed points of prime localizations
with the corresponding prime residue fields, the residue-field map induced by the localized map
agrees with the original prime residue-field map. -/
lemma prime_local_residue_field_map_compat
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hq : p = Ideal.comap (algebraMap A B) q) :
    let f := Localization.localRingHom p q (algebraMap A B) hq
    (localMaximalIdealResidueFieldEquiv (Localization.AtPrime q)).toRingHom.comp
        (Ideal.ResidueField.map
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (Ideal.ResidueField.map p q (algebraMap A B) hq).comp
        (localMaximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom := by
  let f := Localization.localRingHom p q (algebraMap A B) hq
  -- Both maps are the same residue-field morphism, written before and after the canonical
  -- prime-local residue-field identifications.
  simpa [f] using
    (localMaximalIdealResidueFieldEquiv_comp_residueFieldMap (f := f))

/-- Helper for Lemma 10.161.16 (Tate): finite generation over the maximal-ideal residue fields of
prime localizations transports to finite generation over the original prime residue fields. -/
lemma primeLocalization_residueFieldFinite_transport
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hfin :
      let hq : p = Ideal.comap (algebraMap A B) q := Ideal.LiesOver.over (p := p) (P := q)
      let f := Localization.localRingHom p q (algebraMap A B) hq
      letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := f.toAlgebra
      letI : Algebra (maximalIdeal (Localization.AtPrime p)).ResidueField
          (maximalIdeal (Localization.AtPrime q)).ResidueField :=
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p))
          (maximalIdeal (Localization.AtPrime q))
          f
          (IsLocalRing.maximalIdeal_comap f).symm).toAlgebra
      Module.Finite
        (maximalIdeal (Localization.AtPrime p)).ResidueField
        (maximalIdeal (Localization.AtPrime q)).ResidueField) :
    Module.Finite p.ResidueField q.ResidueField := by
  let hq : p = Ideal.comap (algebraMap A B) q := Ideal.LiesOver.over (p := p) (P := q)
  let f := Localization.localRingHom p q (algebraMap A B) hq
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := f.toAlgebra
  letI : Algebra (maximalIdeal (Localization.AtPrime p)).ResidueField
      (maximalIdeal (Localization.AtPrime q)).ResidueField :=
    (Ideal.ResidueField.map
      (maximalIdeal (Localization.AtPrime p))
      (maximalIdeal (Localization.AtPrime q))
      f
      (IsLocalRing.maximalIdeal_comap f).symm).toAlgebra
  letI : Module.Finite (maximalIdeal (Localization.AtPrime p)).ResidueField
      (maximalIdeal (Localization.AtPrime q)).ResidueField := hfin
  let eA : (maximalIdeal (Localization.AtPrime p)).ResidueField ≃+* p.ResidueField := by
    change (maximalIdeal (Localization.AtPrime p)).ResidueField ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime p)
    exact localMaximalIdealResidueFieldEquiv (Localization.AtPrime p)
  let eB : (maximalIdeal (Localization.AtPrime q)).ResidueField ≃+* q.ResidueField := by
    change (maximalIdeal (Localization.AtPrime q)).ResidueField ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime q)
    exact localMaximalIdealResidueFieldEquiv (Localization.AtPrime q)
  have hcompat :
      RingHom.comp (algebraMap p.ResidueField q.ResidueField) ↑eA =
        RingHom.comp ↑eB (algebraMap
          (maximalIdeal (Localization.AtPrime p)).ResidueField
          (maximalIdeal (Localization.AtPrime q)).ResidueField) := by
    -- Proof comment: compatibility is exactly the residue-field map comparison for prime
    -- localizations, with the direction adjusted for `Module.Finite.of_equiv_equiv`.
    simpa [eA, eB, f, hq] using
      (prime_local_residue_field_map_compat (A := A) (B := B) p q hq).symm
  -- Proof comment: once the scalar maps are compatible, finite generation transfers across the two
  -- residue-field equivalences without unfolding either residue-field construction again.
  exact Module.Finite.of_equiv_equiv eA eB hcompat

/-- Helper for Lemma 10.161.16 (Tate): the residue field `κ(q)` inherits its
`R / (x)`-algebra structure from the composite `R / (x) → κ((x)) → κ(q)`. -/
noncomputable abbrev principal_quotient_residueField_algebra
    {M : Type u} [Field M] [Algebra R M]
    (x : R)
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    Algebra (R ⧸ Ideal.span ({x} : Set R)) q.1.ResidueField :=
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  ((Ideal.ResidueField.map p0 q.1 (algebraMap R S) q.2.2.over).comp
    (algebraMap (R ⧸ p0) p0.ResidueField)).toAlgebra

/-- Helper for Lemma 10.161.16 (Tate): the quotient map `S / q → κ(q)` is compatible with the
canonical `R / (x)`-algebra structures. -/
lemma principal_quotient_to_residueField_isScalarTower
    {M : Type u} [Field M] [Algebra R M]
    (x : R)
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let S := integralClosure R M
    letI : Algebra (R ⧸ p0) (S ⧸ q.1) := Ideal.Quotient.algebraOfLiesOver q.1 p0
    letI : Algebra (R ⧸ p0) q.1.ResidueField :=
      principal_quotient_residueField_algebra (R := R) (M := M) x q
    IsScalarTower (R ⧸ p0) (S ⧸ q.1) q.1.ResidueField := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  letI : Algebra (R ⧸ p0) (S ⧸ q.1) := Ideal.Quotient.algebraOfLiesOver q.1 p0
  letI : Algebra (R ⧸ p0) q.1.ResidueField :=
    principal_quotient_residueField_algebra (R := R) (M := M) x q
  -- Proof comment: both `R / (x)`-actions on `κ(q)` send a quotient class `r mod (x)` to the
  -- residue class of the image of `r` in the normalization.
  refine IsScalarTower.of_algebraMap_eq fun z ↦ ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.algebraMap_quotient_residueField_mk]
  change
    Ideal.ResidueField.map p0 q.1 (algebraMap R S) q.2.2.over
        (algebraMap (R ⧸ p0) p0.ResidueField (Ideal.Quotient.mk p0 z)) =
      algebraMap S q.1.ResidueField (algebraMap R S z)
  exact Ideal.ResidueField.map_algebraMap p0 q.1 (algebraMap R S) q.2.2.over z

/-- Helper for Lemma 10.161.16 (Tate): the explicit composite
`R / (x) → κ((x)) → κ(q)` is injective. -/
lemma principal_quotient_to_prime_residueField_map_injective
    {M : Type u} [Field M] [Algebra R M]
    (x : R)
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let S := integralClosure R M
    let f : (R ⧸ p0) →+* q.1.ResidueField :=
      (Ideal.ResidueField.map p0 q.1 (algebraMap R S) q.2.2.over).comp
        (algebraMap (R ⧸ p0) p0.ResidueField)
    Function.Injective f := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  letI : p0.IsPrime := by
    simpa [p0] using (inferInstance : (Ideal.span ({x} : Set R)).IsPrime)
  let f :
      (R ⧸ p0) →+* q.1.ResidueField :=
    (Ideal.ResidueField.map p0 q.1 (algebraMap R S) q.2.2.over).comp
      (algebraMap (R ⧸ p0) p0.ResidueField)
  -- Proof comment: the quotient-domain map factors through the prime residue field `κ((x))`,
  -- so injectivity is inherited from a composite of field maps.
  exact (Ideal.ResidueField.map p0 q.1 (algebraMap R S) q.2.2.over).injective.comp
    (IsFractionRing.injective (R ⧸ p0) p0.ResidueField)

/-- Helper for Lemma 10.161.16 (Tate): if `L` is a field extension of the fraction field of a
domain `A`, then the induced map from a prime localization `A_p` into `L` is injective. -/
lemma localizationAtPrime_algebraMap_injective_to_fractionField_extension
    {A : Type*} [CommRing A] [IsDomain A]
    {p : Ideal A} [p.IsPrime]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower A (Localization.AtPrime p) L] :
    Function.Injective (algebraMap (Localization.AtPrime p) L) := by
  refine IsLocalization.injective_of_map_algebraMap_zero
      (M := p.primeCompl) (S := Localization.AtPrime p)
      (f := algebraMap (Localization.AtPrime p) L) ?_
  intro a ha
  have haL : algebraMap A L a = 0 := by
    -- Proof comment: rewrite the localized base element through the ambient scalar tower.
    calc
      algebraMap A L a =
          algebraMap (Localization.AtPrime p) L (algebraMap A (Localization.AtPrime p) a) := by
            exact IsScalarTower.algebraMap_apply A (Localization.AtPrime p) L a
      _ = 0 := ha
  have ha_zero : a = 0 := by
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    -- Proof comment: compare the image of `a` in `L` through the fraction-field model `K`.
    simpa [IsScalarTower.algebraMap_apply A K L] using haL
  -- Proof comment: once `a = 0` in the base ring, its localization class also vanishes.
  simpa [ha_zero]

/-- Helper for Lemma 10.161.16 (Tate): for any chosen fraction-field model `K` of a domain `A`,
the canonical map `Frac(A) → L` is the transport of the map `K → L` through
`FractionRing.algEquiv A K`. -/
lemma fraction_field_model_liftAlgebra_eq_transport_comp
    {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    (hAL_injective : Function.Injective (algebraMap A L)) :
    letI : FaithfulSMul A L :=
      (faithfulSMul_iff_algebraMap_injective A L).2 hAL_injective
    algebraMap (FractionRing A) L =
      RingHom.comp (algebraMap K L) ↑(FractionRing.algEquiv A K) := by
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2 hAL_injective
  rw [FractionRing.algebraMap_liftAlgebra]
  refine IsFractionRing.lift_unique hAL_injective ?_
  intro a
  -- Proof comment: on elements of `A`, the transported map is just the original tower map
  -- `A → K → L`.
  change algebraMap K L ((FractionRing.algEquiv A K) (algebraMap A (FractionRing A) a)) =
    algebraMap A L a
  rw [AlgEquiv.commutes]
  simpa using (IsScalarTower.algebraMap_apply A K L a).symm

/-- Helper for Lemma 10.161.16 (Tate): any field extension of the fraction field of a domain is
already injective on the base domain. -/
lemma algebraMap_injective_to_fractionField_extension
    {K : Type*} [Field K] [Algebra R K] [Algebra (FractionRing R) K]
    [IsScalarTower R (FractionRing R) K] :
    Function.Injective (algebraMap R K) := by
  intro a b hab
  apply IsFractionRing.injective R (FractionRing R)
  apply (algebraMap (FractionRing R) K).injective
  -- Proof comment: compare the images in `K` after rewriting the scalar tower
  -- `R → FractionRing R → K`.
  simpa [IsScalarTower.algebraMap_apply R (FractionRing R) K] using hab

/-- Helper for Lemma 10.161.16 (Tate): for a prime ideal of a domain, every element of the prime
complement maps to a non-zero-divisor in any field extension of the fraction field. -/
lemma primeCompl_le_comap_nonZeroDivisors_of_fractionField_extension
    (p : Ideal R) [p.IsPrime]
    {K : Type*} [Field K] [Algebra R K] [Algebra (FractionRing R) K]
    [IsScalarTower R (FractionRing R) K] :
    p.primeCompl ≤ Submonoid.comap (algebraMap R K) (nonZeroDivisors K) := by
  exact
    p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
        (algebraMap R K)
        (algebraMap_injective_to_fractionField_extension (R := R) (K := K)))

/-- Helper for Lemma 10.161.16 (Tate): localizing the normalization at the unique prime over
`(x)` gives a finite residue-field extension over the residue field at `(x)`. -/
lemma principal_prime_localization_dim_one
    (x : R) (hx : x ≠ 0)
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime] :
    ringKrullDim (Localization.AtPrime (Ideal.span ({x} : Set R))) = 1 := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  have hp0_min : p0 ∈ p0.minimalPrimes := by
    -- Proof comment: the principal ideal `(x)` is itself prime, hence minimal over itself.
    have hp0_singleton : p0.minimalPrimes = {p0} :=
      Ideal.minimalPrimes_eq_subsingleton_self (I := p0)
    simpa [hp0_singleton]
  have hp0_height : p0.primeHeight = 1 := by
    -- Proof comment: apply the principal-ideal height-one theorem to the prime `(x)`.
    simpa [p0] using
      primeHeight_eq_one_of_minimalPrimes_span_singleton_of_nonzero
        (S := R) (x := x) hx p0 hp0_min
  -- Proof comment: the localization dimension is the height of the localized prime.
  calc
    ringKrullDim (Localization.AtPrime p0) = p0.height := by
      simpa [p0] using
        (IsLocalization.AtPrime.ringKrullDim_eq_height p0 (Localization.AtPrime p0))
    _ = 1 := by
      simpa [Ideal.height_eq_primeHeight] using hp0_height

/-- Helper for Lemma 10.161.16 (Tate): finite-dimensionality over `FractionRing R` transports to
the fraction field of any prime localization `R_p`. -/
lemma localized_base_fraction_field_finite
    {p : Ideal R} [p.IsPrime]
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    [Algebra (Localization.AtPrime p) M] [IsScalarTower R (Localization.AtPrime p) M]
    [FaithfulSMul (Localization.AtPrime p) M] :
    FiniteDimensional (FractionRing (Localization.AtPrime p)) M := by
  let Rp := Localization.AtPrime p
  let hlocal : p.primeCompl ≤ nonZeroDivisors R := p.primeCompl_le_nonZeroDivisors
  have hRM_injective : Function.Injective (algebraMap R M) := by
    -- Proof comment: the ambient field extension is already injective on the base domain `R`.
    exact algebraMap_injective_to_fractionField_extension (R := R) (K := M)
  letI : FaithfulSMul R M := (faithfulSMul_iff_algebraMap_injective R M).2 hRM_injective
  let e : FractionRing R ≃+* FractionRing Rp :=
    (fractionRing_localization_equiv R p.primeCompl hlocal).toRingEquiv
  have hcompat :
      RingHom.comp (algebraMap (FractionRing Rp) M) ↑e =
        RingHom.comp ↑(RingEquiv.refl M) (algebraMap (FractionRing R) M) := by
    -- Proof comment: both maps from `Frac(R)` to `M` are determined by their values on `R`,
    -- and `fractionRing_localization_equiv` preserves those values.
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    have hcomm : e (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing Rp) r := by
      simpa [Rp, e] using
        (fractionRing_localization_equiv R p.primeCompl hlocal).commutes r
    calc
      ((algebraMap (FractionRing Rp) M).comp ↑e) (algebraMap R (FractionRing R) r) =
          algebraMap (FractionRing Rp) M (algebraMap R (FractionRing Rp) r) := by
            simpa [RingHom.comp_apply] using congrArg (algebraMap (FractionRing Rp) M) hcomm
      _ = algebraMap R M r := by
        simpa [Rp] using (IsScalarTower.algebraMap_apply R (FractionRing Rp) M r).symm
      _ = (((RingEquiv.refl M : M ≃+* M).toRingHom).comp (algebraMap (FractionRing R) M))
          (algebraMap R (FractionRing R) r) := by
        simpa [RingHom.comp_apply] using
          (IsScalarTower.algebraMap_apply R (FractionRing R) M r)
  -- Proof comment: transfer the known finite-dimensional `Frac(R)`-vector-space structure on
  -- `M` across the canonical fraction-field equivalence for `R_p`.
  exact Module.Finite.of_equiv_equiv e (RingEquiv.refl M) hcompat

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: if a field `L` is a finite-dimensional model of
`Frac(A)` and is also a fraction field of a domain `B`, then `Frac(B)` is finite-dimensional over
`Frac(A)` after transporting the scalar structure through `L`. -/
lemma fractionRing_finiteDimensional_of_isFractionRing
    {A B L : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field L] [Algebra A L] [FaithfulSMul A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L]
    [Algebra B L] [IsFractionRing B L] :
    letI : Algebra (FractionRing A) (FractionRing B) :=
      ((FractionRing.algEquiv B L).symm.toRingHom.comp
        (algebraMap (FractionRing A) L)).toAlgebra
    letI : Module (FractionRing A) (FractionRing B) := Algebra.toModule
    FiniteDimensional (FractionRing A) (FractionRing B) := by
  letI : Algebra (FractionRing A) (FractionRing B) :=
    ((FractionRing.algEquiv B L).symm.toRingHom.comp
      (algebraMap (FractionRing A) L)).toAlgebra
  letI : Module (FractionRing A) (FractionRing B) := Algebra.toModule
  let e : L ≃+* FractionRing B := (FractionRing.algEquiv B L).symm.toRingEquiv
  have hcompat :
      RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
          ↑(RingEquiv.refl (FractionRing A)) =
        RingHom.comp ↑e (algebraMap (FractionRing A) L) := by
    -- Proof comment: the transported `Frac(A)`-algebra map was defined as this composite.
    ext z
    rfl
  exact Module.Finite.of_equiv_equiv (RingEquiv.refl (FractionRing A)) e hcompat

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: the transported fraction-field algebra structure is
compatible with the original `A → B` map. -/
lemma fractionRing_isScalarTower_of_isFractionRing
    {A B L : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field L] [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    [FaithfulSMul A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [IsFractionRing B L] :
    letI : Algebra (FractionRing A) (FractionRing B) :=
      ((FractionRing.algEquiv B L).symm.toRingHom.comp
        (algebraMap (FractionRing A) L)).toAlgebra
    letI : Module (FractionRing A) (FractionRing B) := Algebra.toModule
    IsScalarTower A (FractionRing A) (FractionRing B) := by
  letI : Algebra (FractionRing A) (FractionRing B) :=
    ((FractionRing.algEquiv B L).symm.toRingHom.comp
      (algebraMap (FractionRing A) L)).toAlgebra
  letI : Module (FractionRing A) (FractionRing B) := Algebra.toModule
  let e : FractionRing B ≃+* L := (FractionRing.algEquiv B L).toRingEquiv
  refine @IsScalarTower.of_algebraMap_eq A (FractionRing A) (FractionRing B)
    _ _ _ inferInstance inferInstance inferInstance ?_
  intro a
  -- Proof comment: apply the fraction-field equivalence to reduce the tower identity to the
  -- already-known scalar tower `A → B → L`.
  apply e.injective
  calc
    e (algebraMap A (FractionRing B) a) =
        algebraMap B L (algebraMap A B a) := by
          rw [IsScalarTower.algebraMap_apply A B (FractionRing B)]
          exact (FractionRing.algEquiv B L).commutes (algebraMap A B a)
    _ = algebraMap A L a := by
          exact (IsScalarTower.algebraMap_apply A B L a).symm
    _ = algebraMap (FractionRing A) L (algebraMap A (FractionRing A) a) := by
          exact IsScalarTower.algebraMap_apply A (FractionRing A) L a
    _ = e (algebraMap (FractionRing A) (FractionRing B)
          (algebraMap A (FractionRing A) a)) := by
          simp [e, RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.161.16 (Tate): an element of the quotient by a prime ideal remains
integral after mapping into the corresponding residue field. -/
lemma quotient_residue_class_isIntegral_in_residueField
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B]
    (q : Ideal B) [q.IsPrime] (z : B ⧸ q) :
    IsIntegral A (algebraMap (B ⧸ q) q.ResidueField z) := by
  -- Proof comment: the quotient is integral over `A`, and integrality persists after applying
  -- the canonical fraction-field map to the residue field.
  exact (Algebra.IsIntegral.isIntegral z).map
    (IsScalarTower.toAlgHom A (B ⧸ q) q.ResidueField)

end
