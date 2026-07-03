import Mathlib
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_54_5 (from Chap10) -/
universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- Helper for Lemma 10.54.5: a surjective ring homomorphism is already a quotient map, so it is
trivially a localization of a quotient. -/
private theorem isLocalizationOfQuotient_of_surjective {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    RingHom.IsLocalizationOfQuotient f := by
  let e : A ⧸ RingHom.ker f ≃+* B := RingHom.quotientKerEquivOfSurjective hf
  let M : Submonoid (A ⧸ RingHom.ker f) := IsUnit.submonoid _
  letI : Algebra (A ⧸ RingHom.ker f) B := e.toRingHom.toAlgebra
  letI : IsLocalization M (A ⧸ RingHom.ker f) := IsLocalization.at_units _ fun _ hx ↦ hx
  let eAlg : (A ⧸ RingHom.ker f) ≃ₐ[A ⧸ RingHom.ker f] B :=
    AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  letI : IsLocalization M B := IsLocalization.isLocalization_of_algEquiv M eAlg
  -- Package the quotient witness and then identify it with the given surjective map.
  refine ⟨RingHom.ker f, inferInstance, M, inferInstance, ?_⟩
  ext x
  simpa [M, e, RingHom.algebraMap_toAlgebra] using
    (RingHom.quotientKerEquivOfSurjective_apply_mk (f := f) hf x)

/-- Helper for Lemma 10.54.5: surjectivity of the induced map on prime localizations remains valid
when the source and target rings lie in different universes. -/
private theorem surjective_localRingHom_of_surjective_univ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f) (P : Ideal B)
    [P.IsPrime] :
    Function.Surjective (Localization.localRingHom (P.comap f) P f rfl) := by
  -- Rebuild the standard proof directly so no same-universe wrapper is required.
  intro x
  rcases IsLocalization.exists_mk'_eq P.primeCompl x with ⟨b, s, rfl⟩
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨t, ht⟩ := hf s.1
  refine ⟨IsLocalization.mk' (M := (Ideal.comap f P).primeCompl)
      (Localization.AtPrime (Ideal.comap f P)) a ⟨t, ?_⟩, ?_⟩
  · change f t ∈ P.primeCompl
    simpa [ht] using s.2
  · rw [Localization.localRingHom_mk']
    simp [ht]

/-- Helper for Lemma 10.54.5: an essentially finite type local map can first be rewritten as a
surjective map from a prime localization of a finite polynomial ring. -/
private theorem exists_prime_localized_polynomial_presentation
    (φ : R →+* S) (hφ : φ.EssFiniteType) :
    ∃ (n : ℕ) (q : PrimeSpectrum (MvPolynomial (Fin n) R))
      (ψ : Localization.AtPrime q.asIdeal →+* S),
        Function.Surjective ψ ∧
          RingHom.IsLocalizationOfQuotient ψ ∧
          φ = ψ.comp (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  classical
  letI := φ.toAlgebra
  letI : Algebra.EssFiniteType R S := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hφ
  let B₀ : Subalgebra R S := Algebra.EssFiniteType.subalgebra R S
  let M₀ : Submonoid B₀ := Algebra.EssFiniteType.submonoid R S
  let p : Ideal B₀ := Ideal.comap (algebraMap B₀ S) (maximalIdeal S)
  letI : p.IsPrime := Ideal.comap_isPrime (algebraMap B₀ S) (maximalIdeal S)
  letI : (maximalIdeal S).LiesOver p := ⟨rfl⟩
  have hSat :
      B₀.saturation ((maximalIdeal S).primeCompl ⊓ B₀.toSubmonoid) (by
        intro x hx
        exact hx.2) = ⊤ := by
    -- Every element of `S` is represented by a numerator in the witness subalgebra and a
    -- denominator that is already a unit in `S`, hence outside the maximal ideal.
    rw [eq_top_iff]
    intro x hx
    rcases IsLocalization.exists_mk'_eq M₀ x with ⟨a, t, rfl⟩
    rw [Subalgebra.mem_saturation_iff]
    have ht_unit : IsUnit (algebraMap B₀ S (t : B₀)) := by
      exact t.2
    have ht_mem : ((t : B₀) : S) ∈ (maximalIdeal S).primeCompl := by
      change ((t : B₀) : S) ∉ maximalIdeal S
      simpa [IsLocalRing.notMem_maximalIdeal] using ht_unit
    refine ⟨((t : B₀) : S), ⟨ht_mem, (t : B₀).2⟩, ?_⟩
    change algebraMap B₀ S (t : B₀) * IsLocalization.mk' S a t ∈ B₀
    -- Multiplying by the chosen denominator clears the fraction back into the subalgebra.
    rw [IsLocalization.mk'_spec' (S := S)]
    exact a.2
  have hlocBij :
      Function.Bijective
        (Localization.localRingHom p (maximalIdeal S) (algebraMap B₀ S) rfl) := by
    -- The local ring `S` is exactly the localization of the finite type witness subalgebra at the
    -- prime under its maximal ideal.
    exact Localization.localRingHom_bijective_of_saturated_inf_eq_top
      (R := R) (S := S) (s := B₀) (P := maximalIdeal S) hSat p
  obtain ⟨n, π, hπsurj⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B₀)).mp
      (inferInstance : Algebra.FiniteType R B₀)
  have hπsurj' : Function.Surjective π.toRingHom := hπsurj
  let q : PrimeSpectrum (MvPolynomial (Fin n) R) :=
    ⟨Ideal.comap π.toRingHom p, Ideal.comap_isPrime π.toRingHom p⟩
  let ψq₀ : Localization.AtPrime q.asIdeal →+* Localization.AtPrime p :=
    Localization.localRingHom q.asIdeal p π.toRingHom rfl
  letI : IsLocalization (maximalIdeal S).primeCompl S :=
    IsLocalization.at_units (maximalIdeal S).primeCompl fun x hx ↦
      (IsLocalRing.notMem_maximalIdeal).mp hx
  let eS : Localization.AtPrime (maximalIdeal S) ≃+* S :=
    (IsLocalization.algEquiv (maximalIdeal S).primeCompl
      (Localization.AtPrime (maximalIdeal S)) S).toRingEquiv
  let ψp : Localization.AtPrime p →+* S :=
    eS.toRingHom.comp (Localization.localRingHom p (maximalIdeal S) (algebraMap B₀ S) rfl)
  let ψ : Localization.AtPrime q.asIdeal →+* S := ψp.comp ψq₀
  have hψp_surj : Function.Surjective ψp := eS.surjective.comp hlocBij.surjective
  have hψq₀_surj : Function.Surjective ψq₀ := by
    -- The finite polynomial presentation remains surjective after localizing at `q`.
    simpa [ψq₀] using
      surjective_localRingHom_of_surjective_univ (f := π.toRingHom) hπsurj' p
  have hψsurj : Function.Surjective ψ := hψp_surj.comp hψq₀_surj
  have hψ : RingHom.IsLocalizationOfQuotient ψ :=
    isLocalizationOfQuotient_of_surjective ψ hψsurj
  refine ⟨n, q, ψ, hψsurj, hψ, ?_⟩
  -- On the image of `R`, both factorizations are the structural map `φ`.
  ext x
  have hq0x :
      ψq₀ (algebraMap R (Localization.AtPrime q.asIdeal) x) =
        algebraMap B₀ (Localization.AtPrime p) (algebraMap R B₀ x) := by
    change
      (Localization.localRingHom q.asIdeal p π.toRingHom rfl)
          (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime q.asIdeal)
            (MvPolynomial.C x)) =
        algebraMap B₀ (Localization.AtPrime p) (algebraMap R B₀ x)
    rw [Localization.localRingHom_to_map]
    simpa using congrArg (algebraMap B₀ (Localization.AtPrime p)) (π.commutes x)
  have hpX :
      ψp (algebraMap B₀ (Localization.AtPrime p) (algebraMap R B₀ x)) = φ x := by
    change
      eS
          ((Localization.localRingHom p (maximalIdeal S) (algebraMap B₀ S) rfl)
            (algebraMap B₀ (Localization.AtPrime p) (algebraMap R B₀ x))) = φ x
    rw [Localization.localRingHom_to_map]
    simp [eS, RingHom.algebraMap_toAlgebra]
  calc
    φ x = ψp (algebraMap B₀ (Localization.AtPrime p) (algebraMap R B₀ x)) := hpX.symm
    _ = ψp (ψq₀ (algebraMap R (Localization.AtPrime q.asIdeal) x)) := by rw [hq0x]

/-- Helper for Lemma 10.54.5: if the prime-localized polynomial presentation already meets the
closed fiber over `maximalIdeal R`, then it extends to a maximal ideal lying over
`maximalIdeal R`. -/
private theorem exists_maximal_over_maximalIdeal_of_not_top {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (hq : q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) ≠ ⊤) :
    ∃ m : MaximalSpectrum (MvPolynomial (Fin n) R),
      q.asIdeal ≤ m.asIdeal ∧ Ideal.comap MvPolynomial.C m.asIdeal = maximalIdeal R := by
  obtain ⟨m, hmMax, hsum⟩ := Ideal.exists_le_maximal
    (q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R)) hq
  refine ⟨⟨m, hmMax⟩, ?_, ?_⟩
  · -- The chosen maximal ideal contains the original prime.
    exact (le_sup_left : q.asIdeal ≤ q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R)).trans
      hsum
  · have hmap : Ideal.map MvPolynomial.C (maximalIdeal R) ≤ m := le_trans
      (le_sup_right : Ideal.map MvPolynomial.C (maximalIdeal R) ≤
        q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R))
      hsum
    have hle : maximalIdeal R ≤ Ideal.comap MvPolynomial.C m := by
      exact (Ideal.map_le_iff_le_comap).mp hmap
    letI : (Ideal.comap MvPolynomial.C m).IsPrime := Ideal.comap_isPrime MvPolynomial.C m
    -- In a local ring every prime ideal lies below the maximal ideal, so containment forces
    -- equality with `maximalIdeal R`.
    exact le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime (Ideal.comap MvPolynomial.C m)) hle

/-- Helper for Lemma 10.54.5: if `S` is already a localization of a quotient of `A_q`, then after
localizing the source further at a larger prime `m`, it is still a localization of a quotient.
This is the quotient-localization transport needed in the easy branch. -/
private noncomputable def source_localization_atPrime_map_algEquiv
    {A : Type u} [CommRing A] {q m q' : Ideal A} [q.IsPrime] [m.IsPrime] [q'.IsPrime]
    (hq' :
      q' = Ideal.comap (algebraMap A (Localization m.primeCompl))
        (Ideal.map (algebraMap A (Localization.AtPrime m)) q))
    [(Ideal.map (algebraMap A (Localization.AtPrime m)) q).IsPrime] :
    Localization.AtPrime (Ideal.map (algebraMap A (Localization.AtPrime m)) q) ≃ₐ[A]
      Localization.AtPrime q' := by
  subst q'
  -- The owner equivalence identifies the two-step localization with the localization at the
  -- contracted prime on the original ring.
  exact
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      m.primeCompl
      (Ideal.map (algebraMap A (Localization.AtPrime m)) q)).symm

/-- Helper for Lemma 10.54.5: the source localization prime used in the easy branch contracts back
to the original prime `q`. -/
private theorem source_localization_atPrime_map_under
    {A : Type u} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    (Ideal.map (algebraMap A (Localization.AtPrime m)) q).under A = q := by
  -- This is the contraction formula for primes under localization at `m`.
  simpa using
    (Ideal.under_map_of_isLocalizationAtPrime
      (S := Localization.AtPrime m) (q := m) hqm :
        (Ideal.map (algebraMap A (Localization.AtPrime m)) q).under A = q)

/-- Helper for Lemma 10.54.5: the source localization prime used in the easy branch is prime. -/
private theorem source_localization_atPrime_map_isPrime
    {A : Type u} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    (Ideal.map (algebraMap A (Localization.AtPrime m)) q).IsPrime := by
  -- The image of a prime under localization at a larger prime remains prime.
  simpa using
    (Ideal.isPrime_map_of_isLocalizationAtPrime
      (S := Localization.AtPrime m) (q := m) hqm :
        (Ideal.map (algebraMap A (Localization.AtPrime m)) q).IsPrime)

/-- Helper for Lemma 10.54.5: the inverse of the two-step localization equivalence is the owner
local map from `A_q` into the localization of `A_m` at the induced prime. -/
private theorem source_localization_atPrime_map_algEquiv_symm_toRingHom
    {A : Type u} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    let p_m : Ideal (Localization.AtPrime m) := Ideal.map (algebraMap A (Localization.AtPrime m)) q
    letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
    let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
      source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
        (source_localization_atPrime_map_under (A := A) hqm).symm
    eLoc.symm.toRingHom =
      Localization.localRingHom q p_m (algebraMap A (Localization.AtPrime m))
        (source_localization_atPrime_map_under (A := A) hqm).symm := by
  let p_m : Ideal (Localization.AtPrime m) := Ideal.map (algebraMap A (Localization.AtPrime m)) q
  letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
  let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
    source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
      (source_localization_atPrime_map_under (A := A) hqm).symm
  change eLoc.symm.toRingHom =
      Localization.localRingHom q p_m (algebraMap A (Localization.AtPrime m))
        (source_localization_atPrime_map_under (A := A) hqm).symm
  -- The inverse map is characterized by its effect on generators from the original ring `A`.
  symm
  apply Localization.localRingHom_unique
  intro x
  calc
    eLoc.symm (algebraMap A (Localization.AtPrime q) x) =
        algebraMap A (Localization.AtPrime p_m) x := eLoc.symm.commutes x
    _ =
        algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)
          (algebraMap A (Localization.AtPrime m) x) := rfl

/-- Helper for Lemma 10.54.5: composing the two-step localization equivalence with the source
algebra map recovers the canonical comparison `A_m → A_q`. -/
private theorem source_localization_atPrime_map_algEquiv_comp_source_algebraMap
    {A : Type u} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    let p_m : Ideal (Localization.AtPrime m) := Ideal.map (algebraMap A (Localization.AtPrime m)) q
    letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
    let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
      source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
        (source_localization_atPrime_map_under (A := A) hqm).symm
    let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
      IsLocalization.map
        (R := A)
        (P := A)
        (S := Localization.AtPrime m)
        (Q := Localization.AtPrime q)
        (M := m.primeCompl)
        (T := q.primeCompl)
        (g := RingHom.id A)
        ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
          (by simpa using hqm))
    (eLoc.toRingHom).comp (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) = ρm :=
    by
  let p_m : Ideal (Localization.AtPrime m) := Ideal.map (algebraMap A (Localization.AtPrime m)) q
  letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
  let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
    source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
      (source_localization_atPrime_map_under (A := A) hqm).symm
  let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
    IsLocalization.map
      (R := A)
      (P := A)
      (S := Localization.AtPrime m)
      (Q := Localization.AtPrime q)
      (M := m.primeCompl)
      (T := q.primeCompl)
      (g := RingHom.id A)
      ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
        (by simpa using hqm))
  change (eLoc.toRingHom).comp (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) =
      ρm
  -- Equality of maps out of `A_m` is detected on the image of the original ring `A`.
  apply IsLocalization.ringHom_ext m.primeCompl
  ext x
  change eLoc (algebraMap A (Localization.AtPrime p_m) x) =
      ρm (algebraMap A (Localization.AtPrime m) x)
  calc
    eLoc (algebraMap A (Localization.AtPrime p_m) x) =
        algebraMap A (Localization.AtPrime q) x := eLoc.commutes x
    _ = ρm (algebraMap A (Localization.AtPrime m) x) := by
      symm
      rw [IsLocalization.map_eq]
      rfl

/-- Helper for Lemma 10.54.5: after localizing at a prime, pushing forward the pullback ideal
recovers the original ideal. This is the canonical map-comap identity used in the easy branch. -/
private theorem source_localized_ideal_map_eq
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p)) :
    Ideal.map (algebraMap A (Localization.AtPrime p))
      (Ideal.comap (algebraMap A (Localization.AtPrime p)) K) = K := by
  -- This is exactly the owner localization identity `map (comap K) = K`.
  simpa using
    (IsLocalization.map_comap p.primeCompl (Localization.AtPrime p) K :
      Ideal.map (algebraMap A (Localization.AtPrime p))
        (Ideal.comap (algebraMap A (Localization.AtPrime p)) K) = K)

/-- Helper for Lemma 10.54.5: the quotient of `A_p` by the localized ideal carries the canonical
`A / J`-algebra structure induced from the quotient map `A → A_p`. -/
@[reducible]
private noncomputable def source_localized_quotient_target_algebra
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (J : Ideal A) :
    Algebra (A ⧸ J)
      (Localization.AtPrime p ⧸ Ideal.map (algebraMap A (Localization.AtPrime p)) J) :=
  Ideal.Quotient.algebraQuotientMapQuotient

/-- Helper for Lemma 10.54.5: mapping an ideal along the identity algebra equivalence does not
change that ideal. -/
private theorem ideal_map_algEquiv_refl {A : Type u} [CommRing A] (I : Ideal A) :
    Ideal.map (AlgEquiv.refl : A ≃ₐ[A] A) I = I := by
  change Ideal.map (RingHom.id A) I = I
  simpa using (Ideal.map_id (I := I))

/-- Helper for Lemma 10.54.5: Proposition 10.9.14 identifies the localization of the quotient
`A / J` at the image of `p.primeCompl` with the quotient of `A_p` by the localized ideal. -/
private noncomputable def source_localized_quotient_localization_algEquiv
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p)) :
    Localization
        (Algebra.algebraMapSubmonoid
          (A ⧸ Ideal.comap (algebraMap A (Localization.AtPrime p)) K) p.primeCompl) ≃ₐ[
        A ⧸ Ideal.comap (algebraMap A (Localization.AtPrime p)) K] (Localization.AtPrime p ⧸ K) :=
  by
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
    let Kmap : Ideal (Localization.AtPrime p) :=
      Ideal.map (algebraMap A (Localization.AtPrime p)) J
    letI : Algebra (A ⧸ J) (Localization.AtPrime p ⧸ Kmap) :=
      source_localized_quotient_target_algebra (A := A) (p := p) J
    let hKmap : Kmap = K := source_localized_ideal_map_eq (A := A) (p := p) K
    letI : Kmap.LiesOver J := ⟨by simpa [Ideal.under_def, J, hKmap]⟩
    letI : K.LiesOver J := ⟨by simpa [Ideal.under_def, J]⟩
    let eLoc :
        Localization (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl) ≃ₐ[A ⧸ J]
          (Localization.AtPrime p ⧸ Kmap) :=
      Localization.algEquiv
        (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
        (Localization.AtPrime p ⧸ Kmap)
    let eQuot :
        (Localization.AtPrime p ⧸ Kmap) ≃ₐ[A ⧸ J] (Localization.AtPrime p ⧸ K) :=
      let hKmap' :
          K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p)
            Kmap := by
        -- For the identity algebra equivalence, the pushed-forward ideal is unchanged.
        calc
          K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) K := by
            exact (ideal_map_algEquiv_refl (A := Localization.AtPrime p) K).symm
          _ = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) Kmap := by
            simpa using
              congrArg
                (fun I : Ideal (Localization.AtPrime p) =>
                  Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) I)
                hKmap.symm
      Ideal.Quotient.algEquivOfEqMap
        (p := J)
        (P := Kmap)
        (Q := K)
        (σ := (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p))
        hKmap'
    -- First identify the localization of `A / J` with the quotient by `Kmap`, then rewrite
    -- `Kmap = K` by the owner map-comap formula.
    exact eLoc.trans eQuot

/-- Helper for Lemma 10.54.5: the canonical localization-of-quotient equivalence sends the class
of `x` in `A / J` to the class of its image in `A_p / K`. -/
private theorem source_localized_quotient_localization_algEquiv_apply_mk
    {A : Type u} [CommRing A] {p : Ideal A} [p.IsPrime] (K : Ideal (Localization.AtPrime p))
    (x : A) :
    let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
    source_localized_quotient_localization_algEquiv (A := A) (p := p) K
      (algebraMap (A ⧸ J)
        (Localization
          (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl))
        (Ideal.Quotient.mk J x)) =
      Ideal.Quotient.mk K (algebraMap A (Localization.AtPrime p) x) := by
  let J : Ideal A := Ideal.comap (algebraMap A (Localization.AtPrime p)) K
  let Kmap : Ideal (Localization.AtPrime p) :=
    Ideal.map (algebraMap A (Localization.AtPrime p)) J
  letI : Algebra (A ⧸ J) (Localization.AtPrime p ⧸ Kmap) :=
    source_localized_quotient_target_algebra (A := A) (p := p) J
  let hKmap : Kmap = K := source_localized_ideal_map_eq (A := A) (p := p) K
  letI : Kmap.LiesOver J := ⟨by simpa [Ideal.under_def, J, hKmap]⟩
  letI : K.LiesOver J := ⟨by simpa [Ideal.under_def, J]⟩
  let eLoc :
      Localization (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl) ≃ₐ[A ⧸ J]
        (Localization.AtPrime p ⧸ Kmap) :=
    Localization.algEquiv
      (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
      (Localization.AtPrime p ⧸ Kmap)
  let hKmap' :
      K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) Kmap := by
    calc
      K = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) K := by
        exact (ideal_map_algEquiv_refl (A := Localization.AtPrime p) K).symm
      _ = Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) Kmap := by
        simpa using
          congrArg
            (fun I : Ideal (Localization.AtPrime p) =>
              Ideal.map (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p) I)
            hKmap.symm
  let eQuot :
      (Localization.AtPrime p ⧸ Kmap) ≃ₐ[A ⧸ J] (Localization.AtPrime p ⧸ K) :=
    Ideal.Quotient.algEquivOfEqMap
      (p := J)
      (P := Kmap)
      (Q := K)
      (σ := (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p))
      hKmap'
  -- Evaluate the localization equivalence on the class of `x / 1` before rewriting the ideal.
  change eQuot
      (eLoc
        (algebraMap (A ⧸ J)
          (Localization (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl))
          (Ideal.Quotient.mk J x))) =
    Ideal.Quotient.mk K (algebraMap A (Localization.AtPrime p) x)
  rw [← IsLocalization.mk'_one
    (M := Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
    (S := Localization (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl))
    (x := Ideal.Quotient.mk J x)]
  rw [show eLoc =
      Localization.algEquiv
        (Algebra.algebraMapSubmonoid (A ⧸ J) p.primeCompl)
        (Localization.AtPrime p ⧸ Kmap) by rfl]
  rw [Localization.algEquiv_mk']
  rw [IsLocalization.mk'_one]
  -- The remaining map is the quotient transport from `Kmap` back to `K`.
  simpa [eQuot] using
    (Ideal.Quotient.algEquivOfEqMap_apply
      (p := J)
      (σ := (AlgEquiv.refl : Localization.AtPrime p ≃ₐ[A] Localization.AtPrime p))
      hKmap'
      (algebraMap A (Localization.AtPrime p) x))

/-- Helper for Lemma 10.54.5: transport an `IsLocalization` witness across the algebra
equivalence that identifies the source-localized quotient with the target quotient. -/
private theorem localized_quotient_isLocalization_of_algEquiv
    {B : Type*} {L : Type*} {Q : Type*} {T : Type*}
    [CommRing B] [CommRing L] [CommRing Q] [CommRing T]
    [Algebra B L] [Algebra B Q] (e : L ≃ₐ[B] Q) (M : Submonoid Q)
    [Algebra Q T] [Algebra L T]
    (hLT : ∀ x, algebraMap L T x = algebraMap Q T (e x)) [IsLocalization M T] :
    IsLocalization (M.comap e.toRingHom) T := by
  -- Move the localization data across `e`, keeping the base quotient ring fixed.
  refine IsLocalization.of_ringEquiv_left (K := T) (M₁ := M) (M₂ := M.comap e.toRingHom)
    e.toRingEquiv ?_ hLT
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact hx'
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    change e (e.symm x) ∈ M
    simpa using hx

/-- Helper for Lemma 10.54.5: the localized source ideal `J` is exactly the pullback of `Iq`
along the comparison map `ρm : A_m → A_q`. -/
private theorem source_localized_quotient_comap_eq
    {A : Type u} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m)
    {Iq : Ideal (Localization.AtPrime q)} :
    let p_m : Ideal (Localization.AtPrime m) :=
      Ideal.map (algebraMap A (Localization.AtPrime m)) q
    letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
    let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
      source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
        (source_localization_atPrime_map_under (A := A) hqm).symm
    let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
      IsLocalization.map
        (R := A)
        (P := A)
        (S := Localization.AtPrime m)
        (Q := Localization.AtPrime q)
        (M := m.primeCompl)
        (T := q.primeCompl)
        (g := RingHom.id A)
        ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
          (by simpa using hqm))
    let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc.toRingHom Iq
    let J : Ideal (Localization.AtPrime m) :=
      Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
    J = Ideal.comap ρm Iq := by
  let p_m : Ideal (Localization.AtPrime m) :=
    Ideal.map (algebraMap A (Localization.AtPrime m)) q
  letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
  let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
    source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
      (source_localization_atPrime_map_under (A := A) hqm).symm
  let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
    IsLocalization.map
      (R := A)
      (P := A)
      (S := Localization.AtPrime m)
      (Q := Localization.AtPrime q)
      (M := m.primeCompl)
      (T := q.primeCompl)
      (g := RingHom.id A)
      ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
        (by simpa using hqm))
  let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc.toRingHom Iq
  let J : Ideal (Localization.AtPrime m) :=
    Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
  -- Rewrite the iterated-localization pullback along
  -- `A_m → A_{p_m} → A_q` to the direct comparison map `ρm : A_m → A_q`.
  change Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m))
      (Ideal.comap eLoc.toRingHom Iq) = Ideal.comap ρm Iq
  rw [Ideal.comap_comap]
  exact congrArg (fun f => Ideal.comap f Iq)
    (source_localization_atPrime_map_algEquiv_comp_source_algebraMap
      (A := A) (q := q) (m := m) hqm)

/-- Helper for Lemma 10.54.5: after transporting the quotient from the iterated localization back
to `A_q`, the induced quotient map from `A_m` is still the canonical composition with `ρm`. -/
private theorem source_localized_quotient_target_algebraMap_comp_mk
    {A : Type u} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m)
    {Iq : Ideal (Localization.AtPrime q)} :
    let p_m : Ideal (Localization.AtPrime m) :=
      Ideal.map (algebraMap A (Localization.AtPrime m)) q
    letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
    let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
      source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
        (source_localization_atPrime_map_under (A := A) hqm).symm
    let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
      IsLocalization.map
        (R := A)
        (P := A)
        (S := Localization.AtPrime m)
        (Q := Localization.AtPrime q)
        (M := m.primeCompl)
        (T := q.primeCompl)
        (g := RingHom.id A)
        ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
          (by simpa using hqm))
    letI : Algebra (Localization.AtPrime m) (Localization.AtPrime q) := ρm.toAlgebra
    let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc.toRingHom Iq
    let J : Ideal (Localization.AtPrime m) :=
      Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
    (Ideal.quotientMap Iq ρm
        ((source_localized_quotient_comap_eq (A := A) (q := q) (m := m) (hqm := hqm)
          (Iq := Iq)).le)).comp (Ideal.Quotient.mk J) =
      (Ideal.Quotient.mk Iq).comp ρm := by
  let p_m : Ideal (Localization.AtPrime m) :=
    Ideal.map (algebraMap A (Localization.AtPrime m)) q
  letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
  let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
    source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
      (source_localization_atPrime_map_under (A := A) hqm).symm
  let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
    IsLocalization.map
      (R := A)
      (P := A)
      (S := Localization.AtPrime m)
      (Q := Localization.AtPrime q)
      (M := m.primeCompl)
      (T := q.primeCompl)
      (g := RingHom.id A)
      ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
        (by simpa using hqm))
  letI : Algebra (Localization.AtPrime m) (Localization.AtPrime q) := ρm.toAlgebra
  let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc.toRingHom Iq
  let J : Ideal (Localization.AtPrime m) :=
    Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
  -- The explicit quotient comparison is determined by its action on generators.
  simpa using
    (Ideal.quotientMap_comp_mk
      (J := J)
      (I := Iq)
      (f := ρm)
      ((source_localized_quotient_comap_eq (A := A) (q := q) (m := m) (hqm := hqm)
        (Iq := Iq)).le))

/-- Helper for Lemma 10.54.5: the quotient of the iterated localization transports back to the
quotient of `A_q` over the common source quotient `A_m / J`. -/
private noncomputable def source_localized_quotient_transport_algEquiv_over_source
    {A : Type u} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m)
    {Iq : Ideal (Localization.AtPrime q)} :
    let p_m : Ideal (Localization.AtPrime m) :=
      Ideal.map (algebraMap A (Localization.AtPrime m)) q
    letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
    let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
      source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
        (source_localization_atPrime_map_under (A := A) hqm).symm
    let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
      IsLocalization.map
        (R := A)
        (P := A)
        (S := Localization.AtPrime m)
        (Q := Localization.AtPrime q)
        (M := m.primeCompl)
        (T := q.primeCompl)
        (g := RingHom.id A)
        ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
          (by simpa using hqm))
    letI : Algebra (Localization.AtPrime m) (Localization.AtPrime q) := ρm.toAlgebra
    let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc.toRingHom Iq
    let J : Ideal (Localization.AtPrime m) :=
      Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
    (Localization.AtPrime p_m ⧸ K) ≃+* (Localization.AtPrime q ⧸ Iq) :=
  by
    let p_m : Ideal (Localization.AtPrime m) :=
      Ideal.map (algebraMap A (Localization.AtPrime m)) q
    letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
    let eLoc₀ : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
      source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
        (source_localization_atPrime_map_under (A := A) hqm).symm
    let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
      IsLocalization.map
        (R := A)
        (P := A)
        (S := Localization.AtPrime m)
        (Q := Localization.AtPrime q)
        (M := m.primeCompl)
        (T := q.primeCompl)
        (g := RingHom.id A)
        ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
          (by simpa using hqm))
    letI : Algebra (Localization.AtPrime m) (Localization.AtPrime q) := ρm.toAlgebra
    let eLoc : Localization.AtPrime p_m ≃ₐ[Localization.AtPrime m] Localization.AtPrime q :=
      { __ := eLoc₀.toRingEquiv
        commutes' := by
          intro x
          -- The second localization followed by the owner equivalence is exactly the canonical
          -- comparison map `ρm : A_m → A_q`.
          exact congrArg (fun f : Localization.AtPrime m →+* Localization.AtPrime q => f x)
            (source_localization_atPrime_map_algEquiv_comp_source_algebraMap
              (A := A) (q := q) (m := m) hqm) }
    let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc₀.toRingHom Iq
    let J : Ideal (Localization.AtPrime m) :=
      Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
    have hcomap : K = Ideal.comap eLoc.toRingHom Iq := by
      rfl
    letI : K.LiesOver J := ⟨by simpa [Ideal.under_def, J]⟩
    letI : Iq.LiesOver J := ⟨by
      simpa [J] using
        (source_localized_quotient_comap_eq (A := A) (q := q) (m := m) (hqm := hqm)
          (Iq := Iq))⟩
    -- Transport the quotient across the owner algebra equivalence over the common base
    -- `Localization.AtPrime m ⧸ J`.
    exact (Ideal.Quotient.algEquivOfEqComap (p := J) (σ := eLoc) hcomap).toRingEquiv

/-- Helper for Lemma 10.54.5: on the class of an element of `A_m`, the quotient transport above
agrees with the canonical quotient map induced by `ρm : A_m → A_q`. -/
private theorem source_localized_quotient_transport_algEquiv_over_source_apply_mk
    {A : Type u} [CommRing A] {q m : Ideal A} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m)
    {Iq : Ideal (Localization.AtPrime q)} (x : Localization.AtPrime m) :
    let p_m : Ideal (Localization.AtPrime m) :=
      Ideal.map (algebraMap A (Localization.AtPrime m)) q
    letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
    let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
      source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
        (source_localization_atPrime_map_under (A := A) hqm).symm
    let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
      IsLocalization.map
        (R := A)
        (P := A)
        (S := Localization.AtPrime m)
        (Q := Localization.AtPrime q)
        (M := m.primeCompl)
        (T := q.primeCompl)
        (g := RingHom.id A)
        ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
          (by simpa using hqm))
    letI : Algebra (Localization.AtPrime m) (Localization.AtPrime q) := ρm.toAlgebra
    let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc.toRingHom Iq
    let J : Ideal (Localization.AtPrime m) :=
      Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
    source_localized_quotient_transport_algEquiv_over_source
      (A := A) (q := q) (m := m) (hqm := hqm) (Iq := Iq)
      (Ideal.Quotient.mk K
        (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m) x)) =
      Ideal.Quotient.mk Iq (ρm x) := by
  let p_m : Ideal (Localization.AtPrime m) :=
    Ideal.map (algebraMap A (Localization.AtPrime m)) q
  letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
  let eLoc₀ : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
    source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
      (source_localization_atPrime_map_under (A := A) hqm).symm
  let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
    IsLocalization.map
      (R := A)
      (P := A)
      (S := Localization.AtPrime m)
      (Q := Localization.AtPrime q)
      (M := m.primeCompl)
      (T := q.primeCompl)
      (g := RingHom.id A)
      ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
        (by simpa using hqm))
  letI : Algebra (Localization.AtPrime m) (Localization.AtPrime q) := ρm.toAlgebra
  let eLoc : Localization.AtPrime p_m ≃ₐ[Localization.AtPrime m] Localization.AtPrime q :=
    { __ := eLoc₀.toRingEquiv
      commutes' := by
        intro z
        -- Reuse the owner comparison between the second localization and the direct map `ρm`.
        exact congrArg (fun f : Localization.AtPrime m →+* Localization.AtPrime q => f z)
          (source_localization_atPrime_map_algEquiv_comp_source_algebraMap
            (A := A) (q := q) (m := m) hqm) }
  let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc₀.toRingHom Iq
  let J : Ideal (Localization.AtPrime m) :=
    Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
  have hcomap : K = Ideal.comap eLoc.toRingHom Iq := by
    rfl
  letI : K.LiesOver J := ⟨by simpa [Ideal.under_def, J]⟩
  letI : Iq.LiesOver J := ⟨by
    simpa [J] using
      (source_localized_quotient_comap_eq (A := A) (q := q) (m := m) (hqm := hqm)
        (Iq := Iq))⟩
  have htransport :
      source_localized_quotient_transport_algEquiv_over_source
          (A := A) (q := q) (m := m) (hqm := hqm) (Iq := Iq)
          (Ideal.Quotient.mk K
            (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m) x)) =
        Ideal.Quotient.mk Iq
          (eLoc (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m) x)) := by
    -- Evaluate the quotient transport on the image of the source generator.
    simpa [source_localized_quotient_transport_algEquiv_over_source, p_m, eLoc₀, ρm, eLoc, K, J]
      using
        (Ideal.Quotient.algEquivOfEqComap_apply
          (p := J) (σ := eLoc) hcomap
          (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m) x))
  have hcomm :
      eLoc (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m) x) = ρm x := by
    -- Replace the iterated-localization route with the direct comparison map `ρm`.
    exact congrArg (fun f : Localization.AtPrime m →+* Localization.AtPrime q => f x)
      (source_localization_atPrime_map_algEquiv_comp_source_algebraMap
        (A := A) (q := q) (m := m) hqm)
  rw [hcomm] at htransport
  simpa using htransport

private theorem isLocalizationOfQuotient_comp_source_localization_atPrime
    {A : Type u} {T : Type v} [CommRing A] [CommRing T] {q m : Ideal A}
    [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) (ψq : Localization.AtPrime q →+* T)
    (hψq : RingHom.IsLocalizationOfQuotient ψq) :
    RingHom.IsLocalizationOfQuotient
      (ψq.comp
        (IsLocalization.map
          (R := A)
          (P := A)
          (S := Localization.AtPrime m)
          (Q := Localization.AtPrime q)
        (M := m.primeCompl)
        (T := q.primeCompl)
        (g := RingHom.id A)
        ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
            (by simpa using hqm)))) := by
  let ρm : Localization.AtPrime m →+* Localization.AtPrime q :=
    IsLocalization.map
      (R := A)
      (P := A)
      (S := Localization.AtPrime m)
      (Q := Localization.AtPrime q)
      (M := m.primeCompl)
      (T := q.primeCompl)
      (g := RingHom.id A)
      ((Localization.le_comap_primeCompl_iff (I := m) (J := q) (f := RingHom.id A)).2
        (by simpa using hqm))
  rcases hψq with ⟨Iq, hAlgq, Mq, hlocq, rfl⟩
  letI : Algebra (Localization.AtPrime q ⧸ Iq) T := hAlgq
  letI : IsLocalization Mq T := hlocq
  let p_m : Ideal (Localization.AtPrime m) :=
    Ideal.map (algebraMap A (Localization.AtPrime m)) q
  letI : p_m.IsPrime := source_localization_atPrime_map_isPrime (A := A) hqm
  let eLoc : Localization.AtPrime p_m ≃ₐ[A] Localization.AtPrime q :=
    source_localization_atPrime_map_algEquiv (A := A) (q := q) (m := m) (q' := q)
      (source_localization_atPrime_map_under (A := A) hqm).symm
  let K : Ideal (Localization.AtPrime p_m) := Ideal.comap eLoc.toRingHom Iq
  let J : Ideal (Localization.AtPrime m) :=
    Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K
  let eTrans : (Localization.AtPrime p_m ⧸ K) ≃+* (Localization.AtPrime q ⧸ Iq) :=
    source_localized_quotient_transport_algEquiv_over_source
      (A := A) (q := q) (m := m) (hqm := hqm) (Iq := Iq)
  letI : Algebra (Localization.AtPrime m ⧸ J) (Localization.AtPrime p_m ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap (show J ≤
      Ideal.comap (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m)) K from le_rfl)
  letI : Algebra (Localization.AtPrime p_m ⧸ K) T :=
    ((algebraMap (Localization.AtPrime q ⧸ Iq) T).comp eTrans.toRingHom).toAlgebra
  let M' : Submonoid (Localization.AtPrime p_m ⧸ K) := Mq.comap eTrans.toRingHom
  have hM' : M'.map (eTrans : Localization.AtPrime p_m ⧸ K ≃* Localization.AtPrime q ⧸ Iq) = Mq := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨eTrans.symm y, ?_, by simp⟩
      change eTrans (eTrans.symm y) ∈ Mq
      simpa using hy
  letI : IsLocalization M' T :=
    IsLocalization.of_ringEquiv_left
      (R := Localization.AtPrime p_m ⧸ K)
      (S := Localization.AtPrime q ⧸ Iq)
      (K := T)
      eTrans hM' (fun _ ↦ rfl)
  let N : Submonoid (Localization.AtPrime m ⧸ J) :=
    Algebra.algebraMapSubmonoid (Localization.AtPrime m ⧸ J) p_m.primeCompl
  let eSource :
      Localization N ≃ₐ[Localization.AtPrime m ⧸ J] (Localization.AtPrime p_m ⧸ K) :=
    source_localized_quotient_localization_algEquiv
      (A := Localization.AtPrime m) (p := p_m) K
  letI : IsLocalization N (Localization.AtPrime p_m ⧸ K) :=
    IsLocalization.isLocalization_of_algEquiv N eSource
  letI : Algebra (Localization.AtPrime m ⧸ J) T :=
    ((algebraMap (Localization.AtPrime p_m ⧸ K) T).comp
      (algebraMap (Localization.AtPrime m ⧸ J) (Localization.AtPrime p_m ⧸ K))).toAlgebra
  letI : SMul (Localization.AtPrime m ⧸ J) (Localization.AtPrime p_m ⧸ K) := Algebra.toSMul
  have hsmul_assoc :
      ∀ x : Localization.AtPrime m ⧸ J, ∀ y : Localization.AtPrime p_m ⧸ K, ∀ z : T,
        (x • y) • z = x • y • z := by
    intro x y z
    simp [RingHom.algebraMap_toAlgebra, Algebra.smul_def, mul_assoc]
  letI : IsScalarTower (Localization.AtPrime m ⧸ J) (Localization.AtPrime p_m ⧸ K) T :=
    ⟨hsmul_assoc⟩
  let M : Submonoid (Localization.AtPrime m ⧸ J) :=
    IsLocalization.localizationLocalizationSubmodule N M'
  letI : IsLocalization M T := IsLocalization.localization_localization_isLocalization N M' T
  refine ⟨J, inferInstance, M, inferInstance, ?_⟩
  -- Evaluate the transported quotient-localization presentation on generators from `A_m`.
  ext x
  change algebraMap (Localization.AtPrime q ⧸ Iq) T (Ideal.Quotient.mk Iq (ρm x)) =
    algebraMap (Localization.AtPrime m ⧸ J) T (Ideal.Quotient.mk J x)
  symm
  calc
    algebraMap (Localization.AtPrime m ⧸ J) T (Ideal.Quotient.mk J x)
        = algebraMap (Localization.AtPrime p_m ⧸ K) T
            (Ideal.Quotient.mk K
              (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m) x)) := rfl
    _ = algebraMap (Localization.AtPrime q ⧸ Iq) T
          (eTrans
            (Ideal.Quotient.mk K
              (algebraMap (Localization.AtPrime m) (Localization.AtPrime p_m) x))) := rfl
    _ = algebraMap (Localization.AtPrime q ⧸ Iq) T
          (Ideal.Quotient.mk Iq (ρm x)) := by
          rw [source_localized_quotient_transport_algEquiv_over_source_apply_mk
            (A := A) (q := q) (m := m) (hqm := hqm) (Iq := Iq)]

/-- Helper for Lemma 10.54.5: in a finite nonempty subset of a valuation ring consisting of
nonzero elements, one element is divisible by all the others. -/
private lemma exists_mem_finset_dvd_by_all_of_valuationRing
    {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    (t : Finset V) (ht : t.Nonempty) (h0 : ∀ y ∈ t, y ≠ 0) :
    ∃ yr ∈ t, yr ≠ 0 ∧ ∀ y ∈ t, y ∣ yr := by
  classical
  refine Finset.strongInductionOn t ?_ ht h0
  intro t ih ht' h0'
  obtain ⟨a, ha⟩ := ht'
  let s := t.erase a
  have hst : insert a s = t := by
    simp [s, ha]
  by_cases hs_nonempty : s.Nonempty
  · -- Compare `a` with the common multiple already chosen from the smaller finite set.
    have hs0 : ∀ y ∈ s, y ≠ 0 := by
      intro y hy
      exact h0' y (hst ▸ Finset.mem_insert_of_mem hy)
    obtain ⟨yr, hyrs, hyr0, hyr_all⟩ := ih s (Finset.erase_ssubset ha) hs_nonempty hs0
    rcases ValuationRing.dvd_total a yr with hayr | hyra
    · refine ⟨yr, hst ▸ by simp [s, hyrs], hyr0, ?_⟩
      intro y hy
      rw [← hst] at hy
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact hayr
      · exact hyr_all y hys
    · refine ⟨a, hst ▸ by simp [s], h0' a (hst ▸ by simp), ?_⟩
      intro y hy
      rw [← hst] at hy
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact dvd_rfl
      · exact dvd_trans (hyr_all y hys) hyra
  · -- If the smaller finite set is empty, the unique element is the desired common multiple.
    have hs_eq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs_nonempty
    refine ⟨a, hst ▸ by simp [s, hs_eq], h0' a (hst ▸ by simp), ?_⟩
    intro y hy
    rw [← hst] at hy
    rcases Finset.mem_insert.mp hy with rfl | hys
    · exact dvd_rfl
    · simpa [s, hs_eq] using hys

/-- Helper for Lemma 10.54.5: if a prime of a polynomial ring maps into a local target over `R`,
then adding the extension of `maximalIdeal R` still gives a proper ideal. -/
private theorem prime_plus_maximalIdeal_ne_top_of_local_target {n : ℕ}
    {T : Type*} [CommRing T] [IsLocalRing T] [Algebra R T]
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (f : MvPolynomial (Fin n) R →ₐ[R] T)
    (hlocal : IsLocalHom (algebraMap R T))
    (hqf : q.asIdeal ≤ RingHom.ker f.toRingHom) :
    q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) ≠ ⊤ := by
  have hq :
      q.asIdeal ≤ Ideal.comap f.toRingHom (maximalIdeal T) := by
    intro x hx
    have hx0 : f x = 0 := hqf hx
    simpa [Ideal.mem_comap, hx0] using (Ideal.zero_mem (maximalIdeal T))
  have hm :
      Ideal.map MvPolynomial.C (maximalIdeal R) ≤ Ideal.comap f.toRingHom (maximalIdeal T) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hx_nonunit : ¬ IsUnit x := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    have hx_mem : x ∈ maximalIdeal R := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have hxT_nonunit : ¬ IsUnit (algebraMap R T x) := fun hxT_unit ↦
      hx_nonunit (IsUnit.of_map (algebraMap R T) x hxT_unit)
    have hxT_mem : algebraMap R T x ∈ maximalIdeal T := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    simpa [f.commutes x] using hxT_mem
  have hproper :
      Ideal.comap f.toRingHom (maximalIdeal T) ≠ ⊤ :=
    Ideal.comap_ne_top _ (maximalIdeal.isMaximal T).ne_top
  intro htop
  have hle :
      q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) ≤
        Ideal.comap f.toRingHom (maximalIdeal T) :=
    sup_le hq hm
  exact hproper (top_unique (htop.symm ▸ hle))

/-- Helper for Lemma 10.54.5: under the hard-branch hypothesis, some residue coordinate of the
prime-localized polynomial presentation is not contained in the chosen valuation subring. -/
private theorem exists_coordinate_not_mem_valuation_subring {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    (hA : ∀ x : R, algebraMap R q.asIdeal.ResidueField x ∈ A)
    (hlocal : IsLocalHom ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA))
    (hqtop : q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) = ⊤) :
    ∃ j : Fin n,
      algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField (MvPolynomial.X j) ∉ A := by
  let K := q.asIdeal.ResidueField
  let coord : Fin n → K := fun j ↦ algebraMap (MvPolynomial (Fin n) R) K (MvPolynomial.X j)
  let fR : R →+* A := (algebraMap R K).codRestrict A.toSubring hA
  letI : Algebra R A := fR.toAlgebra
  by_contra hcontra
  push_neg at hcontra
  let ηA : MvPolynomial (Fin n) R →ₐ[R] A :=
    MvPolynomial.aeval fun j ↦ ⟨coord j, hcontra j⟩
  have hηA :
      A.subtype.comp ηA.toRingHom = algebraMap (MvPolynomial (Fin n) R) K := by
    -- Compare both maps on coefficients and the polynomial generators.
    apply MvPolynomial.ringHom_ext
    · intro x
      calc
        (A.subtype.comp ηA.toRingHom) (MvPolynomial.C x) = A.subtype (algebraMap R A x) := by
          simp [ηA, RingHom.comp_apply]
        _ = algebraMap R K x := rfl
        _ = (algebraMap (MvPolynomial (Fin n) R) K) (MvPolynomial.C x) := by
          symm
          exact MvPolynomial.algHom_C
            (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) K) x
    · intro j
      simp [ηA, coord]
  have hqηA : q.asIdeal ≤ RingHom.ker ηA.toRingHom := by
    -- Every element of `q` already vanishes in the residue field, and the subtype map is injective.
    intro x hx
    have hxComp : (A.subtype.comp ηA.toRingHom) x = 0 := by
      rw [hηA]
      exact Ideal.algebraMap_residueField_eq_zero.mpr hx
    apply A.subtype_injective
    change (A.subtype.comp ηA.toRingHom) x = A.subtype 0
    simpa [RingHom.comp_apply] using hxComp
  have hproper :
      q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) ≠ ⊤ :=
    prime_plus_maximalIdeal_ne_top_of_local_target (R := R) q ηA hlocal hqηA
  exact hproper hqtop

/-- Helper for Lemma 10.54.5: the `j`-th polynomial coordinate viewed in the residue field at
`q`. -/
private noncomputable abbrev residue_coordinate {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (j : Fin n) :
    q.asIdeal.ResidueField :=
  algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField (MvPolynomial.X j)

/-- Helper for Lemma 10.54.5: if a residue coordinate is outside the valuation subring, its
inverse defines an element of that valuation ring. -/
private noncomputable def bad_residue_coordinate_inverse {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField) {j : Fin n}
    (hj : residue_coordinate (R := R) q j ∉ A) : A :=
  ⟨(residue_coordinate (R := R) q j)⁻¹, (A.mem_or_inv_mem _).resolve_left hj⟩

/-- Helper for Lemma 10.54.5: a bad residue coordinate is nonzero, so its inverse lies in the
valuation subring. -/
private theorem bad_residue_coordinate_nonzero_and_inv_mem {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    {j : Fin n} (hj : residue_coordinate (R := R) q j ∉ A) :
    residue_coordinate (R := R) q j ≠ 0 ∧
      (residue_coordinate (R := R) q j)⁻¹ ∈ A := by
  constructor
  · intro h0
    exact hj (by simpa [residue_coordinate, h0] using
      (A.zero_mem : (0 : q.asIdeal.ResidueField) ∈ A))
  · exact (A.mem_or_inv_mem _).resolve_left hj

/-- Helper for Lemma 10.54.5: among the bad residue coordinates, one inverse is divisible by all
the others inside the valuation subring. -/
private theorem exists_bad_coordinate_inverse_dvd_all_bad {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    (hA : ∀ x : R, algebraMap R q.asIdeal.ResidueField x ∈ A)
    (hlocal : IsLocalHom ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA))
    (hqtop : q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) = ⊤) :
    ∃ (i : Fin n) (hi : residue_coordinate (R := R) q i ∉ A),
      ∀ j (hj : residue_coordinate (R := R) q j ∉ A),
        bad_residue_coordinate_inverse (R := R) q A hj ∣
          bad_residue_coordinate_inverse (R := R) q A hi := by
  classical
  let bad : Finset (Fin n) := Finset.univ.filter fun j ↦ residue_coordinate (R := R) q j ∉ A
  have hbad_mem : ∀ {j : Fin n}, j ∈ bad → residue_coordinate (R := R) q j ∉ A := by
    intro j hj
    simpa [bad] using hj
  obtain ⟨j, hj⟩ :=
    exists_coordinate_not_mem_valuation_subring (R := R) q A hA hlocal hqtop
  have hbad_nonempty : bad.Nonempty := ⟨j, by simpa [bad] using hj⟩
  let invs : Finset A :=
    bad.attach.image fun j ↦
      bad_residue_coordinate_inverse (R := R) q A (hbad_mem j.2)
  have hinvs_nonempty : invs.Nonempty := by
    refine ⟨bad_residue_coordinate_inverse (R := R) q A hj, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨j, by simpa [bad] using hj⟩, by simp, rfl⟩
  have hinvs_nonzero : ∀ y ∈ invs, y ≠ 0 := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, -, rfl⟩
    rcases bad_residue_coordinate_nonzero_and_inv_mem (R := R) q A (hbad_mem j.2) with
      ⟨hj0, _⟩
    intro h0
    exact (inv_ne_zero hj0) (congrArg Subtype.val h0)
  obtain ⟨yr, hyr_mem, _, hyr_all⟩ :=
    exists_mem_finset_dvd_by_all_of_valuationRing invs hinvs_nonempty hinvs_nonzero
  rcases Finset.mem_image.mp hyr_mem with ⟨i, -, hiyr⟩
  refine ⟨i.1, hbad_mem i.2, ?_⟩
  intro j hj
  have hj_mem :
      bad_residue_coordinate_inverse (R := R) q A hj ∈ invs := by
    exact Finset.mem_image.mpr
      ⟨⟨j, by simpa [bad] using hj⟩, by simp, rfl⟩
  simpa [hiyr] using hyr_all (bad_residue_coordinate_inverse (R := R) q A hj) hj_mem

/-- Helper for Lemma 10.54.5: if the prime presentation is not already in the easy branch, then a
dominating valuation subring of the residue field yields a reciprocal-chart pivot coordinate. -/
private theorem exists_pivot_coordinate_for_reciprocal_chart {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    (hA : ∀ x : R, algebraMap R q.asIdeal.ResidueField x ∈ A)
    (hlocal : IsLocalHom ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA))
    (hqtop : q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) = ⊤) :
    ∃ i : Fin n,
      algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField (MvPolynomial.X i) ≠ 0 ∧
        (algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField (MvPolynomial.X i))⁻¹ ∈ A ∧
        ∀ j : Fin n,
          algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField (MvPolynomial.X j) /
              algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField (MvPolynomial.X i) ∈ A := by
  obtain ⟨i, hi, hdiv⟩ :=
    exists_bad_coordinate_inverse_dvd_all_bad (R := R) q A hA hlocal hqtop
  obtain ⟨hi0, hiinv⟩ := bad_residue_coordinate_nonzero_and_inv_mem (R := R) q A hi
  refine ⟨i, hi0, hiinv, ?_⟩
  intro j
  by_cases hj : residue_coordinate (R := R) q j ∈ A
  · -- In the good case the quotient is a product of two elements already in the valuation ring.
    simpa [residue_coordinate, div_eq_mul_inv] using
      A.mul_mem (residue_coordinate (R := R) q j) ((residue_coordinate (R := R) q i)⁻¹) hj hiinv
  · -- In the bad case the chosen inverse dominates all other bad inverses by divisibility.
    rcases bad_residue_coordinate_nonzero_and_inv_mem (R := R) q A hj with ⟨hj0, _⟩
    rcases hdiv j hj with ⟨a, ha⟩
    have ha_val :
        (residue_coordinate (R := R) q i)⁻¹ =
          (residue_coordinate (R := R) q j)⁻¹ * (a : q.asIdeal.ResidueField) := by
      exact congrArg Subtype.val ha
    have hquot_val :
        residue_coordinate (R := R) q j / residue_coordinate (R := R) q i =
          (a : q.asIdeal.ResidueField) := by
      calc
        residue_coordinate (R := R) q j / residue_coordinate (R := R) q i
            = residue_coordinate (R := R) q j * (residue_coordinate (R := R) q i)⁻¹ := by
                rw [div_eq_mul_inv]
        _ = residue_coordinate (R := R) q j *
              ((residue_coordinate (R := R) q j)⁻¹ * (a : q.asIdeal.ResidueField)) := by
                rw [ha_val]
        _ = (residue_coordinate (R := R) q j * (residue_coordinate (R := R) q j)⁻¹) *
              (a : q.asIdeal.ResidueField) := by
                rw [mul_assoc]
        _ = (1 : q.asIdeal.ResidueField) * (a : q.asIdeal.ResidueField) := by
                rw [mul_inv_cancel₀ hj0]
        _ = (a : q.asIdeal.ResidueField) := by simp
    rw [hquot_val]
    exact a.2

/-- Helper for Lemma 10.54.5: if the pivot residue coordinate is nonzero, then the corresponding
polynomial variable does not belong to `q`. -/
private theorem pivot_coordinate_not_mem_prime {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) {i : Fin n}
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    MvPolynomial.X i ∉ q.asIdeal := by
  -- The residue map kills exactly the prime ideal defining the residue field.
  intro hXi
  exact hi0 (Ideal.algebraMap_residueField_eq_zero.mpr hXi)

/-- Helper for Lemma 10.54.5: a prime avoiding `r` is the contraction of some prime of the away
localization at `r`. -/
private theorem exists_away_prime_over_prime
    {A : Type*} [CommRing A] (q : PrimeSpectrum A) {r : A} (hr : r ∉ q.asIdeal) :
    ∃ qAway : PrimeSpectrum (Localization.Away r),
      PrimeSpectrum.comap (algebraMap A (Localization.Away r)) qAway = q := by
  have hrange :
      q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away r))) := by
    -- For away localization, the image of `Spec A_r → Spec A` is exactly `D(r)`.
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    simpa [PrimeSpectrum.mem_basicOpen] using hr
  exact Set.mem_range.mp hrange

/-- Helper for Lemma 10.54.5: on the away localization at `X i`, the reciprocal chart sends the
`i`-th coordinate to its inverse and every other coordinate to the corresponding quotient by
`X i`. -/
private noncomputable abbrev reciprocal_chart_away_generator {n : ℕ} (i j : Fin n) :
    Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) :=
  if _ : j = i then
    IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin n) R)
  else
    algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))
        (MvPolynomial.X j) *
      IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin n) R)

/-- Helper for Lemma 10.54.5: the reciprocal-chart polynomial map is the `R`-algebra map obtained
by evaluating the polynomial variables at the reciprocal-chart generators in the away
localization. -/
private noncomputable abbrev reciprocal_chart_away_polynomialRingHom {n : ℕ} (i : Fin n) :
    MvPolynomial (Fin n) R →+*
      Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) :=
  (MvPolynomial.aeval (reciprocal_chart_away_generator (R := R) i)).toRingHom

/-- Helper for Lemma 10.54.5: the reciprocal-chart image of the pivot variable is invertible in
the away localization. -/
private theorem reciprocal_chart_away_generator_isUnit {n : ℕ} (i : Fin n) :
    IsUnit
      ((reciprocal_chart_away_polynomialRingHom (R := R) i) (MvPolynomial.X i)) := by
  have hXi :
      (reciprocal_chart_away_polynomialRingHom (R := R) i) (MvPolynomial.X i) =
        IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin n) R) := by
    simp [reciprocal_chart_away_polynomialRingHom, reciprocal_chart_away_generator]
  rw [hXi]
  refine isUnit_iff_exists_inv.mpr ?_
  refine ⟨algebraMap (MvPolynomial (Fin n) R)
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))
      (MvPolynomial.X i), ?_⟩
  rw [mul_comm, IsLocalization.Away.mul_invSelf]

/-- Helper for Lemma 10.54.5: the reciprocal-chart map of the away localization is obtained by
lifting the reciprocal-chart polynomial substitution across the localization at `X i`. -/
private noncomputable abbrev reciprocal_chart_away_selfmap {n : ℕ} (i : Fin n) :
    Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) →+*
      Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) :=
  Localization.awayLift
    (reciprocal_chart_away_polynomialRingHom (R := R) i)
    (MvPolynomial.X i)
    (reciprocal_chart_away_generator_isUnit (R := R) i)

/-- Helper for Lemma 10.54.5: on elements coming from the polynomial ring, the reciprocal-chart
away self-map agrees with the defining polynomial substitution. -/
private theorem reciprocal_chart_away_selfmap_algebraMap {n : ℕ} (i : Fin n)
    (p : MvPolynomial (Fin n) R) :
    reciprocal_chart_away_selfmap (R := R) i
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) p) =
      (reciprocal_chart_away_polynomialRingHom (R := R) i) p := by
  -- The away lift is characterized by agreeing with the defining polynomial substitution on the
  -- image of the polynomial ring.
  simpa [reciprocal_chart_away_selfmap] using
    (IsLocalization.Away.lift_eq
      (x := MvPolynomial.X i)
      (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))
      (g := reciprocal_chart_away_polynomialRingHom (R := R) i)
      (hg := reciprocal_chart_away_generator_isUnit (R := R) i)
      p)

/-- Helper for Lemma 10.54.5: on the pivot variable, the reciprocal-chart away self-map produces
the canonical inverse of `X i`. -/
private theorem reciprocal_chart_away_selfmap_X_eq {n : ℕ} (i : Fin n) :
    reciprocal_chart_away_selfmap (R := R) i
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))
          (MvPolynomial.X i)) =
      IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin n) R) := by
  -- Evaluate the defining substitution on the pivot generator.
  rw [reciprocal_chart_away_selfmap_algebraMap (R := R) i (MvPolynomial.X i)]
  simp [reciprocal_chart_away_polynomialRingHom, reciprocal_chart_away_generator]

/-- Helper for Lemma 10.54.5: on a non-pivot variable, the reciprocal-chart away self-map divides
that coordinate by the pivot coordinate. -/
private theorem reciprocal_chart_away_selfmap_X_ne {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    reciprocal_chart_away_selfmap (R := R) i
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))
          (MvPolynomial.X j)) =
      algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))
          (MvPolynomial.X j) *
        IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin n) R) := by
  -- Evaluate the defining substitution on a non-pivot generator.
  rw [reciprocal_chart_away_selfmap_algebraMap (R := R) i (MvPolynomial.X j)]
  simp [reciprocal_chart_away_polynomialRingHom, reciprocal_chart_away_generator, hji]

/-- Helper for Lemma 10.54.5: applying the reciprocal-chart away self-map to the canonical inverse
of the pivot variable recovers the pivot variable itself. -/
private theorem reciprocal_chart_away_selfmap_invSelf {n : ℕ} (i : Fin n) :
    reciprocal_chart_away_selfmap (R := R) i
        (IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin n) R)) =
      algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))
        (MvPolynomial.X i) := by
  let P := MvPolynomial (Fin n) R
  let A0 := Localization.Away (MvPolynomial.X i : P)
  let Xi : A0 := algebraMap P A0 (MvPolynomial.X i)
  let invXi : A0 := IsLocalization.Away.invSelf (MvPolynomial.X i : P)
  have hunitInv : IsUnit invXi := by
    simpa [invXi] using reciprocal_chart_away_generator_isUnit (R := R) i
  have hmul :
      reciprocal_chart_away_selfmap (R := R) i Xi *
          reciprocal_chart_away_selfmap (R := R) i invXi = 1 := by
    -- Apply the ring homomorphism to the defining inverse relation `X i * X i⁻¹ = 1`.
    simpa [Xi, invXi, map_mul] using
      congrArg (reciprocal_chart_away_selfmap (R := R) i)
        (IsLocalization.Away.mul_invSelf (x := MvPolynomial.X i) (S := A0))
  have horig : invXi * Xi = 1 := by
    simpa [Xi, invXi, mul_comm] using
      (IsLocalization.Away.mul_invSelf (x := MvPolynomial.X i) (S := A0))
  have hinv :
      reciprocal_chart_away_selfmap (R := R) i invXi = Xi := by
    rw [reciprocal_chart_away_selfmap_X_eq (R := R) i] at hmul
    exact IsUnit.mul_left_cancel hunitInv (by rw [hmul, horig])
  simpa [Xi, invXi] using hinv

/-- Helper for Lemma 10.54.5: composing the reciprocal-chart away self-map with the defining
polynomial substitution recovers the original polynomial algebra map into the away localization. -/
private theorem reciprocal_chart_away_selfmap_comp_polynomialRingHom {n : ℕ} (i : Fin n) :
    (reciprocal_chart_away_selfmap (R := R) i).comp
        (reciprocal_chart_away_polynomialRingHom (R := R) i) =
      algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) := by
  -- It suffices to check the composite on coefficients and polynomial generators.
  apply MvPolynomial.ringHom_ext
  · intro x
    let P := MvPolynomial (Fin n) R
    let A0 := Localization.Away (MvPolynomial.X i : P)
    have hC :
        (reciprocal_chart_away_polynomialRingHom (R := R) i) (MvPolynomial.C x) =
          algebraMap P A0 (MvPolynomial.C x) := by
      simpa [reciprocal_chart_away_polynomialRingHom, A0] using
        (show
          algebraMap R (Localization.Away (MvPolynomial.X i : P)) x =
            algebraMap P (Localization.Away (MvPolynomial.X i : P)) (MvPolynomial.C x) by
          rfl)
    calc
      (reciprocal_chart_away_selfmap (R := R) i)
          ((reciprocal_chart_away_polynomialRingHom (R := R) i) (MvPolynomial.C x))
          =
        (reciprocal_chart_away_selfmap (R := R) i) (algebraMap P A0 (MvPolynomial.C x)) := by
          rw [hC]
      _ = (reciprocal_chart_away_polynomialRingHom (R := R) i) (MvPolynomial.C x) := by
          rw [reciprocal_chart_away_selfmap_algebraMap (R := R) i (MvPolynomial.C x)]
      _ = algebraMap P A0 (MvPolynomial.C x) := hC
  · intro j
    rw [RingHom.comp_apply]
    by_cases hji : j = i
    · subst j
      rw [show (reciprocal_chart_away_polynomialRingHom (R := R) i) (MvPolynomial.X i) =
          IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin n) R) by
            simp [reciprocal_chart_away_polynomialRingHom, reciprocal_chart_away_generator]]
      exact reciprocal_chart_away_selfmap_invSelf (R := R) i
    · rw [show (reciprocal_chart_away_polynomialRingHom (R := R) i) (MvPolynomial.X j) =
          algebraMap (MvPolynomial (Fin n) R)
              (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))
              (MvPolynomial.X j) *
            IsLocalization.Away.invSelf (MvPolynomial.X i : MvPolynomial (Fin n) R) by
            simp [reciprocal_chart_away_polynomialRingHom, reciprocal_chart_away_generator, hji]]
      rw [map_mul]
      rw [reciprocal_chart_away_selfmap_X_ne (R := R) i j hji]
      rw [reciprocal_chart_away_selfmap_invSelf (R := R) i]
      let P := MvPolynomial (Fin n) R
      let A0 := Localization.Away (MvPolynomial.X i : P)
      let Xj : A0 := algebraMap P A0 (MvPolynomial.X j)
      let Xi : A0 := algebraMap P A0 (MvPolynomial.X i)
      let invXi : A0 := IsLocalization.Away.invSelf (MvPolynomial.X i : P)
      have hcancel : invXi * Xi = 1 := by
        simpa [Xi, invXi, mul_comm] using
          (IsLocalization.Away.mul_invSelf (x := MvPolynomial.X i) (S := A0))
      calc
        (Xj * invXi) * Xi = Xj * (invXi * Xi) := by
          simp [Xj, Xi, invXi, mul_left_comm, mul_comm]
        _ = Xj * 1 := by rw [hcancel]
        _ = Xj := by simp

/-- Helper for Lemma 10.54.5: the reciprocal-chart away self-map is involutive. -/
private theorem reciprocal_chart_away_selfmap_involutive {n : ℕ} (i : Fin n) :
    (reciprocal_chart_away_selfmap (R := R) i).comp
        (reciprocal_chart_away_selfmap (R := R) i) =
      RingHom.id
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) := by
  -- Equality of endomorphisms of the away localization is detected on the image of the
  -- polynomial ring, and there the composite reduces to the previous generator calculation.
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin n) R))
  apply RingHom.ext
  intro p
  change
    reciprocal_chart_away_selfmap (R := R) i
      (reciprocal_chart_away_selfmap (R := R) i
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) p)) =
      algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) p
  rw [reciprocal_chart_away_selfmap_algebraMap (R := R) i p]
  exact congrArg (fun f : MvPolynomial (Fin n) R →+*
      Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) => f p)
    (reciprocal_chart_away_selfmap_comp_polynomialRingHom (R := R) i)

/-- Helper for Lemma 10.54.5: the reciprocal-chart coordinate in the residue field sends the pivot
variable to its inverse and every other variable to its quotient by the pivot coordinate. -/
private noncomputable def reciprocal_chart_residue_coordinate {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i j : Fin n) :
    q.asIdeal.ResidueField :=
  if h : j = i then
    (residue_coordinate (R := R) q i)⁻¹
  else
    residue_coordinate (R := R) q j / residue_coordinate (R := R) q i

/-- Helper for Lemma 10.54.5: the reciprocal-chart coordinate in the dominating valuation subring
uses the same formulas as in the residue field, but packages the membership proofs in `A`. -/
private noncomputable def reciprocal_chart_valuation_coordinate {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    (i : Fin n)
    (hiinv : (residue_coordinate (R := R) q i)⁻¹ ∈ A)
    (hquot : ∀ j : Fin n,
      residue_coordinate (R := R) q j / residue_coordinate (R := R) q i ∈ A)
    (j : Fin n) : A :=
  if h : j = i then
    ⟨(residue_coordinate (R := R) q i)⁻¹, hiinv⟩
  else
    ⟨residue_coordinate (R := R) q j / residue_coordinate (R := R) q i, hquot j⟩

/-- Helper for Lemma 10.54.5: forgetting the valuation-subring structure on a reciprocal-chart
coordinate recovers the corresponding residue-field coordinate. -/
private theorem reciprocal_chart_valuation_coordinate_subtype {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    (i : Fin n)
    (hiinv : (residue_coordinate (R := R) q i)⁻¹ ∈ A)
    (hquot : ∀ j : Fin n,
      residue_coordinate (R := R) q j / residue_coordinate (R := R) q i ∈ A)
    (j : Fin n) :
    A.subtype (reciprocal_chart_valuation_coordinate (R := R) q A i hiinv hquot j) =
      reciprocal_chart_residue_coordinate (R := R) q i j := by
  by_cases hj : j = i
  · subst j
    simp [reciprocal_chart_valuation_coordinate, reciprocal_chart_residue_coordinate]
  · simp [reciprocal_chart_valuation_coordinate, reciprocal_chart_residue_coordinate, hj]

/-- Helper for Lemma 10.54.5: the reciprocal-chart polynomial map into the residue field is obtained
by evaluating the polynomial generators at the reciprocal-chart residue coordinates. -/
private noncomputable def reciprocal_chart_residueAlgHom {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n) :
    MvPolynomial (Fin n) R →ₐ[R] q.asIdeal.ResidueField :=
  MvPolynomial.aeval (reciprocal_chart_residue_coordinate (R := R) q i)

/-- Helper for Lemma 10.54.5: the reciprocal-chart polynomial map into the dominating valuation
subring is obtained by evaluating the polynomial generators at the valuation-subring coordinates. -/
private noncomputable def reciprocal_chart_valuationAlgHom {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    (hA : ∀ x : R, algebraMap R q.asIdeal.ResidueField x ∈ A)
    (i : Fin n)
    (hiinv : (residue_coordinate (R := R) q i)⁻¹ ∈ A)
    (hquot : ∀ j : Fin n,
      residue_coordinate (R := R) q j / residue_coordinate (R := R) q i ∈ A) :
    letI : Algebra R A :=
      ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA).toAlgebra
    MvPolynomial (Fin n) R →ₐ[R] A :=
  letI : Algebra R A :=
    ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA).toAlgebra
  MvPolynomial.aeval (reciprocal_chart_valuation_coordinate (R := R) q A i hiinv hquot)

/-- Helper for Lemma 10.54.5: the reciprocal-chart prime is the kernel of the residue-field chart
map. -/
private noncomputable def reciprocal_chart_prime {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n) :
    PrimeSpectrum (MvPolynomial (Fin n) R) :=
  ⟨RingHom.ker (reciprocal_chart_residueAlgHom (R := R) q i).toRingHom,
    RingHom.ker_isPrime (reciprocal_chart_residueAlgHom (R := R) q i).toRingHom⟩

/-- Helper for Lemma 10.54.5: composing the valuation-subring chart map with the subtype map back
to the residue field recovers the residue-field chart map. -/
private theorem reciprocal_chart_valuation_subtype_comp {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    (hA : ∀ x : R, algebraMap R q.asIdeal.ResidueField x ∈ A)
    (i : Fin n)
    (hiinv : (residue_coordinate (R := R) q i)⁻¹ ∈ A)
    (hquot : ∀ j : Fin n,
      residue_coordinate (R := R) q j / residue_coordinate (R := R) q i ∈ A) :
    letI : Algebra R A :=
      ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA).toAlgebra
    A.subtype.comp (reciprocal_chart_valuationAlgHom (R := R) q A hA i hiinv hquot).toRingHom =
      (reciprocal_chart_residueAlgHom (R := R) q i).toRingHom := by
  letI : Algebra R A :=
    ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA).toAlgebra
  let ηA : MvPolynomial (Fin n) R →ₐ[R] A :=
    reciprocal_chart_valuationAlgHom (R := R) q A hA i hiinv hquot
  let ηK : MvPolynomial (Fin n) R →ₐ[R] q.asIdeal.ResidueField :=
    reciprocal_chart_residueAlgHom (R := R) q i
  -- Compare the two polynomial maps on coefficients and on the polynomial generators.
  apply MvPolynomial.ringHom_ext
  · intro x
    calc
      (A.subtype.comp ηA.toRingHom)
          (MvPolynomial.C x) = A.subtype (algebraMap R A x) := by
            simp [ηA, reciprocal_chart_valuationAlgHom, RingHom.comp_apply]
      _ = algebraMap R q.asIdeal.ResidueField x := rfl
      _ = ηK.toRingHom (MvPolynomial.C x) := by
            symm
            exact MvPolynomial.algHom_C ηK x
  · intro j
    change A.subtype (ηA.toRingHom (MvPolynomial.X j)) = ηK.toRingHom (MvPolynomial.X j)
    simpa [ηA, ηK, reciprocal_chart_valuationAlgHom, reciprocal_chart_residueAlgHom] using
      reciprocal_chart_valuation_coordinate_subtype
        (R := R) q A i hiinv hquot j

/-- Helper for Lemma 10.54.5: the reciprocal-chart prime still satisfies the easy-branch
properness condition over `maximalIdeal R`. -/
private theorem reciprocal_chart_prime_proper_over_maximalIdeal {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R))
    (A : ValuationSubring q.asIdeal.ResidueField)
    (hA : ∀ x : R, algebraMap R q.asIdeal.ResidueField x ∈ A)
    (hlocal : IsLocalHom ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA))
    (i : Fin n)
    (hiinv : (residue_coordinate (R := R) q i)⁻¹ ∈ A)
    (hquot : ∀ j : Fin n,
      residue_coordinate (R := R) q j / residue_coordinate (R := R) q i ∈ A) :
    (reciprocal_chart_prime (R := R) q i).asIdeal +
        Ideal.map MvPolynomial.C (maximalIdeal R) ≠ ⊤ := by
  letI : Algebra R A :=
    ((algebraMap R q.asIdeal.ResidueField).codRestrict A.toSubring hA).toAlgebra
  let ηA : MvPolynomial (Fin n) R →ₐ[R] A :=
    reciprocal_chart_valuationAlgHom (R := R) q A hA i hiinv hquot
  let qchart := reciprocal_chart_prime (R := R) q i
  have hker :
      qchart.asIdeal ≤ RingHom.ker ηA.toRingHom := by
    intro x hx
    have hx0 :
        (reciprocal_chart_residueAlgHom (R := R) q i) x = 0 := by
      simpa [qchart, reciprocal_chart_prime, RingHom.mem_ker] using hx
    apply A.subtype_injective
    change (A.subtype.comp ηA.toRingHom) x = A.subtype 0
    rw [reciprocal_chart_valuation_subtype_comp (R := R) q A hA i hiinv hquot]
    simpa [ηA] using hx0
  -- The valuation-subring chart map lands in a local target over `R`, so the easy-branch
  -- properness argument applies to the chart prime as well.
  exact prime_plus_maximalIdeal_ne_top_of_local_target (R := R) qchart ηA hlocal hker

/-- Helper for Lemma 10.54.5: the reciprocal-chart away self-map fixes the image of the base ring
`R` inside the principal localization. -/
private theorem reciprocal_chart_away_selfmap_commutes {n : ℕ} (i : Fin n) (x : R) :
    reciprocal_chart_away_selfmap (R := R) i
        (algebraMap R
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) x) =
      algebraMap R
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) x := by
  let P := MvPolynomial (Fin n) R
  -- Re-express the scalar as the constant polynomial `C x` and evaluate the defining substitution.
  change reciprocal_chart_away_selfmap (R := R) i
      (algebraMap P
        (Localization.Away (MvPolynomial.X i : P))
        (MvPolynomial.C x)) =
    algebraMap R (Localization.Away (MvPolynomial.X i : P)) x
  rw [reciprocal_chart_away_selfmap_algebraMap (R := R) i (MvPolynomial.C x)]
  simp [reciprocal_chart_away_polynomialRingHom]

/-- Helper for Lemma 10.54.5: the reciprocal-chart away self-map is an `R`-algebra endomorphism
of the principal localization `P[1 / X_i]`. -/
private noncomputable def reciprocal_chart_away_selfAlgHom {n : ℕ} (i : Fin n) :
    Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) →ₐ[R]
      Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) :=
  { toRingHom := reciprocal_chart_away_selfmap (R := R) i
    commutes' := reciprocal_chart_away_selfmap_commutes (R := R) i }

/-- Helper for Lemma 10.54.5: the reciprocal-chart away self-map is involutive as an
`R`-algebra endomorphism. -/
private theorem reciprocal_chart_away_selfAlgHom_involutive {n : ℕ} (i : Fin n) :
    (reciprocal_chart_away_selfAlgHom (R := R) i).comp
        (reciprocal_chart_away_selfAlgHom (R := R) i) =
      AlgHom.id R
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) := by
  -- The algebra-hom statement is the ring-hom involution upgraded through extensionality.
  apply AlgHom.ext
  intro x
  exact congrArg
    (fun f :
        Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) →+*
          Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) =>
      f x)
    (reciprocal_chart_away_selfmap_involutive (R := R) i)

/-- Helper for Lemma 10.54.5: the reciprocal-chart away self-map packages to an `R`-algebra
equivalence of the principal localization. -/
private noncomputable def reciprocal_chart_away_algEquiv {n : ℕ} (i : Fin n) :
    Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) ≃ₐ[R]
      Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) :=
  AlgEquiv.ofAlgHom
    (reciprocal_chart_away_selfAlgHom (R := R) i)
    (reciprocal_chart_away_selfAlgHom (R := R) i)
    (reciprocal_chart_away_selfAlgHom_involutive (R := R) i)
    (reciprocal_chart_away_selfAlgHom_involutive (R := R) i)

/-- Helper for Lemma 10.54.5: the canonical away-local map to the residue field sends the pivot
variable to a unit because that coordinate is nonzero in `κ(q)`. -/
private noncomputable def reciprocal_chart_away_residueRingHom {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n)
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R) →+*
      q.asIdeal.ResidueField :=
  Localization.awayLift
    (algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField)
    (MvPolynomial.X i)
    (isUnit_iff_ne_zero.mpr hi0)

/-- Helper for Lemma 10.54.5: the canonical away-local prime over `q` is the kernel of the
away-to-residue map. -/
private noncomputable def reciprocal_chart_away_prime {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n)
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    PrimeSpectrum (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)) :=
  ⟨RingHom.ker (reciprocal_chart_away_residueRingHom (R := R) q i hi0),
    RingHom.ker_isPrime (reciprocal_chart_away_residueRingHom (R := R) q i hi0)⟩

/-- Helper for Lemma 10.54.5: the away-to-residue map extends the original polynomial residue map
on the source ring `P`. -/
private theorem reciprocal_chart_away_residueRingHom_comp_algebraMap {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n)
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    (reciprocal_chart_away_residueRingHom (R := R) q i hi0).comp
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))) =
      algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField := by
  -- This is the defining property of the away lift from `P` to `κ(q)`.
  simpa [reciprocal_chart_away_residueRingHom] using
    (IsLocalization.Away.lift_comp
      (S := q.asIdeal.ResidueField)
      (g := algebraMap (MvPolynomial (Fin n) R) q.asIdeal.ResidueField)
      (x := MvPolynomial.X i)
      (hg := isUnit_iff_ne_zero.mpr hi0))

/-- Helper for Lemma 10.54.5: after applying the away involution and then reducing mod `q`, one
recovers the reciprocal-chart residue map on the polynomial ring. -/
private theorem reciprocal_chart_away_residue_comp_selfmap {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n)
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    ((reciprocal_chart_away_residueRingHom (R := R) q i hi0).comp
        (reciprocal_chart_away_algEquiv (R := R) i).toRingHom).comp
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))) =
      (reciprocal_chart_residueAlgHom (R := R) q i).toRingHom := by
  let P := MvPolynomial (Fin n) R
  let A0 := Localization.Away (MvPolynomial.X i : P)
  let ξAway : A0 →+* q.asIdeal.ResidueField :=
    reciprocal_chart_away_residueRingHom (R := R) q i hi0
  let ξ : P →ₐ[R] q.asIdeal.ResidueField :=
    reciprocal_chart_residueAlgHom (R := R) q i
  have hξXi :
      ξ.toRingHom (MvPolynomial.X i) =
        reciprocal_chart_residue_coordinate (R := R) q i i := by
    -- Evaluating the reciprocal-chart polynomial map on `X i` returns the pivot coordinate.
    change
      (MvPolynomial.aeval (reciprocal_chart_residue_coordinate (R := R) q i))
          (MvPolynomial.X i) =
        reciprocal_chart_residue_coordinate (R := R) q i i
    exact MvPolynomial.aeval_X (f := reciprocal_chart_residue_coordinate (R := R) q i) i
  have hξXj (j : Fin n) :
      ξ.toRingHom (MvPolynomial.X j) =
        reciprocal_chart_residue_coordinate (R := R) q i j := by
    -- The same `aeval_X` formula reads off every chart coordinate.
    change
      (MvPolynomial.aeval (reciprocal_chart_residue_coordinate (R := R) q i))
          (MvPolynomial.X j) =
        reciprocal_chart_residue_coordinate (R := R) q i j
    exact MvPolynomial.aeval_X (f := reciprocal_chart_residue_coordinate (R := R) q i) j
  have hXi :
      ξAway (algebraMap P A0 (MvPolynomial.X i)) =
        residue_coordinate (R := R) q i := by
    -- The away-to-residue map extends the original polynomial residue map on `X i`.
    simpa [residue_coordinate] using
      congrArg
        (fun f : P →+* q.asIdeal.ResidueField => f (MvPolynomial.X i))
        (reciprocal_chart_away_residueRingHom_comp_algebraMap (R := R) q i hi0)
  have hXj (j : Fin n) :
      ξAway (algebraMap P A0 (MvPolynomial.X j)) =
        residue_coordinate (R := R) q j := by
    -- The same extension formula reads off every residue coordinate.
    simpa [residue_coordinate] using
      congrArg
        (fun f : P →+* q.asIdeal.ResidueField => f (MvPolynomial.X j))
        (reciprocal_chart_away_residueRingHom_comp_algebraMap (R := R) q i hi0)
  have hInv :
      ξAway (IsLocalization.Away.invSelf (MvPolynomial.X i : P)) =
        (residue_coordinate (R := R) q i)⁻¹ := by
    -- Apply the residue map to the defining inverse relation `X i * invSelf = 1`.
    have hmul0 :
        ξAway (algebraMap P A0 (MvPolynomial.X i)) *
            ξAway (IsLocalization.Away.invSelf (MvPolynomial.X i : P)) = 1 := by
      simpa [map_mul] using
        congrArg ξAway
          (IsLocalization.Away.mul_invSelf (x := MvPolynomial.X i) (S := A0))
    have hmul :
        residue_coordinate (R := R) q i *
            ξAway (IsLocalization.Away.invSelf (MvPolynomial.X i : P)) = 1 := by
      simpa [hXi] using hmul0
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  -- Compare the two polynomial maps on coefficients and generators.
  apply MvPolynomial.ringHom_ext
  · intro x
    -- Coefficients are fixed because the away involution is `R`-linear.
    calc
      (((ξAway.comp (reciprocal_chart_away_algEquiv (R := R) i).toRingHom).comp
          (algebraMap P A0)) (MvPolynomial.C x)) =
          ξAway
            (reciprocal_chart_away_selfmap (R := R) i (algebraMap R A0 x)) := by
              rfl
      _ = ξAway (algebraMap R A0 x) := by
            rw [reciprocal_chart_away_selfmap_commutes (R := R) i x]
      _ = algebraMap R q.asIdeal.ResidueField x := by
            simpa using
              congrArg
                (fun f : P →+* q.asIdeal.ResidueField => f (MvPolynomial.C x))
                (reciprocal_chart_away_residueRingHom_comp_algebraMap (R := R) q i hi0)
      _ = ξ.toRingHom (MvPolynomial.C x) := by
            symm
            exact MvPolynomial.algHom_C ξ x
  · intro j
    by_cases hji : j = i
    · subst j
      -- On the pivot generator, the away involution produces the canonical inverse.
      calc
        (((ξAway.comp (reciprocal_chart_away_algEquiv (R := R) i).toRingHom).comp
            (algebraMap P A0)) (MvPolynomial.X i)) =
            ξAway (IsLocalization.Away.invSelf (MvPolynomial.X i : P)) := by
              change ξAway
                  (reciprocal_chart_away_selfmap (R := R) i
                    (algebraMap P A0 (MvPolynomial.X i))) =
                ξAway (IsLocalization.Away.invSelf (MvPolynomial.X i : P))
              rw [reciprocal_chart_away_selfmap_X_eq (R := R) i]
        _ = (residue_coordinate (R := R) q i)⁻¹ := hInv
        _ = ξ.toRingHom (MvPolynomial.X i) := by
              calc
                (residue_coordinate (R := R) q i)⁻¹ =
                    reciprocal_chart_residue_coordinate (R := R) q i i := by
                      simp [reciprocal_chart_residue_coordinate]
                _ = ξ.toRingHom (MvPolynomial.X i) := by
                      symm
                      exact hξXi
    · -- On a non-pivot generator, the away involution divides by the pivot coordinate.
      calc
        (((ξAway.comp (reciprocal_chart_away_algEquiv (R := R) i).toRingHom).comp
            (algebraMap P A0)) (MvPolynomial.X j)) =
            ξAway
              (algebraMap P A0 (MvPolynomial.X j) *
                IsLocalization.Away.invSelf (MvPolynomial.X i : P)) := by
                  change ξAway
                      (reciprocal_chart_away_selfmap (R := R) i
                        (algebraMap P A0 (MvPolynomial.X j))) =
                    ξAway
                      (algebraMap P A0 (MvPolynomial.X j) *
                        IsLocalization.Away.invSelf (MvPolynomial.X i : P))
                  rw [reciprocal_chart_away_selfmap_X_ne (R := R) i j hji]
        _ = ξAway (algebraMap P A0 (MvPolynomial.X j)) *
              ξAway (IsLocalization.Away.invSelf (MvPolynomial.X i : P)) := by
                rw [map_mul]
        _ = residue_coordinate (R := R) q j *
              (residue_coordinate (R := R) q i)⁻¹ := by
                rw [hXj, hInv]
        _ = residue_coordinate (R := R) q j / residue_coordinate (R := R) q i := by
              rw [div_eq_mul_inv]
        _ = ξ.toRingHom (MvPolynomial.X j) := by
              calc
                residue_coordinate (R := R) q j / residue_coordinate (R := R) q i =
                    reciprocal_chart_residue_coordinate (R := R) q i j := by
                      simp [reciprocal_chart_residue_coordinate, hji]
                _ = ξ.toRingHom (MvPolynomial.X j) := by
                      symm
                      exact hξXj j

/-- Helper for Lemma 10.54.5: the canonical away prime contracts back to the original prime `q`. -/
private theorem reciprocal_chart_away_prime_comap_eq {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n)
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    PrimeSpectrum.comap
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)))
        (reciprocal_chart_away_prime (R := R) q i hi0) =
      q := by
  -- Contract the kernel prime along `P → P[1 / X_i]` and identify the resulting kernel in `P`.
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, reciprocal_chart_away_prime]
  change RingHom.ker
      ((reciprocal_chart_away_residueRingHom (R := R) q i hi0).comp
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)))) =
    q.asIdeal
  rw [reciprocal_chart_away_residueRingHom_comp_algebraMap (R := R) q i hi0]
  simpa using
    (Ideal.ker_algebraMap_residueField
      (R := MvPolynomial (Fin n) R) (I := q.asIdeal))

/-- Helper for Lemma 10.54.5: after transporting the canonical away prime by the reciprocal-chart
away involution and contracting back to `P`, one recovers `reciprocal_chart_prime q i`. -/
private theorem reciprocal_chart_transported_away_prime_comap_eq {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n)
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    PrimeSpectrum.comap
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)))
        (PrimeSpectrum.comap
          (reciprocal_chart_away_algEquiv (R := R) i).toRingHom
          (reciprocal_chart_away_prime (R := R) q i hi0)) =
      reciprocal_chart_prime (R := R) q i := by
  -- Reduce the double contraction to an equality of kernels of polynomial maps to `κ(q)`.
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal,
    reciprocal_chart_away_prime, reciprocal_chart_prime]
  change RingHom.ker
      (((reciprocal_chart_away_residueRingHom (R := R) q i hi0).comp
          (reciprocal_chart_away_algEquiv (R := R) i).toRingHom).comp
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R)))) =
    RingHom.ker (reciprocal_chart_residueAlgHom (R := R) q i).toRingHom
  rw [reciprocal_chart_away_residue_comp_selfmap (R := R) q i hi0]

/-- Helper for Lemma 10.54.5: a contraction equality identifies the localization of the source
polynomial ring at a prime with the localization at the corresponding prime of the away chart. -/
private noncomputable def reciprocal_chart_localization_atPrime_algEquiv_of_comap_eq {n : ℕ}
    (i : Fin n) {I : Ideal (MvPolynomial (Fin n) R)} [I.IsPrime]
    {J : Ideal (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))} [J.IsPrime]
    (hI :
      I = Ideal.comap
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) R))) J) :
    Localization.AtPrime I ≃ₐ[R] Localization.AtPrime J := by
  subst hI
  -- Collapse the iterated localization directly after substituting the contracted prime.
  simpa using
    ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin n) R))
      (p := J)).restrictScalars R)

/-- Helper for Lemma 10.54.5: there exists an `R`-algebra equivalence between the localization at
the reciprocal-chart prime and the original localization at `q`. -/
private theorem exists_reciprocal_chart_localization_algEquiv {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n)
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    ∃ e : Localization.AtPrime (reciprocal_chart_prime (R := R) q i).asIdeal ≃ₐ[R]
        Localization.AtPrime q.asIdeal, True := by
  let P := MvPolynomial (Fin n) R
  let A0 := Localization.Away (MvPolynomial.X i : P)
  let qAway := reciprocal_chart_away_prime (R := R) q i hi0
  let qAwayChart :=
    PrimeSpectrum.comap (reciprocal_chart_away_algEquiv (R := R) i).toRingHom qAway
  have hChart :
      Ideal.comap (algebraMap P A0) qAwayChart.asIdeal =
        (reciprocal_chart_prime (R := R) q i).asIdeal := by
    -- Route correction: read the transported chart prime as a contraction from the away chart.
    simpa [qAwayChart, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal
        (reciprocal_chart_transported_away_prime_comap_eq (R := R) q i hi0)
  have hQ :
      Ideal.comap (algebraMap P A0) qAway.asIdeal = q.asIdeal := by
    -- The canonical away prime contracts back to the original prime `q`.
    simpa [PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal
        (reciprocal_chart_away_prime_comap_eq (R := R) q i hi0)
  have hChart' :
      (reciprocal_chart_prime (R := R) q i).asIdeal =
        Ideal.comap (algebraMap P A0) qAwayChart.asIdeal := hChart.symm
  have hQ' : q.asIdeal = Ideal.comap (algebraMap P A0) qAway.asIdeal := hQ.symm
  let eChart :
      Localization.AtPrime (reciprocal_chart_prime (R := R) q i).asIdeal ≃ₐ[R]
        Localization.AtPrime qAwayChart.asIdeal :=
    -- Collapse the chart-side iterated localization using the transported contraction equality.
    reciprocal_chart_localization_atPrime_algEquiv_of_comap_eq
      (R := R)
      (i := i)
      (I := (reciprocal_chart_prime (R := R) q i).asIdeal)
      (J := qAwayChart.asIdeal)
      hChart'
  let eMid :
      Localization.AtPrime qAwayChart.asIdeal ≃ₐ[R]
        Localization.AtPrime qAway.asIdeal :=
    Localization.localAlgEquiv
      (R := R)
      (I := qAwayChart.asIdeal)
      (J := qAway.asIdeal)
      (reciprocal_chart_away_algEquiv (R := R) i)
      (by
        change Ideal.comap (reciprocal_chart_away_algEquiv (R := R) i).toRingHom qAway.asIdeal =
          Ideal.comap (reciprocal_chart_away_algEquiv (R := R) i).toRingHom qAway.asIdeal
        rfl)
  let eQ : Localization.AtPrime q.asIdeal ≃ₐ[R] Localization.AtPrime qAway.asIdeal :=
    -- Collapse the original iterated localization at the canonical away prime over `q`.
    reciprocal_chart_localization_atPrime_algEquiv_of_comap_eq
      (R := R)
      (i := i)
      (I := q.asIdeal)
      (J := qAway.asIdeal)
      hQ'
  refine ⟨eChart.trans (eMid.trans eQ.symm), trivial⟩

/-- Helper for Lemma 10.54.5: the reciprocal-chart prime should have localization equivalent to the
original localization at `q`. -/
private noncomputable def reciprocal_chart_localization_algEquiv {n : ℕ}
    (q : PrimeSpectrum (MvPolynomial (Fin n) R)) (i : Fin n)
    (hi0 : residue_coordinate (R := R) q i ≠ 0) :
    Localization.AtPrime (reciprocal_chart_prime (R := R) q i).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  Classical.choose (exists_reciprocal_chart_localization_algEquiv (R := R) q i hi0)

-- Proof sketch: choose an essential finite type presentation of `φ`, reduce to a localization of a
-- finite polynomial algebra over `R`, and then use the local hypotheses together with the valuation
-- ring argument from the text to find a maximal ideal of the polynomial ring lying over
-- `maximalIdeal R`. The resulting local ring maps to `S`, and `S` is explicitly a localization of
-- a quotient of that local ring.
/-- Lemma 10.54.5: if `φ : R →+* S` is essentially of finite type and `R` and `S` are local,
then there is a maximal ideal `m` of a finite polynomial ring over `R` lying over
`maximalIdeal R` such that `φ` factors through `Localization.AtPrime m.asIdeal`, and `S` is a
localization of a quotient of that local ring. -/
theorem exists_localized_polynomial_quotient_presentation
    (φ : R →+* S) (hφ : φ.EssFiniteType) :
    ∃ (n : ℕ)
      (m : { m : MaximalSpectrum (MvPolynomial (Fin n) R) //
        Ideal.comap MvPolynomial.C m.asIdeal = maximalIdeal R })
      (ψ : Localization.AtPrime m.1.asIdeal →+* S),
        RingHom.IsLocalizationOfQuotient ψ ∧
          φ = ψ.comp (algebraMap R (Localization.AtPrime m.1.asIdeal)) :=
  by
    classical
    obtain ⟨n, q, ψq, hψqsurj, hψq, hφq⟩ :=
      exists_prime_localized_polynomial_presentation (R := R) (S := S) φ hφ
    by_cases hq : q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) ≠ ⊤
    · obtain ⟨m, hqm, hmcomap⟩ := exists_maximal_over_maximalIdeal_of_not_top
        (R := R) q hq
      letI : m.asIdeal.IsPrime := Ideal.IsMaximal.isPrime m.isMaximal
      have hρ :
          m.asIdeal.primeCompl ≤ q.asIdeal.primeCompl.comap (RingHom.id _) :=
        (Localization.le_comap_primeCompl_iff (I := m.asIdeal) (J := q.asIdeal)
          (f := RingHom.id _)).2 (by simpa using hqm)
      let ρ : Localization.AtPrime m.asIdeal →+* Localization.AtPrime q.asIdeal :=
        IsLocalization.map
          (R := MvPolynomial (Fin n) R)
          (P := MvPolynomial (Fin n) R)
          (S := Localization.AtPrime m.asIdeal)
          (Q := Localization.AtPrime q.asIdeal)
          (M := m.asIdeal.primeCompl)
          (T := q.asIdeal.primeCompl)
          (g := RingHom.id _) hρ
      let ψ : Localization.AtPrime m.asIdeal →+* S := ψq.comp ρ
      refine ⟨n, ⟨m, hmcomap⟩, ψ, ?_⟩
      constructor
      · -- Reuse the easy-branch transport lemma: localizing the source further at `m` preserves
        -- the quotient-localization presentation of `S`.
        exact isLocalizationOfQuotient_comp_source_localization_atPrime
          (A := MvPolynomial (Fin n) R) (T := S) hqm ψq hψq
      · -- The source-localization map does not alter the structural `R`-algebra factorization.
        ext x
        have hρx :
            ρ (algebraMap R (Localization.AtPrime m.asIdeal) x) =
              algebraMap R (Localization.AtPrime q.asIdeal) x := by
          change
            (IsLocalization.map
              (R := MvPolynomial (Fin n) R)
              (P := MvPolynomial (Fin n) R)
              (S := Localization.AtPrime m.asIdeal)
              (Q := Localization.AtPrime q.asIdeal)
              (M := m.asIdeal.primeCompl)
              (T := q.asIdeal.primeCompl)
              (g := RingHom.id _) hρ)
                (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime m.asIdeal)
                  (MvPolynomial.C x)) =
              algebraMap R (Localization.AtPrime q.asIdeal) x
          rw [IsLocalization.map_eq]
          rfl
        calc
          φ x = ψq (algebraMap R (Localization.AtPrime q.asIdeal) x) := by
            simpa [RingHom.comp_apply] using congrArg (fun f : R →+* S => f x) hφq
          _ = ψq (ρ (algebraMap R (Localization.AtPrime m.asIdeal) x)) := by rw [hρx]
    · -- Route correction: the remaining source-faithful step is the valuation-ring chart argument
      -- from the textbook, which replaces `q` by an equivalent reciprocal-coordinate chart prime
      -- satisfying the easy-case properness condition.
      let K := q.asIdeal.ResidueField
      obtain ⟨A, hA, hlocalA⟩ := IsLocalRing.exists_factor_valuationRing (f := algebraMap R K)
      have hqtop : q.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) = ⊤ := by
        exact not_not.mp hq
      obtain ⟨i, hi0, hiinv, hquot⟩ :=
        exists_pivot_coordinate_for_reciprocal_chart (R := R) q A hA hlocalA hqtop
      let qchart := reciprocal_chart_prime (R := R) q i
      have hqchart :
          qchart.asIdeal + Ideal.map MvPolynomial.C (maximalIdeal R) ≠ ⊤ := by
        -- The source proof returns to the easy branch once the chart prime is seen to lie over a
        -- proper ideal above `maximalIdeal R`.
        exact reciprocal_chart_prime_proper_over_maximalIdeal
          (R := R) q A hA hlocalA i hiinv hquot
      let eChart := reciprocal_chart_localization_algEquiv (R := R) q i hi0
      let ψchart : Localization.AtPrime qchart.asIdeal →+* S := ψq.comp eChart.toRingHom
      have hψchart_surj : Function.Surjective ψchart := hψqsurj.comp eChart.surjective
      have hψchart : RingHom.IsLocalizationOfQuotient ψchart :=
        isLocalizationOfQuotient_of_surjective ψchart hψchart_surj
      have hφchart :
          φ = ψchart.comp (algebraMap R (Localization.AtPrime qchart.asIdeal)) := by
        -- Once the localization equivalence is in place, the structural factorization of `φ`
        -- transports along it by the commutativity of `eChart`.
        ext x
        change φ x = ψq (eChart (algebraMap R (Localization.AtPrime qchart.asIdeal) x))
        rw [eChart.commutes]
        simpa [ψchart, RingHom.comp_apply] using
          congrArg (fun f : R →+* S => f x) hφq
      obtain ⟨m, hqm, hmcomap⟩ := exists_maximal_over_maximalIdeal_of_not_top
        (R := R) qchart hqchart
      letI : m.asIdeal.IsPrime := Ideal.IsMaximal.isPrime m.isMaximal
      have hρ :
          m.asIdeal.primeCompl ≤ qchart.asIdeal.primeCompl.comap (RingHom.id _) :=
        (Localization.le_comap_primeCompl_iff (I := m.asIdeal) (J := qchart.asIdeal)
          (f := RingHom.id _)).2 (by simpa using hqm)
      let ρ : Localization.AtPrime m.asIdeal →+* Localization.AtPrime qchart.asIdeal :=
        IsLocalization.map
          (R := MvPolynomial (Fin n) R)
          (P := MvPolynomial (Fin n) R)
          (S := Localization.AtPrime m.asIdeal)
          (Q := Localization.AtPrime qchart.asIdeal)
          (M := m.asIdeal.primeCompl)
          (T := qchart.asIdeal.primeCompl)
          (g := RingHom.id _) hρ
      let ψ : Localization.AtPrime m.asIdeal →+* S := ψchart.comp ρ
      refine ⟨n, ⟨m, hmcomap⟩, ψ, ?_⟩
      constructor
      · -- Re-enter the easy branch after replacing `q` by the reciprocal-chart prime.
        exact isLocalizationOfQuotient_comp_source_localization_atPrime
          (A := MvPolynomial (Fin n) R) (T := S) hqm ψchart hψchart
      · -- The final factorization is the transported chart factorization followed by the source
        -- localization map from the maximal ideal `m`.
        ext x
        have hρx :
            ρ (algebraMap R (Localization.AtPrime m.asIdeal) x) =
              algebraMap R (Localization.AtPrime qchart.asIdeal) x := by
          change
            (IsLocalization.map
              (R := MvPolynomial (Fin n) R)
              (P := MvPolynomial (Fin n) R)
              (S := Localization.AtPrime m.asIdeal)
              (Q := Localization.AtPrime qchart.asIdeal)
              (M := m.asIdeal.primeCompl)
              (T := qchart.asIdeal.primeCompl)
              (g := RingHom.id _) hρ)
                (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime m.asIdeal)
                  (MvPolynomial.C x)) =
              algebraMap R (Localization.AtPrime qchart.asIdeal) x
          rw [IsLocalization.map_eq]
          rfl
        calc
          φ x = ψchart (algebraMap R (Localization.AtPrime qchart.asIdeal) x) := by
            simpa [RingHom.comp_apply] using congrArg (fun f : R →+* S => f x) hφchart
          _ = ψchart (ρ (algebraMap R (Localization.AtPrime m.asIdeal) x)) := by rw [hρx]

end
