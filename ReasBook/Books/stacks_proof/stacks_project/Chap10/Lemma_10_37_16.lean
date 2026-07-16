import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Pi
import stacks_proof.stacks_project.Chap10.Definition_10_37_11
import stacks_proof.stacks_project.Chap10.Lemma_10_25_4
import stacks_proof.stacks_project.Chap10.Lemma_10_36_10
import stacks_proof.stacks_project.Chap10.Lemma_10_37_12
import stacks_proof.stacks_project.Chap10.Lemma_10_37_15
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

/-- Helper for Chap10 Lemma 10 37 16: every minimal prime carries its canonical prime-ideal
instance. -/
local instance minimalPrime_isPrime (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Chap10 Lemma 10 37 16: if an element of `R` maps to zero in the localization at a
minimal prime, then it already lies in that minimal prime. -/
lemma minimalPrime_mem_of_localization_zero (p : minimalPrimes R) {x : R}
    (hx : algebraMap R (Localization.AtPrime p.1) x = 0) :
    x ∈ p.1 := by
  have hxmem :
      algebraMap R (Localization.AtPrime p.1) x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.1) := by
    rw [IsLocalRing.mem_maximalIdeal]
    simpa [hx]
  exact
    (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (S := Localization.AtPrime p.1) p.1 x).1 hxmem

variable [IsReduced R]

/-- Helper for Chap10 Lemma 10 37 16: in a reduced ring, the radical of `⊥` is `⊥`. -/
lemma radical_bot_eq_bot : (⊥ : Ideal R).radical = ⊥ := by
  -- Reducedness identifies the nilradical with the zero ideal.
  simpa [nilradical, Ideal.zero_eq_bot] using nilradical_eq_zero R

/-- Helper for Chap10 Lemma 10 37 16: localizing a reduced ring at a minimal prime produces a
field. -/
theorem minimalPrime_localization_isField (p : minimalPrimes R) :
    IsField (Localization.AtPrime p.1) := by
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p.1) :=
    Ring.KrullDimLE.of_isLocalization p.1 p.2 (Localization.AtPrime p.1)
  exact Ring.KrullDimLE.isField_of_isReduced

/-- Helper for Chap10 Lemma 10 37 16: every idempotent element is integral over the base ring. -/
lemma isIntegral_of_isIdempotentElem {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (hx : IsIdempotentElem x) : IsIntegral A x := by
  -- The monic polynomial `X * (X - 1)` vanishes on any idempotent.
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : A)), ?_, ?_⟩
  · exact Polynomial.Monic.mul Polynomial.monic_X (Polynomial.monic_X_sub_C 1)
  · simpa [hx.eq, sub_eq_add_neg, mul_add]

/-- Helper for Chap10 Lemma 10 37 16: normality transports across ring equivalences. -/
theorem isNormalRing_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) [IsNormalRing A] : IsNormalRing B := by
  refine ⟨fun p ↦ ?_⟩
  let q : PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom p
  let eLoc :
      Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime p.asIdeal :=
    Localization.localRingEquiv _ _ e (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) p)
  have hDomain : IsDomain (Localization.AtPrime q.asIdeal) := isDomain_localizationAtPrime q
  have hIntegrallyClosed : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_localizationAtPrime q
  refine ⟨?_, ?_⟩
  · -- The localized equivalence transfers the domain structure.
    simpa [eLoc] using
      ((eLoc : Localization.AtPrime q.asIdeal ≃* Localization.AtPrime p.asIdeal).isDomain_iff).mp
        hDomain
  · -- The same equivalence transports integrally closedness.
    exact IsIntegrallyClosed.of_equiv eLoc

/-- Helper for Chap10 Lemma 10 37 16: every element of a minimal prime vanishes in the
corresponding localization. -/
lemma minimalPrime_maps_to_zero_in_localization (p : minimalPrimes R) {x : R}
    (hx : x ∈ p.1) :
    algebraMap R (Localization.AtPrime p.1) x = 0 := by
  letI : Field (Localization.AtPrime p.1) :=
    (minimalPrime_localization_isField (R := R) p).toField
  have hxmem :
      algebraMap R (Localization.AtPrime p.1) x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.1) := by
    exact
      (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (S := Localization.AtPrime p.1) p.1 x).2 hx
  simpa [IsLocalRing.maximalIdeal_eq_bot] using hxmem

/-- Helper for Chap10 Lemma 10 37 16: the quotient by a minimal prime maps canonically to the
corresponding localization. -/
noncomputable abbrev minimalPrimeQuotientToLocalization (p : minimalPrimes R) :
    R ⧸ p.1 →+* Localization.AtPrime p.1 :=
  Ideal.Quotient.lift p.1 (algebraMap R (Localization.AtPrime p.1)) fun _ hx ↦
    minimalPrime_maps_to_zero_in_localization (R := R) p hx

/-- Helper for Chap10 Lemma 10 37 16: on quotient representatives, the canonical
quotient-to-localization map is just the original localization map. -/
@[simp]
lemma minimalPrimeQuotientToLocalization_mk (p : minimalPrimes R) (x : R) :
    minimalPrimeQuotientToLocalization (R := R) p (Ideal.Quotient.mk p.1 x) =
      algebraMap R (Localization.AtPrime p.1) x := by
  -- The quotient lift was defined to agree with the localization map on representatives.
  rfl

/-- Helper for Chap10 Lemma 10 37 16: the quotient by a minimal prime embeds into the corresponding
localization. -/
lemma minimalPrimeQuotientToLocalization_injective (p : minimalPrimes R) :
    Function.Injective (minimalPrimeQuotientToLocalization (R := R) p) := by
  -- Compute the localization kernel exactly as the minimal prime and then invoke the quotient
  -- injectivity criterion.
  rw [Ideal.injective_lift_iff]
  ext x
  constructor
  · intro hx
    exact minimalPrime_mem_of_localization_zero (R := R) p hx
  · intro hx
    exact minimalPrime_maps_to_zero_in_localization (R := R) p hx

/-- Helper for Chap10 Lemma 10 37 16: the canonical quotient-to-localization map provides the
`R / p`-algebra structure on `R_p`. -/
noncomputable local instance minimalPrimeQuotientToLocalization_algebra (p : minimalPrimes R) :
    Algebra (R ⧸ p.1) (Localization.AtPrime p.1) :=
  RingHom.toAlgebra (minimalPrimeQuotientToLocalization (R := R) p)

/-- Helper for Chap10 Lemma 10 37 16: for a minimal prime `p`, the localization `R_p` is the
fraction field of `R / p`. -/
theorem minimalPrime_quotient_isFractionRing (p : minimalPrimes R) :
    IsFractionRing (R ⧸ p.1) (Localization.AtPrime p.1) := by
  -- The quotient map is injective, so it supplies the faithful scalar action required by the
  -- fraction-field constructor for fields.
  letI : Field (Localization.AtPrime p.1) :=
    (minimalPrime_localization_isField (R := R) p).toField
  letI : FaithfulSMul (R ⧸ p.1) (Localization.AtPrime p.1) :=
    (faithfulSMul_iff_algebraMap_injective
      (R ⧸ p.1) (Localization.AtPrime p.1)).2
        (minimalPrimeQuotientToLocalization_injective (R := R) p)
  refine IsFractionRing.of_field (R ⧸ p.1) (Localization.AtPrime p.1) ?_
  intro z
  -- Write an arbitrary element of the prime localization as `x / s`, then descend `x` and `s` to
  -- the quotient by the minimal prime.
  obtain ⟨x, s, hz⟩ := IsLocalization.exists_mk'_eq p.1.primeCompl z
  refine ⟨Ideal.Quotient.mk p.1 x, Ideal.Quotient.mk p.1 s.1, ?_⟩
  rw [← hz]
  have hsne : algebraMap R (Localization.AtPrime p.1) s.1 ≠ 0 := by
    intro hs0
    exact s.2 (minimalPrime_mem_of_localization_zero (R := R) p hs0)
  have hqne :
      algebraMap (R ⧸ p.1) (Localization.AtPrime p.1)
        (Ideal.Quotient.mk p.1 s.1) ≠ 0 := by
    change minimalPrimeQuotientToLocalization (R := R) p
      (Ideal.Quotient.mk p.1 s.1) ≠ 0
    simpa [minimalPrimeQuotientToLocalization_mk] using hsne
  have hden :
      algebraMap (R ⧸ p.1) (Localization.AtPrime p.1)
          (Ideal.Quotient.mk p.1 s.1) =
        algebraMap R (Localization.AtPrime p.1) s.1 := by
    change minimalPrimeQuotientToLocalization (R := R) p
      (Ideal.Quotient.mk p.1 s.1) = _
    simp
  have hnum :
      algebraMap (R ⧸ p.1) (Localization.AtPrime p.1)
          (Ideal.Quotient.mk p.1 x) =
        algebraMap R (Localization.AtPrime p.1) x := by
    change minimalPrimeQuotientToLocalization (R := R) p
      (Ideal.Quotient.mk p.1 x) = _
    simp
  rw [eq_div_iff_mul_eq hqne]
  rw [hden, hnum]
  exact IsLocalization.mk'_spec (M := p.1.primeCompl)
    (S := Localization.AtPrime p.1) x s

/-- Helper for Chap10 Lemma 10 37 16: the union of the minimal primes of a reduced ring is exactly
the complement of the nonzerodivisors. -/
lemma iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors :
    (⋃ p : minimalPrimes R, (p.1 : Set R)) = { x : R | x ∉ nonZeroDivisors R } := by
  -- Specialize the standard zerodivisor description to `I = ⊥`.
  rw [show (⋃ p : minimalPrimes R, (p.1 : Set R)) = (⋃ p ∈ minimalPrimes R, (p : Set R)) by
    ext x
    simp]
  rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes by rfl]
  rw [Ideal.iUnion_minimalPrimes]
  ext x
  have hx :
      x ∉ nonZeroDivisors R ↔ { y : R | x * y = 0 ∧ y ≠ 0 }.Nonempty :=
    notMem_nonZeroDivisors_iff_left
  simpa [radical_bot_eq_bot (R := R), Set.nonempty_def, and_comm] using hx.symm

variable [Finite (minimalPrimes R)]

/-- Helper for Chap10 Lemma 10 37 16: every coordinate idempotent in
`∏ p, Localization.AtPrime p.1` is the image of an element of `R` in `FractionRing R`. -/
private lemma liftedPiSingle_mem_range_algebraMap [IsIntegrallyClosed R]
    (p : minimalPrimes R) :
    ∃ r : R,
      fractionRing_equiv_pi_minimalPrimeLocalizations R
          (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
          (algebraMap R (FractionRing R) r) =
        Pi.single p 1 := by
  classical
  let E := fractionRing_equiv_pi_minimalPrimeLocalizations R
      (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
  -- The coordinate idempotent pulls back to an idempotent in `Q(R)`, hence is integral over `R`.
  have hintegral : IsIntegral R
      (E.symm (Pi.single (ι := minimalPrimes R)
        (M := fun q => Localization.AtPrime q.1) p 1)) := by
    have hidemProd : IsIdempotentElem
        (Pi.single (ι := minimalPrimes R)
          (M := fun q => Localization.AtPrime q.1) p 1) := by
      exact (CompleteOrthogonalIdempotents.single
        (fun q : minimalPrimes R => Localization.AtPrime q.1)).idem p
    have hidem : IsIdempotentElem
        (E.symm (Pi.single (ι := minimalPrimes R)
          (M := fun q => Localization.AtPrime q.1) p 1)) := by
      simpa [E] using hidemProd.map E.symm
    exact isIntegral_of_isIdempotentElem (A := R) hidem
  -- Integral closedness of `R` supplies the desired preimage in the total quotient ring.
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hintegral
  refine ⟨r, ?_⟩
  calc
    fractionRing_equiv_pi_minimalPrimeLocalizations R
        (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
        (algebraMap R (FractionRing R) r)
        = E (E.symm (Pi.single (ι := minimalPrimes R)
            (M := fun q => Localization.AtPrime q.1) p 1)) := by
          rw [hr]
    _ = Pi.single p 1 := by
      exact E.apply_symm_apply _

/-- Helper for Chap10 Lemma 10 37 16: integrally closedness lifts the coordinate idempotents in
`Q(R) ≃ ∏ R_p` back to a complete orthogonal family in `R`. -/
lemma lifted_minimalPrime_idempotents_complete [IsIntegrallyClosed R] :
    ∃ e : minimalPrimes R → R,
      CompleteOrthogonalIdempotents e ∧
        ∀ p : minimalPrimes R,
          fractionRing_equiv_pi_minimalPrimeLocalizations R
              (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
              (algebraMap R (FractionRing R) (e p)) =
            Pi.single p 1 := by
  classical
  -- Choose the integral lifts of all coordinate idempotents simultaneously.
  choose e he using fun p : minimalPrimes R =>
    liftedPiSingle_mem_range_algebraMap (R := R) p
  refine ⟨e, ?_, he⟩
  let E := fractionRing_equiv_pi_minimalPrimeLocalizations R
      (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
  let f : R →+* (∀ p : minimalPrimes R, Localization.AtPrime p.1) :=
    E.toRingHom.comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f := by
    exact E.injective.comp (IsFractionRing.injective R (FractionRing R))
  have hmap : f ∘ e = fun p : minimalPrimes R =>
      Pi.single (ι := minimalPrimes R)
        (M := fun q => Localization.AtPrime q.1) p 1 := by
    funext p
    exact he p
  have hsingle : CompleteOrthogonalIdempotents (fun p : minimalPrimes R =>
      Pi.single (ι := minimalPrimes R)
        (M := fun q => Localization.AtPrime q.1) p 1) := by
    exact CompleteOrthogonalIdempotents.single
      (fun q : minimalPrimes R => Localization.AtPrime q.1)
  have hmapComplete : CompleteOrthogonalIdempotents (f ∘ e) := by
    simpa [hmap] using hsingle
  -- Injectivity of `R → Q(R) → ∏ R_p` reflects the complete orthogonal relations to `R`.
  exact (CompleteOrthogonalIdempotents.map_injective_iff f hf).1 hmapComplete

/-- Helper for Chap10 Lemma 10 37 16: the splitting ideal attached to the lifted `p`-th idempotent
is exactly the minimal prime `p`. -/
lemma span_one_sub_lifted_idempotent_eq_minimalPrime {e : minimalPrimes R → R}
    (he :
      ∀ p : minimalPrimes R,
        fractionRing_equiv_pi_minimalPrimeLocalizations R
            (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
            (algebraMap R (FractionRing R) (e p)) =
          Pi.single p 1)
    (p : minimalPrimes R) :
    Ideal.span ({1 - e p} : Set R) = p.1 := by
  let E := fractionRing_equiv_pi_minimalPrimeLocalizations R
      (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
  -- The `p`-coordinate of `e p` is one, so `1 - e p` vanishes in `R_p` and lies in `p`.
  have hpgen : 1 - e p ∈ p.1 := by
    refine minimalPrime_mem_of_localization_zero (R := R) p ?_
    have hep : algebraMap R (Localization.AtPrime p.1) (e p) = 1 := by
      simpa [E] using congrFun (he p) p
    simp [map_sub, hep]
  apply le_antisymm
  · have hsubset : ({1 - e p} : Set R) ⊆ p.1 := by
      intro x hx
      simpa using hx ▸ hpgen
    exact Ideal.span_le.mpr hsubset
  · intro x hx
    -- If `x ∈ p`, then `x` kills the `p`-th idempotent after comparing all product coordinates.
    have hxe_zero : x * e p = 0 := by
      have hprod : E (algebraMap R (FractionRing R) (x * e p)) = 0 := by
        ext q
        by_cases hq : q = p
        · subst q
          have hx0 := minimalPrime_maps_to_zero_in_localization (R := R) p hx
          simp [E, map_mul, hx0]
        · have heq0 : algebraMap R (Localization.AtPrime q.1) (e p) = 0 := by
            simpa [E, Pi.single_eq_of_ne hq] using congrFun (he p) q
          simp [E, map_mul, heq0]
      have hprod' : E (algebraMap R (FractionRing R) (x * e p)) = E 0 := by
        simpa [E] using hprod
      have hfrac : algebraMap R (FractionRing R) (x * e p) = 0 := by
        exact E.injective hprod'
      have hfrac' :
          algebraMap R (FractionRing R) (x * e p) =
            algebraMap R (FractionRing R) 0 := by
        simpa using hfrac
      exact IsFractionRing.injective R (FractionRing R) hfrac'
    have hxmul : x * (1 - e p) = x := by
      rw [mul_sub, mul_one, hxe_zero, sub_zero]
    rw [← hxmul]
    have honeSub_mem : 1 - e p ∈ ({1 - e p} : Set R) := by
      simp
    have honeSub_span : 1 - e p ∈ Ideal.span ({1 - e p} : Set R) :=
      Ideal.subset_span honeSub_mem
    exact Ideal.mul_mem_left _ x honeSub_span

/-- Helper for Chap10 Lemma 10 37 16: the canonical product map to the minimal-prime quotients
is bijective. -/
private lemma minimalPrimeQuotientPiRingHom_bijective [IsIntegrallyClosed R] :
    Function.Bijective
      (Pi.ringHom fun p : minimalPrimes R => Ideal.Quotient.mk p.1) := by
  classical
  obtain ⟨e, hecomp, hecoords⟩ := lifted_minimalPrime_idempotents_complete (R := R)
  have hspan : ∀ p : minimalPrimes R,
      Ideal.span ({1 - e p} : Set R) = p.1 :=
    span_one_sub_lifted_idempotent_eq_minimalPrime (R := R) hecoords
  let g : ((p : minimalPrimes R) → R ⧸ Ideal.span ({1 - e p} : Set R)) ≃+*
      ((p : minimalPrimes R) → R ⧸ p.1) :=
    RingEquiv.piCongrRight fun p =>
      (Ideal.quotientEquivAlgOfEq R (hspan p)).toRingEquiv
  -- Transport the standard idempotent product quotient bijection across the quotient
  -- identifications `span {1 - e p} = p`.
  have hgcomp : g.toRingHom.comp
        (Pi.ringHom fun p : minimalPrimes R =>
          Ideal.Quotient.mk (Ideal.span ({1 - e p} : Set R))) =
      (Pi.ringHom fun p : minimalPrimes R => Ideal.Quotient.mk p.1) := by
    ext x p
    simp [g, Ideal.quotientEquivAlgOfEq_mk]
  rw [← hgcomp]
  exact g.bijective.comp hecomp.bijective_pi

/-- Helper for Chap10 Lemma 10 37 16: the lifted complete orthogonal idempotents split `R` as the
product of the minimal-prime quotients. -/
noncomputable def minimalPrime_quotient_pi_ringEquiv [IsIntegrallyClosed R] :
    R ≃+* ∀ p : minimalPrimes R, R ⧸ p.1 :=
  RingEquiv.ofBijective
    (Pi.ringHom fun p : minimalPrimes R => Ideal.Quotient.mk p.1)
    (minimalPrimeQuotientPiRingHom_bijective (R := R))

/-- Helper for Chap10 Lemma 10 37 16: the nonzerodivisors in a product ring are exactly the
componentwise nonzerodivisors. -/
private lemma pi_nonZeroDivisors_eq {ι : Type*} {S : ι → Type*} [∀ i, CommRing (S i)] :
    nonZeroDivisors (∀ i, S i) =
      Submonoid.pi Set.univ (fun i => nonZeroDivisors (S i)) := by
  classical
  ext x
  constructor
  · intro hx i _
    change x i ∈ nonZeroDivisors (S i)
    rw [mem_nonZeroDivisors_iff] at hx ⊢
    constructor
    · intro y hy
      have hsingle_zero : (Pi.single i y : ∀ j, S j) = 0 := by
        have hmul : x * Pi.single i y = 0 := by
          ext j
          by_cases hji : j = i
          · subst j
            simpa using hy
          · simp [Pi.single_eq_of_ne hji]
        exact hx.1 _ hmul
      simpa using congrFun hsingle_zero i
    · intro y hy
      have hsingle_zero : (Pi.single i y : ∀ j, S j) = 0 := by
        have hmul : Pi.single i y * x = 0 := by
          ext j
          by_cases hji : j = i
          · subst j
            simpa using hy
          · simp [Pi.single_eq_of_ne hji]
        exact hx.2 _ hmul
      simpa using congrFun hsingle_zero i
  · intro hx
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro y hxy
      ext i
      have hcoord : x i * y i = 0 := by
        simpa using congrFun hxy i
      exact (mem_nonZeroDivisors_iff.mp (hx i trivial)).1 (y i) hcoord
    · intro y hxy
      ext i
      have hcoord : y i * x i = 0 := by
        simpa using congrFun hxy i
      exact (mem_nonZeroDivisors_iff.mp (hx i trivial)).2 (y i) hcoord

/-- Helper for Chap10 Lemma 10 37 16: a finite product of fraction rings is the fraction ring of
the finite product. -/
private lemma isFractionRing_pi_of_isFractionRing {ι : Type*} [Finite ι]
    (S K : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, CommRing (K i)] [∀ i, Algebra (S i) (K i)]
    [∀ i, IsFractionRing (S i) (K i)] :
    IsFractionRing (∀ i, S i) (∀ i, K i) := by
  classical
  -- The localization instance for products is stated for the componentwise submonoid; the previous
  -- lemma identifies that submonoid with the product ring's nonzerodivisors.
  change IsLocalization (nonZeroDivisors (∀ i, S i)) (∀ i, K i)
  rw [pi_nonZeroDivisors_eq]
  infer_instance

/-- Helper for Chap10 Lemma 10 37 16: the product of the minimal-prime quotients is integrally
closed inside the product of their fraction fields. -/
private lemma minimalPrimeQuotientPi_isIntegrallyClosedIn_localizations [IsIntegrallyClosed R] :
    IsIntegrallyClosedIn
      ((p : minimalPrimes R) → R ⧸ p.1)
      ((p : minimalPrimes R) → Localization.AtPrime p.1) := by
  classical
  letI : ∀ p : minimalPrimes R,
      IsFractionRing (R ⧸ p.1) (Localization.AtPrime p.1) :=
    fun p => minimalPrime_quotient_isFractionRing (R := R) p
  letI : IsFractionRing ((p : minimalPrimes R) → R ⧸ p.1)
      ((p : minimalPrimes R) → Localization.AtPrime p.1) :=
    isFractionRing_pi_of_isFractionRing
      (fun p : minimalPrimes R => R ⧸ p.1)
      (fun p : minimalPrimes R => Localization.AtPrime p.1)
  have hclosed : IsIntegrallyClosed ((p : minimalPrimes R) → R ⧸ p.1) := by
    exact IsIntegrallyClosed.of_equiv (minimalPrime_quotient_pi_ringEquiv (R := R))
  -- Convert integrally closedness of the product ring to integrally closedness inside the product
  -- of the component fraction rings.
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn
    ((p : minimalPrimes R) → Localization.AtPrime p.1)).mp hclosed

/-- Helper for Chap10 Lemma 10 37 16: every minimal-prime quotient is integrally closed. -/
theorem minimalPrime_quotient_isIntegrallyClosed [IsIntegrallyClosed R]
    (p : minimalPrimes R) :
    IsIntegrallyClosed (R ⧸ p.1) := by
  classical
  letI : IsFractionRing (R ⧸ p.1) (Localization.AtPrime p.1) :=
    minimalPrime_quotient_isFractionRing (R := R) p
  -- Componentwise integrally closedness follows from the product statement via the product API.
  have hpclosed : IsIntegrallyClosedIn (R ⧸ p.1) (Localization.AtPrime p.1) :=
    (isIntegrallyClosedIn_pi_iff.mp
      (minimalPrimeQuotientPi_isIntegrallyClosedIn_localizations (R := R))) p
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn
    (Localization.AtPrime p.1)).2 hpclosed

/-- Chap10 Lemma 10 37 16: for a reduced ring with finitely many minimal primes, the following are
equivalent: `R` is a normal ring, `R` is integrally closed in its total ring of fractions, and
`R` is a finite product of normal domains. -/
-- Proof sketch: combine the normal-ring criterion from the previous lemmas with the description
-- of the total quotient ring as the product of the localizations at the minimal primes. The
-- idempotents in that product split `R` as a finite product of the quotients by its minimal
-- primes. For the domain factors, the chapter's owner predicate for "normal domain" is the
-- canonical `IsIntegrallyClosed`, so the finite-product clause is stated directly with that API.
@[stacks 030C]
theorem normalRing_tfae_isIntegrallyClosed_isFiniteProductOfNormalDomains :
    List.TFAE
      [ IsNormalRing R
      , IsIntegrallyClosed R
      , ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : R ≃+* ∀ i, S i),
          (∀ i, IsDomain (S i)) ∧ ∀ i, IsIntegrallyClosed (S i)
      ] := by
  tfae_have 1 → 2 := fun h ↦ by
    -- A normal ring is integrally closed in its total quotient ring by Lemma 10.37.12.
    letI : IsNormalRing R := h
    exact isIntegrallyClosed_of_isNormalRing (R := R)
  tfae_have 2 → 3 := fun h ↦ by
    classical
    letI : IsIntegrallyClosed R := h
    -- Lift the coordinate idempotents of `Q(R) ≃ ∏ R_p` and split `R` into the minimal-prime
    -- quotients, which are domains and remain integrally closed.
    refine ⟨minimalPrimes R, inferInstance, fun p ↦ R ⧸ p.1, ?_, ?_, ?_⟩
    · intro p
      infer_instance
    · exact minimalPrime_quotient_pi_ringEquiv (R := R)
    · constructor
      · intro p
        haveI : p.1.IsPrime := Ideal.minimalPrimes_isPrime p.2
        infer_instance
      · intro p
        exact minimalPrime_quotient_isIntegrallyClosed (R := R) p
  tfae_have 3 → 1 := fun h ↦ by
    classical
    obtain ⟨ι, hι, S, hS, e, hDomain, hClosed⟩ := h
    letI : Finite ι := hι
    letI : ∀ i, CommRing (S i) := hS
    letI : ∀ i, IsNormalRing (S i) := fun i ↦ by
      letI : IsDomain (S i) := hDomain i
      letI : IsIntegrallyClosed (S i) := hClosed i
      infer_instance
    -- A finite product of normal domains is normal, and ring equivalence transports normality.
    letI : IsNormalRing (∀ i, S i) := isNormalRing_pi
    exact isNormalRing_of_ringEquiv (A := ∀ i, S i) (B := R) e.symm
  tfae_finish

end
