import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Pi
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Lemma_10_25_4
import StacksProject_2024.Chap10.Lemma_10_36_10
import StacksProject_2024.Chap10.Lemma_10_37_12
import StacksProject_2024.Chap10.Lemma_10_37_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

variable [IsReduced R]
variable [Finite (minimalPrimes R)]

/-- Helper for Lemma 10.37.16: every minimal prime carries its canonical prime-ideal instance. -/
local instance minimalPrime_isPrime (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Lemma 10.37.16: in a reduced ring, the radical of `⊥` is `⊥`. -/
lemma radical_bot_eq_bot : (⊥ : Ideal R).radical = ⊥ := by
  -- Reducedness identifies the nilradical with the zero ideal.
  simpa [nilradical, Ideal.zero_eq_bot] using nilradical_eq_zero R

/-- Helper for Lemma 10.37.16: the union of the minimal primes of a reduced ring is exactly the
complement of the nonzerodivisors. -/
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

/-- Helper for Lemma 10.37.16: localizing a reduced ring at a minimal prime produces a field. -/
theorem minimalPrime_localization_isField (p : minimalPrimes R) :
    IsField (Localization.AtPrime p.1) := by
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p.1) :=
    Ring.KrullDimLE.of_isLocalization p.1 p.2 (Localization.AtPrime p.1)
  exact Ring.KrullDimLE.isField_of_isReduced

/-- Helper for Lemma 10.37.16: every idempotent element is integral over the base ring. -/
lemma isIntegral_of_isIdempotentElem {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (hx : IsIdempotentElem x) : IsIntegral A x := by
  -- The monic polynomial `X * (X - 1)` vanishes on any idempotent.
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : A)), ?_, ?_⟩
  · exact Polynomial.Monic.mul Polynomial.monic_X (Polynomial.monic_X_sub_C 1)
  · simpa [hx.eq, sub_eq_add_neg, mul_add]

/-- Helper for Lemma 10.37.16: normality transports across ring equivalences. -/
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

/-- Helper for Lemma 10.37.16: if an element of `R` maps to zero in the localization at a minimal
prime, then it already lies in that minimal prime. -/
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

/-- Helper for Lemma 10.37.16: every element of a minimal prime vanishes in the corresponding
localization. -/
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

/-- Helper for Lemma 10.37.16: the quotient by a minimal prime maps canonically to the
corresponding localization. -/
noncomputable abbrev minimalPrimeQuotientToLocalization (p : minimalPrimes R) :
    R ⧸ p.1 →+* Localization.AtPrime p.1 :=
  Ideal.Quotient.lift p.1 (algebraMap R (Localization.AtPrime p.1)) fun x hx ↦
    minimalPrime_maps_to_zero_in_localization (R := R) p hx

/-- Helper for Lemma 10.37.16: on quotient representatives, the canonical quotient-to-localization
map is just the original localization map. -/
@[simp]
lemma minimalPrimeQuotientToLocalization_mk (p : minimalPrimes R) (x : R) :
    minimalPrimeQuotientToLocalization (R := R) p (Ideal.Quotient.mk p.1 x) =
      algebraMap R (Localization.AtPrime p.1) x := by
  -- The quotient lift was defined to agree with the localization map on representatives.
  rfl

/-- Helper for Lemma 10.37.16: the quotient by a minimal prime embeds into the corresponding
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

/-- Helper for Lemma 10.37.16: the canonical quotient-to-localization map provides the
`R / p`-algebra structure on `R_p`. -/
noncomputable local instance minimalPrimeQuotientToLocalization_algebra (p : minimalPrimes R) :
    Algebra (R ⧸ p.1) (Localization.AtPrime p.1) :=
  RingHom.toAlgebra (minimalPrimeQuotientToLocalization (R := R) p)

/-- Helper for Lemma 10.37.16: for a minimal prime `p`, the localization `R_p` is the fraction
field of `R / p`. -/
theorem minimalPrime_quotient_isFractionRing (p : minimalPrimes R) :
    IsFractionRing (R ⧸ p.1) (Localization.AtPrime p.1) := by
  -- TODO: package `Localization.AtPrime p.1` as the fraction field of `R ⧸ p.1` by reusing the
  -- injective quotient map above, adding the induced `FaithfulSMul` instance, and then expressing
  -- each localization element via `IsLocalization.exists_mk'_eq p.1.primeCompl`.
  sorry

/-- Helper for Lemma 10.37.16: integrally closedness lifts the coordinate idempotents in
`Q(R) ≃ ∏ R_p` back to a complete orthogonal family in `R`. -/
lemma lifted_minimalPrime_idempotents_complete [IsIntegrallyClosed R] :
    ∃ e : minimalPrimes R → R,
      CompleteOrthogonalIdempotents e ∧
        ∀ p : minimalPrimes R,
          fractionRing_equiv_pi_minimalPrimeLocalizations R
              (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
              (algebraMap R (FractionRing R) (e p)) =
            Pi.single p 1 := by
  -- TODO: pull back the coordinate idempotents along
  -- `Q(R) ≃ ∏_{p ∈ MinSpec R} R_p`, then use injectivity of `R → Q(R)` to show the lifted family
  -- is complete orthogonal.
  sorry

/-- Helper for Lemma 10.37.16: the splitting ideal attached to the lifted `p`-th idempotent is
exactly the minimal prime `p`. -/
lemma span_one_sub_lifted_idempotent_eq_minimalPrime {e : minimalPrimes R → R}
    (he :
      ∀ p : minimalPrimes R,
        fractionRing_equiv_pi_minimalPrimeLocalizations R
            (iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors (R := R))
            (algebraMap R (FractionRing R) (e p)) =
          Pi.single p 1)
    (p : minimalPrimes R) :
    Ideal.span ({1 - e p} : Set R) = p.1 := by
  -- TODO: compare the `p`-coordinate of the product embedding to show
  -- `span(1 - e_p) ⊆ p`, then use injectivity of the global embedding and the vanishing of `p`
  -- in `R_p` to prove the reverse inclusion.
  sorry

/-- Helper for Lemma 10.37.16: the lifted complete orthogonal idempotents split `R` as the
product of the minimal-prime quotients. -/
noncomputable def minimalPrime_quotient_pi_ringEquiv [IsIntegrallyClosed R] :
    R ≃+* ∀ p : minimalPrimes R, R ⧸ p.1 :=
  -- TODO: combine `CompleteOrthogonalIdempotents.bijective_pi` with the ideal identifications
  -- from `span_one_sub_lifted_idempotent_eq_minimalPrime`.
  sorry

/-- Helper for Lemma 10.37.16: every minimal-prime quotient is integrally closed. -/
theorem minimalPrime_quotient_isIntegrallyClosed [IsIntegrallyClosed R]
    (p : minimalPrimes R) :
    IsIntegrallyClosed (R ⧸ p.1) := by
  -- TODO: transport global integrally closedness to the product of minimal-prime quotients,
  -- apply `isIntegrallyClosedIn_pi_iff`, and then use
  -- `minimalPrime_quotient_isFractionRing` to pass from integrally closed maps to the owner
  -- predicate `IsIntegrallyClosed`.
  sorry

/-- Lemma 10.37.16: for a reduced ring with finitely many minimal primes, the following are
equivalent: `R` is a normal ring, `R` is integrally closed in its total ring of fractions, and
`R` is a finite product of normal domains. -/
-- Proof sketch: combine the normal-ring criterion from the previous lemmas with the description
-- of the total quotient ring as the product of the localizations at the minimal primes. The
-- idempotents in that product split `R` as a finite product of the quotients by its minimal
-- primes. For the domain factors, the chapter's owner predicate for "normal domain" is the
-- canonical `IsIntegrallyClosed`, so the finite-product clause is stated directly with that API.
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
