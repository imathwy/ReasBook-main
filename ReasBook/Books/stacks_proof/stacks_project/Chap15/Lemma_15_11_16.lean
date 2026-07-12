import Mathlib
import StacksProject_2024.Chap10.IdempotentMap
import StacksProject_2024.Chap10.Lemma_10_17_7
import StacksProject_2024.Chap10.Lemma_10_21_4
import StacksProject_2024.Chap15.Lemma_15_11_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open PrimeSpectrum
open scoped PrimeSpectrum

variable {A : Type u} [CommRing A]
variable (I : Ideal A) [HenselianRing A I] (p : PrimeSpectrum A)

/- Domain-style sampling:
- primary domain: commutative algebra of henselian pairs, quotient spectra, and connectedness of
  closed subsets of `Spec(A)`;
- sampled owner declarations:
  `HenselianRing`,
  `ideal_map_henselianRing_of_isIntegral`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`,
  `primeSpectrum_connectedSpace_iff_idempotents_trivial`;
- best owner abstraction: the source-facing theorem remains the connectedness statement for the
  closed subset `V(p + I)`, but its canonical proof/data flow is owned by the quotient-spectrum
  homeomorphism onto a zero locus, the third-isomorphism equivalence
  `DoubleQuot.quotQuotEquivQuotSup`, and the Chapter 10 connectedness criterion for spectra;
- primitive data: the prime `p`, the ideal `I`, the quotient ring `A ⧸ p.asIdeal`, and the mapped
  ideal `Ideal.map (Ideal.Quotient.mk p.asIdeal) I`;
- derived API: henselianity of the mapped pair, the double-quotient identification with
  `A ⧸ (p.asIdeal ⊔ I)`, and the idempotent-triviality criterion for connected prime spectra.

Source/core/bridge triage:
- `source-facing`: connectedness of the closed subset `V(p + I)` in `Spec(A)`;
- `core/canonical`: `HenselianRing`, `DoubleQuot.quotQuotEquivQuotSup`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`, and
  `primeSpectrum_connectedSpace_iff_idempotents_trivial`;
- `bridge/view`: passing from `V(p + I)` to the spectrum of the quotient
  `(A ⧸ p.asIdeal) ⧸ Ideal.map (Ideal.Quotient.mk p.asIdeal) I`.
-/

-- Proof sketch: by Lemma `15.11.8`, the quotient pair
-- `(A ⧸ p.asIdeal, Ideal.map (Ideal.Quotient.mk p.asIdeal) I)` is henselian. Thus it is enough to
-- prove connectedness of `Spec ((A ⧸ p.asIdeal) ⧸ Ideal.map (Ideal.Quotient.mk p.asIdeal) I)`.
-- Since `A ⧸ p.asIdeal` is a domain, any disconnection would give a nontrivial idempotent in this
-- quotient by Lemma `10.21.4`; Lemma `15.11.6` then lifts that idempotent to a nontrivial
-- idempotent of the domain `A ⧸ p.asIdeal`, a contradiction.
/-- Helper for Lemma 15.11.16: if reduction modulo `J` is bijective on idempotents, then every
idempotent in the quotient of a domain is trivial. -/
private lemma quotient_idempotents_trivial_of_domain_of_idempotent_bijective
    {B : Type u} [CommRing B] [IsDomain B] (J : Ideal B)
    (hbij : Function.Bijective (Ideal.Quotient.mk J).idempotentMap)
    (e : B ⧸ J) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  obtain ⟨x, hx⟩ := hbij.surjective ⟨e, he⟩
  have hx_val : (Ideal.Quotient.mk J) x.1 = e := by
    -- Proof comment: forget the idempotent subtype structure after lifting `e` to an
    -- idempotent `x` of the domain.
    simpa [RingHom.idempotentMap] using congrArg Subtype.val hx
  have hx_trivial : x.1 = 0 ∨ x.1 = 1 := by
    -- Proof comment: a domain has only the two trivial idempotents.
    have hmul : x.1 * (x.1 - 1) = 0 := by
      calc
        x.1 * (x.1 - 1) = x.1 * x.1 - x.1 := by ring
        _ = 0 := by exact sub_eq_zero.mpr x.2.eq
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hx0 | hx1
    · exact Or.inl hx0
    · exact Or.inr (sub_eq_zero.mp hx1)
  rcases hx_trivial with hx0 | hx1
  · left
    simpa [hx0] using hx_val.symm
  · right
    simpa [hx1] using hx_val.symm

/-- Helper for Lemma 15.11.16: if the quotient map is bijective on idempotents and the ideal lies
in the Jacobson radical, then the quotient spectrum of a domain is connected. -/
private lemma connectedSpace_primeSpectrum_quotient_of_domain_of_jacobson_and_idempotent_bijective
    {B : Type u} [CommRing B] [IsDomain B] (J : Ideal B)
    (hJjac : J ≤ Ring.jacobson B)
    (hbij : Function.Bijective (Ideal.Quotient.mk J).idempotentMap) :
    ConnectedSpace (PrimeSpectrum (B ⧸ J)) := by
  have hJ_ne_top : J ≠ ⊤ := by
    intro hJ_top
    have h_one : (1 : B) ∈ Ring.jacobson B := by
      exact hJjac <| by simpa [hJ_top]
    have h_one' : (1 : B) ∈ Ideal.jacobson (⊥ : Ideal B) := by
      simpa [Ideal.jacobson_bot] using h_one
    have hzero_unit : IsUnit (0 : B) := by
      -- Proof comment: if `1` lay in the Jacobson radical, testing against `-1` would force
      -- `0` to be a unit.
      simpa using (Ideal.mem_jacobson_bot.mp h_one' (-1 : B))
    exact hzero_unit.ne_zero rfl
  letI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ_ne_top
  refine (primeSpectrum_connectedSpace_iff_idempotents_trivial (R := B ⧸ J)).2 ?_
  intro e he
  -- Proof comment: triviality of quotient idempotents follows from lifting them back to the
  -- ambient domain `B`.
  exact quotient_idempotents_trivial_of_domain_of_idempotent_bijective J hbij e he

/-- Helper for Lemma 15.11.16: connectedness of the quotient spectrum transports to the
corresponding zero locus in `Spec(A)`. -/
private lemma connectedSpace_zeroLocus_of_connected_quotient
    (K : Ideal A) (hK : ConnectedSpace (PrimeSpectrum (A ⧸ K))) :
    ConnectedSpace (V((K : Set A))) := by
  let eSpec : PrimeSpectrum (A ⧸ K) ≃ₜ V((K : Set A)) :=
    Ideal.primeSpectrum_quotient_homeomorph_zeroLocus K
  letI : ConnectedSpace (PrimeSpectrum (A ⧸ K)) := hK
  exact eSpec.surjective.connectedSpace eSpec.continuous

/-- Lemma 15.11.16: for a henselian pair `(A, I)` and a prime ideal `p` of `A`, the closed subset
`V(p + I)` of `Spec(A)` is connected. -/
@[stacks 09Y6]
theorem connectedSpace_zeroLocus_prime_add_of_henselianRing :
    ConnectedSpace (V(((p.asIdeal + I : Ideal A) : Set A))) := by
  let B : Type u := A ⧸ p.asIdeal
  let J : Ideal B := Ideal.map (Ideal.Quotient.mk p.asIdeal) I
  letI : IsDomain B := Ideal.Quotient.isDomain p.asIdeal
  letI : Module.Finite A B := by
    dsimp [B]
    exact RingHom.Finite.of_surjective (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  letI : Algebra.IsIntegral A B := by
    infer_instance
  letI : HenselianRing B J := by
    -- Proof comment: Lemma `15.11.8` keeps henselianity after passing to the integral quotient
    -- `A ⧸ p`.
    simpa [B, J] using
      (ideal_map_henselianRing_of_isIntegral (A := A) (B := B) (I := I))
  have hconnBQ : ConnectedSpace (PrimeSpectrum (B ⧸ J)) :=
    connectedSpace_primeSpectrum_quotient_of_domain_of_jacobson_and_idempotent_bijective
      J J.le_ring_jacobson_of_henselianRing
      J.quotientMk_bijective_idempotentMap_of_henselianRing
  let eSpec :
      PrimeSpectrum (B ⧸ J) ≃ₜ PrimeSpectrum (A ⧸ (p.asIdeal + I : Ideal A)) :=
    PrimeSpectrum.homeomorphOfRingEquiv <| by
      simpa [B, J, Ideal.add_eq_sup] using DoubleQuot.quotQuotEquivQuotSup p.asIdeal I
  have hconnAquot : ConnectedSpace (PrimeSpectrum (A ⧸ (p.asIdeal + I : Ideal A))) := by
    letI : ConnectedSpace (PrimeSpectrum (B ⧸ J)) := hconnBQ
    exact eSpec.surjective.connectedSpace eSpec.continuous
  simpa using
    connectedSpace_zeroLocus_of_connected_quotient (A := A) (p.asIdeal + I) hconnAquot

end
