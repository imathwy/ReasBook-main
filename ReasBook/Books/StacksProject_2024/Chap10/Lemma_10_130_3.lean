import Mathlib
import StacksProject_2024.Chap10.Lemma_10_130_2
import StacksProject_2024.Chap10.Lemma_10_72_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum IsLocalRing Module.associatedPrimes
open scoped ENat

section

variable {S : Type v} [CommRing S]

/- Domain-style sampling:
- primary domain: the Cohen-Macaulay locus on `Spec(S)`, with the core local owner
  `Module.CohenMacaulay` on localized self-modules;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.cohenMacaulayLocus`,
  `PrimeSpectrum.mem_cohenMacaulayLocus`,
  `Module.CohenMacaulay`,
  `Ring.KrullDimLE.of_isLocalization`;
- best owner abstraction: the source-facing owner remains the locus
  `PrimeSpectrum.cohenMacaulayLocus S`, while the reusable core input is the canonical
  `Module.CohenMacaulay` statement for `Localization.AtPrime q.1`;
- primitive data: a Noetherian ring, a minimal prime, and the canonical localization at that
  prime;
- derived API: Cohen-Macaulayness of that localization, then membership in the Cohen-Macaulay
  locus.

Source/core/bridge triage:
- `source-facing`: density of `PrimeSpectrum.cohenMacaulayLocus S`;
- `core/canonical`: `Module.CohenMacaulay R R` for a zero-dimensional Noetherian local ring, and
  its specialization to `Localization.AtPrime q.1` for `q : minimalPrimes S`;
- `bridge/view`: passage from a minimal prime to a point of `PrimeSpectrum S` lying in the locus.
-/

/-- A Noetherian local ring of Krull dimension at most zero is Cohen-Macaulay as a module over
itself. -/
theorem self_cohenMacaulay_of_krullDimLE_zero
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 0 R]
    [Nontrivial R] :
    Module.CohenMacaulay R R := by
  refine Module.CohenMacaulay.mk ?_
  have hann : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  have hassoc : maximalIdeal R ∈ associatedPrimes R R := by
    have hmin' : maximalIdeal R ∈ (⊥ : Ideal R).minimalPrimes :=
      Ideal.mem_minimalPrimes_of_krullDimLE_zero (maximalIdeal R)
    have hmin : maximalIdeal R ∈ (Module.annihilator R R).minimalPrimes := by
      simpa [hann] using hmin'
    exact minimalPrimes_annihilator_subset_associatedPrimes R R hmin
  have hdepth_le : moduleDepth R R ≤ 0 := by
    have hle : WithBot.some (moduleDepth R R : ℕ∞) ≤ ringKrullDim (R ⧸ maximalIdeal R) :=
      moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (maximalIdeal R) hassoc
    have hdim : ringKrullDim (R ⧸ maximalIdeal R) = 0 := by
      letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
      exact ringKrullDim_eq_zero_of_field (R ⧸ maximalIdeal R)
    rw [hdim] at hle
    simpa [WithBot.some_eq_coe] using hle
  have hdepth : moduleDepth R R = 0 := le_antisymm hdepth_le bot_le
  have hdim : ringKrullDim R = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  simp [Module.supportDim_self_eq_ringKrullDim, hdim, hdepth]

local instance (q : minimalPrimes S) : q.1.IsPrime :=
  Ideal.minimalPrimes_isPrime q.2

/-- If `q` is a minimal prime of a Noetherian ring `S`, then the localization `S_q` is
Cohen-Macaulay. -/
theorem cohenMacaulay_localizationAtPrime_self_of_minimalPrime
    [IsNoetherianRing S] (q : minimalPrimes S) :
    Module.CohenMacaulay (Localization.AtPrime q.1) (Localization.AtPrime q.1) := by
  letI : IsNoetherianRing (Localization.AtPrime q.1) :=
    IsLocalization.isNoetherianRing q.1.primeCompl (Localization.AtPrime q.1) inferInstance
  letI : Ring.KrullDimLE 0 (Localization.AtPrime q.1) :=
    Ring.KrullDimLE.of_isLocalization q.1 q.2 (Localization.AtPrime q.1)
  exact self_cohenMacaulay_of_krullDimLE_zero (Localization.AtPrime q.1)

/-- Every minimal prime of a Noetherian ring lies in its Cohen-Macaulay locus. -/
theorem mem_cohenMacaulayLocus_of_mem_minimalPrimes
    [IsNoetherianRing S]
    (q : PrimeSpectrum S) (hq : q.asIdeal ∈ minimalPrimes S) :
    q ∈ PrimeSpectrum.cohenMacaulayLocus S := by
  let qmin : minimalPrimes S := ⟨q.asIdeal, hq⟩
  simpa using cohenMacaulay_localizationAtPrime_self_of_minimalPrime qmin

-- Proof sketch: Lemma `10.130.2` gives that the Cohen--Macaulay locus is open. To prove density,
-- it is enough to show that every minimal prime of `S` lies in this locus. For a minimal prime
-- `q`, the local ring `Localization.AtPrime q.asIdeal` has Krull dimension zero, hence it is
-- Cohen--Macaulay.
/-- Lemma 10.130.3, owner-level form: for a Noetherian ring `S`, the set of primes `q` such that
the local ring `S_q` is Cohen-Macaulay is dense in `Spec(S)`. The finite type over a field
hypothesis from the source is used only to obtain `IsNoetherianRing S`, so the main public theorem
lives at the Noetherian-ring owner level. -/
theorem dense_cohenMacaulayLocus [IsNoetherianRing S] :
    Dense (PrimeSpectrum.cohenMacaulayLocus S) := by
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff]
  intro U hU hUne
  rcases hU with ⟨f, rfl⟩
  rcases hUne with ⟨x, hx⟩
  obtain ⟨q, hq, hqx⟩ :=
    Ideal.exists_minimalPrimes_le (show (⊥ : Ideal S) ≤ x.asIdeal from bot_le)
  let q' : PrimeSpectrum S := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
  have hq' : q'.asIdeal ∈ minimalPrimes S := by
    simpa [minimalPrimes] using hq
  refine ⟨q', ?_, mem_cohenMacaulayLocus_of_mem_minimalPrimes q' hq'⟩
  refine (PrimeSpectrum.mem_basicOpen f q').2 fun hfq ↦ ?_
  exact (PrimeSpectrum.mem_basicOpen f x).1 hx (hqx hfq)

/-- Lemma 10.130.3: for a finite type algebra `S` over a field `k`, the set of primes `q` such
that the local ring `S_q` is Cohen-Macaulay is dense in `Spec(S)`, so together with Lemma
`10.130.2` it is a dense open subset. -/
theorem dense_cohenMacaulayLocus_of_finiteType
    (k : Type u) [Field k] [Algebra k S] [Algebra.FiniteType k S] :
    Dense (PrimeSpectrum.cohenMacaulayLocus S) := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  exact dense_cohenMacaulayLocus

end
