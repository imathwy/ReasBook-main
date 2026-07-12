import Mathlib
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped RatFunc TensorProduct
open Algebra.TensorProduct

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

attribute [local instance] Polynomial.algebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.47.10: irreducibility of `Spec R` is equivalent to the existence of a
unique minimal prime ideal of `R`. -/
theorem irreducibleSpace_primeSpectrum_iff_existsUnique_minimalPrime
    {R : Type u} [CommRing R] :
    IrreducibleSpace (PrimeSpectrum R) ↔ ∃! p : Ideal R, p ∈ minimalPrimes R := by
  constructor
  · intro hR
    -- Proof comment: in an irreducible prime spectrum, the nilradical is prime, so it is the
    -- unique minimal prime.
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR
    letI : (nilradical R).IsPrime := hR
    have hminimal : minimalPrimes R = {nilradical R} := by
      simpa [minimalPrimes, nilradical] using
        (show (nilradical R).minimalPrimes = {nilradical R} from
          Ideal.minimalPrimes_eq_subsingleton_self)
    refine ⟨nilradical R, ?_, ?_⟩
    · rw [hminimal]
      simp
    · intro q hq
      rw [hminimal] at hq
      simpa using hq
  · rintro ⟨p, hp, hp_unique⟩
    -- Proof comment: a unique minimal prime forces the nilradical to equal that prime ideal.
    have hminimal : minimalPrimes R = {p} := by
      ext q
      constructor
      · intro hq
        simpa using hp_unique q hq
      · rintro rfl
        exact hp
    have hsInf : sInf (minimalPrimes R) = nilradical R := by
      rw [minimalPrimes, nilradical]
      exact Ideal.sInf_minimalPrimes
    have hnil : nilradical R = p := by
      rw [← hsInf, hminimal]
      simp
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
    simpa [hnil] using Ideal.minimalPrimes_isPrime hp

/-- Helper for Lemma 10.47.10: irreducibility of prime spectra descends along injective ring
homomorphisms. -/
theorem irreducibleSpace_primeSpectrum_of_injective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) :
    IrreducibleSpace (PrimeSpectrum S) → IrreducibleSpace (PrimeSpectrum R) := by
  intro hS
  -- Proof comment: compare nilradicals through the injective map and pull primality back.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hS ⊢
  letI : (nilradical S).IsPrime := hS
  have hcomap : Ideal.comap f (nilradical S) = nilradical R := by
    ext x
    simp [Ideal.mem_comap, mem_nilradical, IsNilpotent.map_iff hf]
  simpa [hcomap] using Ideal.comap_isPrime f (nilradical S)

/-- Helper for Lemma 10.47.10: a nontrivial localization of a ring with irreducible prime
spectrum again has irreducible prime spectrum. -/
theorem irreducibleSpace_primeSpectrum_of_isLocalization
    {R A : Type u} [CommRing R] [CommRing A] (M : Submonoid R)
    [Algebra R A] [IsLocalization M A] [Nontrivial A]
    (hR : IrreducibleSpace (PrimeSpectrum R)) :
    IrreducibleSpace (PrimeSpectrum A) := by
  let eAlg : A ≃ₐ[R] Localization M := IsLocalization.algEquiv M A (Localization M)
  letI : Nontrivial (Localization M) := eAlg.injective.nontrivial
  let eSpec : PrimeSpectrum A ≃ₜ PrimeSpectrum (Localization M) :=
    PrimeSpectrum.homeomorphOfRingEquiv eAlg.toRingEquiv
  let f : PrimeSpectrum (Localization M) → PrimeSpectrum R :=
    PrimeSpectrum.comap (algebraMap R (Localization M))
  have hdense : DenseRange f := by
    -- Proof comment: the unique minimal prime of an irreducible spectrum survives localization,
    -- because any localized denominator inside the nilradical would force the localization to be
    -- trivial.
    rw [PrimeSpectrum.denseRange_comap_iff_minimalPrimes]
    intro I hI
    letI : (nilradical R).IsPrime := by
      rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR
      exact hR
    have hminimal : minimalPrimes R = {nilradical R} := by
      simpa [minimalPrimes, nilradical] using
        (show (nilradical R).minimalPrimes = {nilradical R} from
          Ideal.minimalPrimes_eq_subsingleton_self)
    have hIeq : I = nilradical R := by
      rw [hminimal] at hI
      simpa using hI
    let p : PrimeSpectrum R := ⟨I, Ideal.minimalPrimes_isPrime hI⟩
    have hdisj : Disjoint (M : Set R) p.asIdeal := by
      change Disjoint (M : Set R) I
      rw [hIeq]
      refine Set.disjoint_left.2 ?_
      intro x hxM hxnil
      rcases mem_nilradical.mp hxnil with ⟨n, hn⟩
      have hxunit : IsUnit (algebraMap R (Localization M) x) :=
        IsLocalization.map_units (Localization M) ⟨x, hxM⟩
      have hxpowzero : (algebraMap R (Localization M) x) ^ n = 0 := by
        simpa [map_pow] using congrArg (algebraMap R (Localization M)) hn
      rcases hxunit with ⟨u, hu⟩
      have honezero : (1 : Localization M) = 0 := by
        calc
          (1 : Localization M) = ↑(((u⁻¹ : Units (Localization M)) ^ n) * u ^ n) := by
            simp
          _ = ↑(u⁻¹ ^ n) * ↑u ^ n := by
            rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
          _ = ↑(u⁻¹ ^ n) * (algebraMap R (Localization M) x) ^ n := by
            rw [hu]
          _ = 0 := by rw [hxpowzero, mul_zero]
      exact one_ne_zero honezero
    rw [PrimeSpectrum.localization_comap_range (Localization M) M]
    exact hdisj
  have hRange : IsIrreducible (Set.range f) := by
    -- Proof comment: a dense subset of an irreducible space is irreducible after identifying its
    -- closure with the whole space.
    rw [← isIrreducible_iff_closure, hdense.closure_range]
    simpa using (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum R))
  let eRange : PrimeSpectrum (Localization M) ≃ₜ Set.range f :=
    (Homeomorph.Set.univ _).symm.trans <|
      (Homeomorph.setCongr (by ext x; simp [f])).trans <|
        (PrimeSpectrum.localization_comap_isEmbedding (Localization M) M).homeomorphOfSubsetRange
          (by intro x hx; exact hx)
  have hLoc : IrreducibleSpace (PrimeSpectrum (Localization M)) :=
    (eRange.irreducibleSpace_iff).2 (Subtype.irreducibleSpace hRange)
  exact (eSpec.irreducibleSpace_iff).2 hLoc

/-- Helper for Lemma 10.47.10: localizing away from an element preserves irreducibility of prime
spectra as soon as the localized ring is nontrivial. -/
theorem irreducibleSpace_primeSpectrum_localizationAway
    {R : Type u} [CommRing R] (r : R) [Nontrivial (Localization.Away r)]
    (hR : IrreducibleSpace (PrimeSpectrum R)) :
    IrreducibleSpace (PrimeSpectrum (Localization.Away r)) := by
  -- Proof comment: `Localization.Away r` is a special case of a nontrivial localization, so the
  -- general localization lemma applies directly.
  exact irreducibleSpace_primeSpectrum_of_isLocalization (Submonoid.powers r) hR
end

end Algebra
