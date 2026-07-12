import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open PrimeSpectrum

universe u

variable {R : Type u} [CommRing R]

/- Layering for this item:
* source-facing: the localization map induces a homeomorphism from `Spec(Localization M)` onto the
  subspace of `Spec(R)` cut out by primes disjoint from `M`.
* core/canonical owners: `localization_comap_isEmbedding` and `localization_comap_range`.
* bridge/view: turn the owner embedding into a homeomorphism onto the identified subtype.
-/

/-- Lemma 10.17.5: the map on prime spectra induced by the localization map
`R → Localization M` is a homeomorphism from `Spec(Localization M)` onto the subspace of
`Spec(R)` consisting of the primes disjoint from `M`. -/
@[stacks 00E3]
def primeSpectrum_localization_homeomorph (M : Submonoid R) :
    PrimeSpectrum (Localization M) ≃ₜ { p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal } :=
  (localization_comap_isEmbedding (Localization M) M).toHomeomorph.trans <|
    Homeomorph.setCongr (localization_comap_range (Localization M) M)

/-- The localization homeomorphism is induced by the comap along `R → Localization M`. -/
-- Proof sketch: the owner embedding `PrimeSpectrum.comap (algebraMap R (Localization M))`
-- underlies the homeomorphism, so the forward map is definitionally the canonical comap.
@[simp] theorem primeSpectrum_localization_homeomorph_apply (M : Submonoid R)
    (p : PrimeSpectrum (Localization M)) :
    ↑(primeSpectrum_localization_homeomorph M p) =
      comap (algebraMap R (Localization M)) p := by
  rfl

/-- The inverse of the localization homeomorphism sends a prime disjoint from `M`
to its extension to `Localization M`. -/
-- Proof sketch: the prime of the localization defined by extension maps back to `p` by the
-- canonical localization formula, so it is the inverse image of `p` under the homeomorphism.
@[simp] theorem primeSpectrum_localization_homeomorph_symm_apply (M : Submonoid R)
    (p : { p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal }) :
    (primeSpectrum_localization_homeomorph M).symm p =
      ⟨p.1.asIdeal.map (algebraMap R (Localization M)),
        IsLocalization.isPrime_of_isPrime_disjoint M (Localization M) _ p.1.2 p.2⟩ := by
  let q : PrimeSpectrum (Localization M) :=
    ⟨p.1.asIdeal.map (algebraMap R (Localization M)),
      IsLocalization.isPrime_of_isPrime_disjoint M (Localization M) _ p.1.2 p.2⟩
  -- Track the extended prime through the forward homeomorphism and identify its contraction.
  have hq : primeSpectrum_localization_homeomorph M q = p := by
    apply Subtype.ext
    rw [primeSpectrum_localization_homeomorph_apply]
    ext1
    simpa [q] using
      (IsLocalization.comap_map_of_isPrime_disjoint M (Localization M) p.1.2 p.2 : _)
  -- The inverse point is uniquely characterized by mapping forward to `p`.
  exact (primeSpectrum_localization_homeomorph M).symm_apply_eq.mpr hq.symm

/-- The inverse of the localization homeomorphism is represented by extending the prime ideal
along the localization map. -/
-- Proof sketch: apply `congrArg PrimeSpectrum.asIdeal` to the explicit inverse-point formula for
-- `primeSpectrum_localization_homeomorph`, and simplify the resulting equality of prime spectra.
theorem primeSpectrum_localization_homeomorph_symm_apply_asIdeal (M : Submonoid R)
    (p : { p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal }) :
    ((primeSpectrum_localization_homeomorph M).symm p).asIdeal =
      p.1.asIdeal.map (algebraMap R (Localization M)) := by
  -- Project the explicit inverse-point formula to the underlying prime ideal.
  simpa using congrArg PrimeSpectrum.asIdeal
    (primeSpectrum_localization_homeomorph_symm_apply M p)
