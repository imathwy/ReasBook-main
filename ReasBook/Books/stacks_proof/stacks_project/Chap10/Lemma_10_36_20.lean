import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]

open PrimeSpectrum Ideal

/- Domain triage:
* primary domain: integral extensions and the induced map on prime spectra;
* core/canonical owner: `Ideal.comap_lt_comap_of_integral_mem_sdiff` from the going-up API;
* layer split: the ideal-level strict-comap theorem is the owner result, while the theorem below is
  the source-facing bridge reformulating it as incomparability in `PrimeSpectrum`;
* primitive data vs. derived API: the primitive hypotheses are the integral `R`-algebra structure
  on `S`, distinct primes `q ≠ q'`, and equality of their images under `PrimeSpectrum.comap`. The
  specialization-order incomparability is derived from the owner theorem and should not be stored
  as separate local data.
-/

/-- Lemma 10.36.20: distinct points of `Spec(S)` with the same image in `Spec(R)` are
incomparable in the specialization order, equivalently their prime ideals are incomparable by
inclusion. -/
@[stacks 00GT]
theorem primes_over_same_prime_are_incomparable (q q' : PrimeSpectrum S) (hqq' : q ≠ q')
    (himage : comap (algebraMap R S) q = comap (algebraMap R S) q') :
    ¬ q ≤ q' ∧ ¬ q' ≤ q := by
  have hnot_le :
      ∀ ⦃a b : PrimeSpectrum S⦄,
        a ≠ b →
        comap (algebraMap R S) a = comap (algebraMap R S) b →
        ¬ a ≤ b := by
    intro a b hab hab_comap hab_le
    have hab' : a.asIdeal < b.asIdeal := by
      refine lt_of_le_of_ne hab_le ?_
      intro h
      exact hab (PrimeSpectrum.ext h)
    obtain ⟨hab_le', x, hxb, hxa⟩ := SetLike.lt_iff_le_and_exists.mp hab'
    have hcomap :
        Ideal.comap (algebraMap R S) a.asIdeal = Ideal.comap (algebraMap R S) b.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hab_comap
    exact (comap_lt_comap_of_integral_mem_sdiff hab_le' ⟨hxb, hxa⟩
      (Algebra.IsIntegral.isIntegral x)).ne hcomap
  exact ⟨hnot_le hqq' himage, hnot_le hqq'.symm himage.symm⟩

end
