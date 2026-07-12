import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain triage:
* primary domain: finite ring maps and the induced map on prime spectra;
* source-facing layer: a finite ring map `f : R →+* S` has finite fibers on `Spec`;
* core/canonical owner: `Algebra.QuasiFinite R S`, with finite-fiber theorem
  `Algebra.QuasiFinite.finite_comap_preimage_singleton`;
* bridge/view: `RingHom.QuasiFinite.of_finite` turns the finite map into the owner hypothesis.

Primitive data vs. derived API:
* primitive input: a ring hom `f : R →+* S` together with `f.Finite`;
* derived conclusion: for each `p : Spec R`, the fiber `(PrimeSpectrum.comap f)⁻¹({p})` is finite.
-/

/-- Lemma 10.36.21: a finite ring map has finite fibers on prime spectra. -/
@[stacks 05DR]
theorem finite_comap_preimage_singleton_of_finite (f : R →+* S) (hf : f.Finite)
    (p : PrimeSpectrum R) : (PrimeSpectrum.comap f ⁻¹' {p}).Finite := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.QuasiFinite R S := RingHom.QuasiFinite.of_finite hf
  simpa using Algebra.QuasiFinite.finite_comap_preimage_singleton p

end
