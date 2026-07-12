import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum
open Topology

section

variable {R : Type u} [CommRing R]

-- Proof sketch: this is the quotient specialization of the owner theorem
-- `PrimeSpectrum.isConstructible_comap_image`. The only primitive input is `hI : I.FG`; the
-- finite-presentation structure on `R ⧸ I` is derived canonically from
-- `Algebra.FinitePresentation.quotient hI`.
/-- Lemma 10.29.6: if `I` is a finitely generated ideal of a commutative ring `R`, then the image
of a constructible subset of `Spec (R ⧸ I)` under the quotient map to `Spec(R)` is constructible
in `Spec(R)`. -/
@[stacks 00FA]
theorem isConstructible_image_comap_quotient
    (I : Ideal R) (hI : I.FG) {s : Set (PrimeSpectrum (R ⧸ I))} (hs : IsConstructible s) :
    IsConstructible (comap (Ideal.Quotient.mk I) '' s) := by
  letI : Algebra.FinitePresentation R (R ⧸ I) := Algebra.FinitePresentation.quotient hI
  simpa using
    isConstructible_comap_image
      (RingHom.finitePresentation_algebraMap.mpr inferInstance) hs

end
