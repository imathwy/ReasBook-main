import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Ideal

open PrimeSpectrum
open scoped PrimeSpectrum

variable {R : Type u} [CommRing R]

/- Layering for this item:
* source-facing: the quotient map induces a homeomorphism `Spec (R ⧸ I) ≃ₜ V(I)`.
* core/canonical owner: `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`.
* bridge/view: upgrade the owner-side closed embedding of the quotient-spectrum comap to a
  homeomorphism onto its identified range `V(I)`. -/

/-- Lemma 10.17.7: the quotient map `R → R ⧸ I` induces a homeomorphism
from `Spec (R ⧸ I)` onto the closed subset `V(I)` of `Spec R`. -/
@[stacks 00E5]
def primeSpectrum_quotient_homeomorph_zeroLocus (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃ₜ V((I : Set R)) :=
  (PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).toIsEmbedding.toHomeomorph
    |>.trans (Homeomorph.setCongr <| by
      simpa [Ideal.mk_ker] using
        (range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective))

@[simp]
theorem primeSpectrum_quotient_homeomorph_zeroLocus_apply
    (I : Ideal R) (x : PrimeSpectrum (R ⧸ I)) :
    (primeSpectrum_quotient_homeomorph_zeroLocus I x).1 =
      PrimeSpectrum.comap (Ideal.Quotient.mk I) x :=
  rfl

/-- The inverse homeomorphism sends a prime ideal of `R` containing `I`
to its image in the quotient ring `R ⧸ I`. -/
theorem primeSpectrum_quotient_homeomorph_zeroLocus_symm_asIdeal
    (I : Ideal R) (x : V((I : Set R))) :
    ((primeSpectrum_quotient_homeomorph_zeroLocus I).symm x).asIdeal =
      x.1.asIdeal.map (Ideal.Quotient.mk I) :=
  by
    let q : PrimeSpectrum (R ⧸ I) := I.primeSpectrumQuotientOrderIsoZeroLocus.symm x
    have hq : primeSpectrum_quotient_homeomorph_zeroLocus I q = x := by
      apply Subtype.ext
      exact congrArg Subtype.val (I.primeSpectrumQuotientOrderIsoZeroLocus.apply_symm_apply x)
    have hsymm : (primeSpectrum_quotient_homeomorph_zeroLocus I).symm x = q :=
      (primeSpectrum_quotient_homeomorph_zeroLocus I).symm_apply_eq.mpr hq.symm
    simpa [q] using congrArg PrimeSpectrum.asIdeal hsymm

end Ideal
