import StacksProject_2024.stacks_project.Chap10.«10_118_3_2»
import StacksProject_2024.stacks_project.Chap10.Lemma_10_17_6

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped PrimeSpectrum

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/- Domain triage:
* primary domain: generic-flatness loci on prime spectra under localization away from one element;
* source-facing owner: `goodLocus R S M` from `10_118_3_2`;
* core/canonical bridge: `primeSpectrum_localizationAway_homeomorph_D f` and its pointwise
  description via `PrimeSpectrum.comap`;
* bridge/view target of this file: transport `goodLocus` across the canonical identification
  `Spec(R_f) ≃ D(f)`, with the restriction to `D(f)` expressed canonically as a subtype preimage
  rather than a separate wrapper set. -/

/-- Lemma 10.118.5: pulling back `U(R → S, M)` along `Spec(R_f) → Spec(R)` gives the good locus of
the localized pair `(R_f → S_f, M_f)`. Equivalently, under the identification
`Spec(R_f) ≃ D(f)`, this is the equality `U(R_f → S_f, M_f) = D(f) ∩ U(R → S, M)`. -/
-- Proof sketch: membership in the localized good locus means there is `g ∈ R_f` such that
-- `(10.118.3.1)` holds after localizing once more at `g`. Write `g = a / f^n`, replace it by an
-- element of `R` giving the same doubly localized rings and modules, and use that the image of
-- `Spec(R_f) → Spec(R)` is `D(f)`.
theorem goodLocus_localizationAway_eq_preimage (f : R) :
    goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) =
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) ⁻¹'
      goodLocus R S M := sorry

/-- Under the canonical homeomorphism `Spec(R_f) ≃ D(f)`, the localized good locus is the
restriction of `U(R → S, M)` to the basic open `D(f)`. -/
-- Proof sketch: rewrite `goodLocus_localizationAway_eq_preimage` through
-- `primeSpectrum_localizationAway_homeomorph_D f`, using the explicit description of that
-- homeomorphism on points. Express the restriction to `D(f)` as the preimage of `goodLocus R S M`
-- under the subtype coercion `D(f) → Spec(R)`.
theorem goodLocus_localizationAway_eq_D_restrict (f : R) :
    Set.image (primeSpectrum_localizationAway_homeomorph_D f)
      (goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M)) =
    ((↑) : D(f) → PrimeSpectrum R) ⁻¹' goodLocus R S M := sorry

end GenericFlatness

end
