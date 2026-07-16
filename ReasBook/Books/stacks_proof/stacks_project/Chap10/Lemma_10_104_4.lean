import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_103_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
* primary domain: Krull-dimension formulas for Cohen-Macaulay local rings, viewed as the
  self-module specialization of the general Cohen-Macaulay module theorem;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay`,
  `Module.support_of_algebra`,
  `CohenMacaulayRing`;
* best owner abstraction: `Module.CohenMacaulay R R`;
* primitive data: the ambient local Noetherian ring, the self-module owner hypothesis
  `hCM : Module.CohenMacaulay R R`, and the prime ideal `p`;
* derived API: the full-support fact for the self-module, obtained canonically from
  `Module.support_of_algebra`.

Source/core/bridge triage:
* source-facing: the textbook dimension formula for a Cohen-Macaulay local ring;
* core/canonical: `Module.CohenMacaulay R R` together with the general module theorem
  `ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay`;
* bridge/view: the self-support identification `Module.support R R = Set.univ`.

The later class `CohenMacaulayRing` is not the owner abstraction for this local statement: it is a
global ring property introduced later in the chapter. This file should stay a thin source-facing
self-module specialization of the earlier owner theorem, not a second ring-level owner. -/

-- Proof sketch: specialize Lemma `10.103.10` to the self-module `M = R`. The hypothesis
-- `hCM : Module.CohenMacaulay R R` is exactly the Cohen-Macaulay condition for this module, and
-- the self-module `R` has full support, so the general dimension formula yields the claimed
-- equality.
/-- Lemma 10.104.4: if `R` is a Noetherian local Cohen-Macaulay ring, then for every prime ideal
`p` of `R` the dimension of `R` is the sum of the dimensions of the localization `Rₚ` and the
quotient `R / p`. -/
@[stacks 00NA]
theorem ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_cohenMacaulayRing
    (hCM : Module.CohenMacaulay R R) (p : Ideal R) [p.IsPrime] :
    ringKrullDim R = ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) := by
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  have hsupp : Module.support R R = Set.univ := by
    simpa [hker, PrimeSpectrum.zeroLocus_bot] using
      (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
        Module.support_of_algebra)
  exact ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay
    hCM hsupp p

end
