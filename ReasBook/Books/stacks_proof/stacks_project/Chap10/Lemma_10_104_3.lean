import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_1
import StacksProject_2024.Chap10.Lemma_10_103_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- 
Domain-style sampling for the prime-chain statement:
- primary domain: Cohen-Macaulay modules over Noetherian local rings, specialized to the
  self-module `R`;
- sampled owner declarations:
  `Module.CohenMacaulay`,
  `ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay`,
  `Module.support_of_algebra`,
  `Module.supportDim_self_eq_ringKrullDim`;
- best owner abstraction: `Module.CohenMacaulay R R`;
- primitive data: the owner hypothesis `hCM : Module.CohenMacaulay R R`;
- derived API: full support of the self-module and the maximal-chain length theorem for a
  Cohen-Macaulay module with full support.

Source/core/bridge triage:
* source-facing: this lemma is the textbook self-module specialization for Cohen-Macaulay local
  rings;
* core/canonical: `ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay`;
* bridge/view: the canonical self-support fact `Module.support R R = Set.univ`.
-/
-- Proof sketch: this is the self-module specialization of Lemma `10.103.9`. The hypothesis `hCM`
-- is the self-module Cohen-Macaulay owner `Module.CohenMacaulay R R`; the support of the
-- self-module is all of `Spec R`, so the general maximal-chain statement applies directly.
/-- Lemma 10.104.3: if `R` is a Noetherian local Cohen-Macaulay ring, then every maximal chain of
prime ideals of `R`, encoded as an `LTSeries` with maximal range, has length `ringKrullDim R`. -/
@[stacks 00N9]
theorem length_maximal_prime_chain_eq_of_cohenMacaulayRing
    (hCM : Module.CohenMacaulay R R) (p : LTSeries (PrimeSpectrum R))
    (hp : IsMaxChain (· ≤ ·) (Set.range p)) :
    p.length = ringKrullDim R := by
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  have hsupp : Module.support R R = Set.univ := by
    simpa [hker, PrimeSpectrum.zeroLocus_bot] using
      (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
        Module.support_of_algebra)
  simpa using
    (ringKrullDim_eq_length_of_maximal_prime_chain_of_full_support_cohenMacaulay
      hCM hsupp p hp).symm

end
