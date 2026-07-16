import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

/- Domain-style sampling:
* primary domain: Cohen-Macaulay modules, support dimension, and associated primes over
  Noetherian local rings;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes`,
  `minimal_support_iff_minimal_associatedPrimes`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* primitive data: the ambient local Noetherian ring, the module structure on `M`, and the owner
  instance `[Module.CohenMacaulay R M]`;
* derived API: the equality `Module.supportDim R M = .some (moduleDepth R M)` and the inherited
  finiteness instance.

Source/core/bridge triage:
* `source-facing`: the two consequences for associated primes of a Cohen-Macaulay module;
* `core/canonical`: `Module.CohenMacaulay`, `Module.support`, `Module.supportDim`,
  `associatedPrimes`, and `ringKrullDim`;
* `bridge/view`: passing between support-minimal prime points and minimal associated ideals.
-/

-- Proof sketch: apply Lemma `10.72.9` to get
-- `.some (moduleDepth R M) ≤ ringKrullDim (R ⧸ 𝔭.asIdeal)`, use the Cohen-Macaulay identity
-- `Module.CohenMacaulay.supportDim_eq_moduleDepth`, and
-- combine this with the general inequality `ringKrullDim (R ⧸ 𝔭.asIdeal) ≤ Module.supportDim R M`
-- coming from `𝔭 ∈ Module.support R M`. Equality of dimensions forces `𝔭` to be minimal in the
-- support.
/-- Lemma 10.103.7: if `M` is a Cohen-Macaulay module over a Noetherian local ring and `𝔭` is an
associated prime of `M`, then the Krull dimension of `R / 𝔭` equals the dimension of the support
of `M`, and `𝔭` is minimal in `Module.support R M`. -/
theorem ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay
    (𝔭 : PrimeSpectrum R) (h𝔭 : 𝔭.asIdeal ∈ associatedPrimes R M) :
    ringKrullDim (R ⧸ 𝔭.asIdeal) = Module.supportDim R M ∧
      Minimal (· ∈ Module.support R M) 𝔭 := sorry

-- Proof sketch: apply the minimal-support conclusion of
-- `ringKrullDim_quotient_and_minimal_support_of_mem_associatedPrimes_of_cohenMacaulay` to the
-- prime point corresponding to `p`, then use Proposition `10.63.6` to pass from minimality in the
-- support to minimality among associated primes.
/-- If `M` is Cohen-Macaulay, then every associated prime of `M` is minimal among the associated
primes; equivalently, `M` has no embedded associated primes. -/
theorem minimal_mem_associatedPrimes_of_mem_associatedPrimes_of_cohenMacaulay
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    Minimal (· ∈ associatedPrimes R M) p := sorry

end
