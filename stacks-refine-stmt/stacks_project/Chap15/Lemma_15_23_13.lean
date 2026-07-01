import Mathlib
import stacks_project.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open LocalizedModule (AtPrime map)
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Domain triage:
* primary domain: local-to-global isomorphism criteria for finite module maps over Noetherian
  rings, using localized depth and associated primes;
* sampled owner declarations:
  `moduleDepth`,
  `injective_of_injective_localizedMap_at_associatedPrimes`,
  `exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes`,
  `subsingleton_iff_associatedPrimes_eq_empty`;
* best owner abstraction: the local-depth bridge `moduleDepth` together with the owner set
  `associatedPrimes R _`;
* primitive data: the linear map `φ : M →ₗ[R] N` and the primewise disjunction from the source;
* derived API: injectivity via associated-prime localizations and vanishing of the cokernel via
  emptiness of associated primes.

Layering:
* this numbered item is `source-facing`: it is the textbook criterion for when a finite module map
  is an isomorphism from primewise local data;
* the `core/canonical` owners reused here are `moduleDepth` and `associatedPrimes`;
* no extra `bridge/view` wrapper should be introduced in this file.
-/

-- Proof sketch: first apply Lemma `15.23.12` to the kernel to obtain injectivity of `φ`, since
-- bijectivity of the localized map implies injectivity and the second branch excludes associated
-- primes of the codomain. Then replace `N` by a finite submodule containing the image of `M`,
-- form the cokernel `Q`, and analyze its localizations: in the first branch `Qₚ = 0`, while in
-- the second branch Lemmas `10.63.18` and `10.72.6` give `moduleDepth` at least `1` for `Qₚ`.
-- Hence `Q` has no associated primes, so Lemma `10.63.7` forces `Q = 0`, proving surjectivity.
/-- Lemma 15.23.13: let `R` be a Noetherian ring and let `φ : M → N` be a map of `R`-modules with
`M` finite. If for every prime `p` of `R` either the localized map `Mₚ → Nₚ` is an isomorphism,
or the localized module `Mₚ` has depth at least `2` and `p` is not an associated prime of `N`,
then `φ` is an isomorphism. -/
theorem bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_and_not_mem_associatedPrimes
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective (map p.asIdeal.primeCompl φ) ∨
        ((2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) ∧
          p.asIdeal ∉ associatedPrimes R N)) :
    Function.Bijective φ := sorry

end
