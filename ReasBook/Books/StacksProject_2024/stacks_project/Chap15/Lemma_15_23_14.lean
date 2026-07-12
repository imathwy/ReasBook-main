import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap15.Definition_15_22_1
import StacksProject_2024.Chap15.Lemma_15_23_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open LocalizedModule (AtPrime map)
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]

/- Domain-style sampling:
- primary domain: local-to-global isomorphism criteria for finite module maps over Noetherian
  domains, using primewise localized depth and torsion-freeness of the codomain;
- sampled owner declarations:
  `moduleDepth`,
  `associatedPrimes R _`,
  `Module.IsTorsionFree`,
  `Module.not_mem_associatedPrimes_of_ne_bot`,
  `bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_and_not_mem_associatedPrimes`;
- best owner abstraction:
  `moduleDepth` is the canonical local depth owner surface in this chapter, while
  `Module.IsTorsionFree` is the canonical owner for the codomain hypothesis, and the previous
  lemma is the source-facing ambient isomorphism criterion being specialized here;
- source/core/bridge triage:
  `source-facing`: this lemma is the textbook torsion-free specialization of the previous local
    isomorphism criterion;
  `core/canonical`: `moduleDepth`, `associatedPrimes`, `Module.IsTorsionFree`;
  `bridge/view`: the implication from torsion-freeness over a domain to the associated-prime
    exclusion needed by the previous lemma.

Primitive data are only the linear map `φ`, the finite source module, the torsion-free codomain
owner instance, and the primewise disjunction from the source. The local depth term is derived API
and should therefore use the chapter owner `moduleDepth` rather than an inlined
`Ideal.depth (maximalIdeal _)` spelling. The associated-prime exclusion is also derived API here:
for a torsion-free module over a domain, every nonzero element of an associated prime would be a
zero divisor, so only the generic prime can remain.
-/

-- Proof sketch: this is the torsion-free specialization of Lemma `15.23.13`, but the source text
-- phrases the primewise alternative without exposing the generic-point exclusion
-- `p.asIdeal ≠ ⊥`. In the current depth formalization that generic-point case is not discharged by
-- definitional simplification alone, so the public theorem keeps the source-facing statement and
-- the proof obligation is deferred here rather than strengthening the API.
/-- Lemma 15.23.14: let `R` be a Noetherian domain and let `φ : M → N` be a map of `R`-modules.
Assume `M` is finite, `N` is torsion free, and that for every prime `p` of `R` either the
localized map `Mₚ → Nₚ` is an isomorphism, or the localized module `Mₚ` has depth at least `2`.
Then `φ` is an isomorphism. -/
theorem bijective_of_localizedMap_bijective_or_depth_localizedModule_ge_two_of_isTorsionFree
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : PrimeSpectrum R,
      Function.Bijective (map p.asIdeal.primeCompl φ) ∨
        (2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M)) :
    Function.Bijective φ := by
  sorry

end
