import stacks_proof.stacks_project.Chap10.Lemma_10_63_19
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open LocalizedModule (map mkLinearMap)

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Domain triage:
* primary domain: injectivity criteria for module maps over a Noetherian ring via associated-prime
  localizations;
* sampled owner declarations:
  `associatedPrimes R M`,
  `LocalizedModule.map`,
  `LocalizedModule.mkLinearMap`,
  `to_pi_localization_at_associated_primes_injective`;
* best owner abstraction: the owner index type `associatedPrimes R M` together with the canonical
  map `M → ∏ p ∈ Ass(M), Mₚ`;
* primitive data: the linear map `φ : M →ₗ[R] N`;
* derived API: injectivity of the localized maps at the associated primes of `M`.

Layering:
* this numbered item is `source-facing`: it is the associated-prime criterion for injectivity from
  the source text;
* the `core/canonical` owner is the chapter theorem
  `to_pi_localization_at_associated_primes_injective`;
* there is no separate `bridge/view` owner to introduce here. The theorem should reuse the owner
  index set `associatedPrimes R M` directly rather than restating it through all prime-spectrum
  points with an implication.
-/

-- Proof sketch: the canonical map from `M` to the product of the localizations `∏_{p ∈ Ass(M)} Mₚ`
-- is injective by Lemma `10.63.19`. If `φ x = φ y`, then for every associated prime `p` the
-- localized equality `φₚ(x/1) = φₚ(y/1)` holds; injectivity of `φₚ` gives `x/1 = y/1` in `Mₚ`.
-- Hence `x` and `y` have the same image in the product of localizations at the associated primes,
-- so they are equal.
/-- Lemma 15.23.12: if `R` is Noetherian and every associated prime of `M` is a prime at which the
localized map `M_p → N_p` is injective, then `φ : M →ₗ[R] N` is injective. -/
@[stacks 0AV7]
theorem injective_of_injective_localizedMap_at_associatedPrimes
    (φ : M →ₗ[R] N)
    (hφ : ∀ p : associatedPrimes R M,
      Function.Injective (map ((p : Ideal R).primeCompl) φ)) :
    Function.Injective φ := by
  intro x y hxy
  exact to_pi_localization_at_associated_primes_injective <| by
    ext p
    exact hφ p <| by
      simpa [LinearMap.pi_apply, LocalizedModule.map_mk] using
        congrArg (mkLinearMap ((p : Ideal R).primeCompl) N) hxy

end
