import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_66_9
import stacks_proof.stacks_project.Chap10.Lemma_10_66_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open LocalizedModule

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage:
* `source-facing`: this item is the associated-prime-indexed localization map from the Stacks
  statement.
* `core/canonical`: the canonical family of localization maps is `LocalizedModule.mkLinearMap`,
  assembled over an index set by `LinearMap.pi`.
* `bridge/view`: this theorem reindexes the weakly-associated-prime statement from
  `Lemma_10_66_17` along `associatedPrimes_eq_weaklyAssociatedPrimes`, so it should stay a thin
  bridge rather than introducing a parallel map definition. -/

/-- Lemma 10.63.19: if `R` is Noetherian, then the canonical map from `M` to the product of its
localizations at the associated primes of `M` is injective. -/
-- Proof sketch: if `x : M` maps to zero in every localization `M_𝔭` for `𝔭 ∈ associatedPrimes R M`,
-- then any associated prime of the cyclic submodule `R ∙ x` also lies in `associatedPrimes R M`
-- by Lemma 10.63.3, but localization at that prime would keep `R ∙ x` nonzero. Hence
-- `associatedPrimes R (R ∙ x) = ∅`, so Lemma 10.63.7 forces `R ∙ x = 0`, and therefore `x = 0`.
@[stacks 0311]
theorem to_pi_localization_at_associated_primes_injective :
    Function.Injective
      (LinearMap.pi fun p : associatedPrimes R M ↦
        mkLinearMap p.1.primeCompl M) :=
  by
    let reindex :
        ((p : associatedPrimes R M) → LocalizedModule.AtPrime (p : Ideal R) M) ≃ₗ[R]
          ((p : weaklyAssociatedPrimes R M) → LocalizedModule.AtPrime (p : Ideal R) M) :=
      LinearEquiv.piCongrLeft R
        (fun p : weaklyAssociatedPrimes R M ↦ LocalizedModule.AtPrime (p : Ideal R) M)
        (Equiv.setCongr associatedPrimes_eq_weaklyAssociatedPrimes)
    have hcomp :
        reindex.toLinearMap.comp
            (LinearMap.pi fun p : associatedPrimes R M ↦ mkLinearMap p.1.primeCompl M) =
          LinearMap.pi fun p : weaklyAssociatedPrimes R M ↦ mkLinearMap p.1.primeCompl M := by
      ext x p
      rfl
    have hinj :
        Function.Injective
          ⇑(reindex.toLinearMap.comp
            (LinearMap.pi fun p : associatedPrimes R M ↦ mkLinearMap p.1.primeCompl M)) := by
      simpa [hcomp] using
        (weaklyAssociatedPrimes_localizationMap_injective :
          Function.Injective
            ⇑(LinearMap.pi fun p : weaklyAssociatedPrimes R M ↦ mkLinearMap p.1.primeCompl M))
    intro x y hxy
    exact hinj <| by simpa using congrArg reindex hxy

end
