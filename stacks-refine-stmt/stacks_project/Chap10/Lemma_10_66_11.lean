import stacks_project.Chap10.Definition_10_66_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/- Domain triage:
* `source-facing`: the textbook statement is the image inclusion for `weaklyAssociatedPrimes`
  under restriction of scalars.
 * `core/canonical`: the owner object is the set-valued declaration `weaklyAssociatedPrimes R M`,
  with the ambient `R`-module structure carried by `[Module R M] [IsScalarTower R S M]` rather
  than rebuilt ad hoc by repeated `Module.compHom`.
 * `bridge/view`: the pointwise lifting of one weakly associated prime is kept internal and the
  set-theoretic inclusion remains the only public theorem. -/

namespace weaklyAssociatedPrimes

/- Internal pointwise lifting used to derive Lemma 10.66.11. Every weakly associated prime of `M`
over `R` lifts to a weakly associated prime of `M` over `S` whose contraction along
`algebraMap R S` is the given prime. -/
-- Proof sketch: let `𝔭 ∈ WeakAss_R(M)`. After localizing at `𝔭`, Lemma 10.66.2 gives an element
-- of the localized module whose annihilator has radical the maximal ideal. Regard the same element
-- over the localized `S`-algebra, choose a minimal prime over its annihilator there, and apply
-- Lemma 10.66.2 again to obtain a weakly associated prime of `M` over `S` contracting to `𝔭`.
private theorem exists_mem_comap_eq_of_mem
    (S : Type v) [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    {𝔭 : Ideal R}
    (h𝔭 : 𝔭 ∈ weaklyAssociatedPrimes R M) :
    ∃ 𝔮 ∈ weaklyAssociatedPrimes S M, Ideal.comap (algebraMap R S) 𝔮 = 𝔭 := by
  sorry

/-- Lemma 10.66.11: under the map `Spec(algebraMap R S)`, the weakly associated primes of the
`R`-module `M` are contained in the image of the weakly associated primes of `M` over `S`. -/
theorem subset_comap_image :
    weaklyAssociatedPrimes R M ⊆
      Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M := by
  intro 𝔭 h𝔭
  rcases exists_mem_comap_eq_of_mem S h𝔭 with ⟨𝔮, h𝔮, hcomap⟩
  exact ⟨𝔮, h𝔮, hcomap⟩

end weaklyAssociatedPrimes

end
