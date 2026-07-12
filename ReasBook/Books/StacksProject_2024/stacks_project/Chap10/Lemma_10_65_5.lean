import Mathlib
import StacksProject_2024.Chap10.Lemma_10_65_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/- Domain triage:
* primary domain: associated primes under flat base change along `R → S`;
* source-facing layer: the chapter owner `relativeAssassin R S N` together with the textbook
  exact-annihilator set `associatedPrimesOfModule`;
* core/canonical layer: mathlib's Noetherian owner `associatedPrimes`;
* bridge/view: the contraction description of the fiberwise union coming from Lemma 10.65.1 and
  Remark 10.18.5.

This item stays at the source-facing layer. The Noetherian equality is stated for
`associatedPrimesOfModule`, and any owner-form restatement via `associatedPrimes` belongs in a
later bridge file.
-/

-- Proof sketch: rewrite the fiberwise union from the source as
-- `relativeAssassin R S N ∩ {q | q.asIdeal.under R ∈ associatedPrimesOfModule R M}` using
-- Lemma 10.65.1 together with the fiber-spectrum identification from Remark 10.18.5, then apply
-- Lemma 10.65.3(1) to the contracted prime quotient modules `N / pN`.
/-- Lemma 10.65.5 (1): if `N` is flat over `R`, then every associated prime of a fiber module
`κ(𝔭) ⊗[R] N`, viewed as a prime of `S` by the canonical map
`Spec (κ(𝔭) ⊗[R] S) → Spec S`, for `𝔭 ∈ Ass_R(M)`, is an associated prime of the base-changed
module `M ⊗[R] N`. In Lean the canonically `S`-linear tensor model is written `N ⊗[R] M`. -/
theorem fiberAssociatedPrimes_subset_associatedPrimesOfModule_tensorProduct
    [Module.Flat R N] :
    relativeAssassin R S N ∩
        { q : PrimeSpectrum S | q.asIdeal.under R ∈ associatedPrimesOfModule R M } ⊆
      { q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) } := sorry

-- Proof sketch: combine the source-facing inclusion above with the Noetherian converse furnished
-- by Lemma 10.65.3(2), again rewriting the fiberwise union through the contraction description
-- from Lemma 10.65.1 and Remark 10.18.5.
/-- Lemma 10.65.5 (2): if `R` is Noetherian and `N` is flat over `R`, then the associated primes
of `M ⊗[R] N` over `S` are exactly the fiberwise associated primes over those
`𝔭 ∈ Ass_R(M)`, viewed inside `Spec S` by the canonical maps from the fiber spectra. In Lean this
is expressed by equality with
`relativeAssassin R S N ∩ { q | q.asIdeal.under R ∈ associatedPrimesOfModule R M }`. -/
theorem associatedPrimesOfModule_tensorProduct_eq_fiberAssociatedPrimes_of_isNoetherianRing
    [Module.Flat R N] [IsNoetherianRing R] :
    { q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) } =
      relativeAssassin R S N ∩
        { q : PrimeSpectrum S | q.asIdeal.under R ∈ associatedPrimesOfModule R M } := sorry

end
