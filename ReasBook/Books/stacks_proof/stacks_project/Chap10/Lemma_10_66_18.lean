import Mathlib
import StacksProject_2024.Chap10.Lemma_10_66_15
import StacksProject_2024.Chap10.Lemma_10_66_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped nonZeroDivisors

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Flat R N]

local notation "R⁰" => nonZeroDivisors R
local notation "T" => Algebra.algebraMapSubmonoid S R⁰
local notation "Sₖ" => Localization T
local notation "Nₖ" => LocalizedModule T N

/-
Domain triage:
- primary domain: weakly associated primes under fraction-ring base change;
- `core/canonical` owner: localize the `S`-module `N` at the image `T` of `R⁰`, namely
  `Nₖ = LocalizedModule T N`;
- `bridge/view`: the textbook tensor model `(S ⊗[R] FractionRing R) ⊗[S] N`.

This item is best stated at the owner layer `Nₖ`, because Lemmas `10.66.15` and `10.66.16`
already provide the canonical localization API for `weaklyAssociatedPrimes`. The tensor-product
presentation is only a derived realization of the same base change, and in the domain case this is
exactly the usual fraction-ring base change.
-/

/-- Lemma 10.66.18, owner form: if `R → S` is a ring map, `N` is an `S`-module that is flat over
`R`, and `T` is the image in `S` of the nonzerodivisors of `R`, then the weakly
associated primes of `N` over `S` coincide with those of the canonical localization owner
`Nₖ = LocalizedModule T N`, still computed over `S`. -/
-- Proof sketch: every element of `R⁰` acts regularly on `N` by flatness over the domain `R`, so
-- every element of its image `T` in `S` acts regularly as well. Lemma 10.66.16 then identifies
-- `WeakAss_S(N)` with `WeakAss_S(Nₖ)`.
@[stacks 05CC]
theorem weaklyAssociatedPrimes_eq_fractionRingBaseChange_as_SModule :
    weaklyAssociatedPrimes S N = weaklyAssociatedPrimes S Nₖ := by
  refine weaklyAssociatedPrimes_eq_localizedModule T ?_
  intro t
  rcases t.2 with ⟨r, hr, hs⟩
  have ht : IsSMulRegular N (algebraMap R S r) :=
    (isSMulRegular_algebraMap_iff S).2
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hr)
  simpa [hs] using ht

/-- Lemma 10.66.18: the weakly associated primes of `N` over `S` are exactly the contractions of
the weakly associated primes of the canonical base change `Nₖ` along the
localization map `S → Sₖ`. -/
-- Proof sketch: first replace `N` by the canonical owner `Nₖ` using the previous theorem. Then
-- apply Lemma 10.66.15 (1) to the localization of `N` at `T`.
@[stacks 05CC]
theorem weaklyAssociatedPrimes_baseChange_to_fractionRing_eq_image_comap :
    weaklyAssociatedPrimes S N =
      Ideal.comap (algebraMap S Sₖ) '' weaklyAssociatedPrimes Sₖ Nₖ := by
  calc
    weaklyAssociatedPrimes S N = weaklyAssociatedPrimes S Nₖ :=
      weaklyAssociatedPrimes_eq_fractionRingBaseChange_as_SModule
    _ = Ideal.comap (algebraMap S Sₖ) '' weaklyAssociatedPrimes Sₖ Nₖ :=
      (weaklyAssociatedPrimes.localizedModule_eq_image_comap T).symm

end
