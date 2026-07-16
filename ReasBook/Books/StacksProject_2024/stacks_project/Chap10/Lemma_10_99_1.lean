import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_13

open IsLocalRing

section CriteriaForFlatness

universe u v w x

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Flat R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]

/-- Lemma 10.99.1 (1): if the reduction of an `R`-linear map `u : N → M` modulo the maximal ideal
of `R` is injective, then `u` itself is injective. -/
-- Proof sketch: prove by induction that the induced maps
-- `N / 𝔪^n N → M / 𝔪^n M` are injective for all `n`, using flatness of `M` to control the left
-- exactness of reduction modulo `𝔪^(n+1)` and the finite generation of `N` over the Noetherian
-- ring `S`; then use Krull intersection for the ideal `𝔪S` on `N`.
theorem injective_of_mod_maximalIdeal_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective u := sorry

/-- Lemma 10.99.1 (2): under the same hypothesis, the quotient of `M` by the image of `u` is flat
over `R`. -/
-- Proof sketch: use the injectivity from part (1) to obtain a short exact sequence
-- `0 → N → M → M / range u → 0`; then test flatness of the quotient against `R / I` for an
-- arbitrary ideal `I`, reduce the needed injectivity of `N / IN → M / IM` to part (1) over the
-- local homomorphism `R / I → S / IS`, and conclude by the Tor criterion for flatness.
theorem flat_quotient_of_mod_maximalIdeal_injective
    (u : N →ₗ[R] M)
    (hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R))) :
    Module.Flat R (M ⧸ LinearMap.range u) := sorry

end CriteriaForFlatness
