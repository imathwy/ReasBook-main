import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open Module
open LocalizedModule
open LocalizedModule (AtPrime)

/-
Domain-style sampling:
- primary domain: local properties of module maps detected by localization at prime and maximal
  ideals;
- sampled owner declarations:
  `Module.eq_zero_of_localization_maximal`,
  `Module.subsingleton_of_localization_maximal`,
  `LocalizedModule.map_exact`,
  `injective_of_localized_maximal`,
  `surjective_of_localized_maximal`,
  `bijective_of_localized_maximal`;
- best owner abstraction: the mathlib local-property owners for localized modules and localized
  linear maps, with `LocalizedModule.mkLinearMap` as the canonical bridge;
- source/core/bridge triage:
  `source-facing`: the six textbook `List.TFAE` statements below;
  `core/canonical`: the local-to-global owners listed above;
  `bridge/view`: the prime and maximal localization families built from `AtPrime` and
  `mkLinearMap`.

Primitive data are just the module(s), the linear map(s), and the canonical localization maps.
The prime/maximal conditions are derived predicates on those owners, so this file should keep only
the source-facing TFAE layer and reuse the owner API directly in proofs.
-/

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {M' : Type w} [AddCommMonoid M'] [Module R M']
variable {M₁ : Type v} [AddCommMonoid M₁] [Module R M₁]
variable {M₂ : Type w} [AddCommMonoid M₂] [Module R M₂]
variable {M₃ : Type x} [AddCommMonoid M₃] [Module R M₃]

private theorem tfae_localization_prime_maximal
    {A : Prop} {B : (P : Ideal R) → [P.IsPrime] → Prop}
    (hAB : A → ∀ (P : Ideal R) [P.IsPrime], B P)
    (hCA : (∀ (P : Ideal R) [P.IsMaximal], B P) → A) :
    List.TFAE [A, ∀ (P : Ideal R) [P.IsPrime], B P, ∀ (P : Ideal R) [P.IsMaximal], B P] := by
  tfae_have 1 → 2 := hAB
  tfae_have 2 → 3 := by
    intro h P _
    exact h P
  tfae_have 3 → 1 := hCA
  tfae_finish

/-- Lemma 10.23.1 (1): for an element `x` of an `R`-module `M`, the following are equivalent:
`x = 0`, the image of `x` in `M_𝔭` is zero for every prime ideal `𝔭`, and the image of `x` in
`M_𝔪` is zero for every maximal ideal `𝔪`. -/
-- Proof sketch: `(1) ⇒ (2) ⇒ (3)` is immediate from functoriality of localization. For
-- `(3) ⇒ (1)`, apply `Module.eq_zero_of_localization_maximal` to the canonical maps
-- `LocalizedModule.mkLinearMap P.primeCompl M`; the prime-localization condition specializes to
-- maximal ideals because maximal ideals are prime.
@[stacks 00HN]
theorem element_zero_localization_tfae (x : M) :
    List.TFAE [
      x = 0,
      ∀ (P : Ideal R) [P.IsPrime], mkLinearMap P.primeCompl M x = 0,
      ∀ (P : Ideal R) [P.IsMaximal], mkLinearMap P.primeCompl M x = 0
    ] :=
  tfae_localization_prime_maximal
    (fun hx P _ ↦ by simp [hx])
    (fun h ↦ eq_zero_of_localization_maximal
      (fun P _ ↦ AtPrime P M)
      (fun P _ ↦ mkLinearMap P.primeCompl M) x h)

/-- Lemma 10.23.1 (2): for an `R`-module `M`, the following are equivalent: `M` is the zero
module, `M_𝔭` is the zero module for every prime ideal `𝔭`, and `M_𝔪` is the zero module for every
maximal ideal `𝔪`. -/
-- Proof sketch: if `M` is zero, every localization is zero. Conversely, if all maximal
-- localizations are subsingletons, apply `Module.subsingleton_of_localization_maximal` to the
-- canonical localization maps; the prime-localization condition again implies the maximal one.
@[stacks 00HN]
theorem module_zero_localization_tfae :
    List.TFAE [
      Subsingleton M,
      ∀ (P : Ideal R) [P.IsPrime], Subsingleton (AtPrime P M),
      ∀ (P : Ideal R) [P.IsMaximal], Subsingleton (AtPrime P M)
    ] :=
  tfae_localization_prime_maximal
    (fun hM P _ ↦ by
      letI : Subsingleton M := hM
      simpa [LocalizedModule.AtPrime] using
        (IsLocalizedModule.subsingleton_of_subsingleton P.primeCompl
          (mkLinearMap P.primeCompl M) : Subsingleton (LocalizedModule P.primeCompl M)))
    (fun h ↦ subsingleton_of_localization_maximal
      (fun P _ ↦ AtPrime P M)
      (fun P _ ↦ mkLinearMap P.primeCompl M) h)

/-- Lemma 10.23.1 (3): for a complex `M₁ ⟶ M₂ ⟶ M₃` of `R`-modules, the following are
equivalent: the complex is exact, its localization at every prime ideal is exact, and its
localization at every maximal ideal is exact. -/
-- Proof sketch: exactness localizes by `LocalizedModule.map_exact`, giving `(1) ⇒ (2) ⇒ (3)`.
-- For `(3) ⇒ (1)`, use `exact_of_localized_maximal`; the maximal-localization hypotheses are
-- obtained by specializing the prime-localization hypotheses when needed.
@[stacks 00HN]
theorem exact_localization_tfae (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
    List.TFAE [
      Function.Exact f g,
      ∀ (P : Ideal R) [P.IsPrime], Function.Exact (map P.primeCompl f) (map P.primeCompl g),
      ∀ (P : Ideal R) [P.IsMaximal], Function.Exact (map P.primeCompl f) (map P.primeCompl g)
    ] :=
  tfae_localization_prime_maximal
    (fun hfg P _ ↦ map_exact P.primeCompl f g hfg)
    (exact_of_localized_maximal f g)

/-- Lemma 10.23.1 (4): for a map `f : M → M'` of `R`-modules, the following are equivalent:
`f` is injective, the localized map `f_𝔭` is injective for every prime ideal `𝔭`, and the
localized map `f_𝔪` is injective for every maximal ideal `𝔪`. -/
-- Proof sketch: localization preserves injectivity by `LocalizedModule.map_injective`, so
-- `(1) ⇒ (2) ⇒ (3)`. For `(3) ⇒ (1)`, invoke `injective_of_localized_maximal`; the prime case
-- specializes to the maximal case because every maximal ideal is prime.
@[stacks 00HN]
theorem injective_localization_tfae (f : M →ₗ[R] M') :
    List.TFAE [
      Function.Injective f,
      ∀ (P : Ideal R) [P.IsPrime], Function.Injective (map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl f)
    ] :=
  tfae_localization_prime_maximal
    (fun hf P _ ↦ map_injective P.primeCompl f hf)
    (injective_of_localized_maximal f)

/-- Lemma 10.23.1 (5): for a map `f : M → M'` of `R`-modules, the following are equivalent:
`f` is surjective, the localized map `f_𝔭` is surjective for every prime ideal `𝔭`, and the
localized map `f_𝔪` is surjective for every maximal ideal `𝔪`. -/
-- Proof sketch: localization preserves surjectivity by `LocalizedModule.map_surjective`, giving
-- `(1) ⇒ (2) ⇒ (3)`. For `(3) ⇒ (1)`, apply `surjective_of_localized_maximal`; the prime
-- condition restricts to maximal ideals.
@[stacks 00HN]
theorem surjective_localization_tfae (f : M →ₗ[R] M') :
    List.TFAE [
      Function.Surjective f,
      ∀ (P : Ideal R) [P.IsPrime], Function.Surjective (map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal], Function.Surjective (map P.primeCompl f)
    ] :=
  tfae_localization_prime_maximal
    (fun hf P _ ↦ map_surjective P.primeCompl f hf)
    (surjective_of_localized_maximal f)

/-- Lemma 10.23.1 (6): for a map `f : M → M'` of `R`-modules, the following are equivalent:
`f` is bijective, the localized map `f_𝔭` is bijective for every prime ideal `𝔭`, and the
localized map `f_𝔪` is bijective for every maximal ideal `𝔪`. -/
-- Proof sketch: combine the injective and surjective cases. Localization preserves bijectivity,
-- and `bijective_of_localized_maximal` recovers global bijectivity from the maximal-localization
-- condition.
@[stacks 00HN]
theorem bijective_localization_tfae (f : M →ₗ[R] M') :
    List.TFAE [
      Function.Bijective f,
      ∀ (P : Ideal R) [P.IsPrime], Function.Bijective (map P.primeCompl f),
      ∀ (P : Ideal R) [P.IsMaximal], Function.Bijective (map P.primeCompl f)
    ] :=
  tfae_localization_prime_maximal
    (fun hf P _ ↦ ⟨map_injective P.primeCompl f hf.1, map_surjective P.primeCompl f hf.2⟩)
    (bijective_of_localized_maximal f)

end
