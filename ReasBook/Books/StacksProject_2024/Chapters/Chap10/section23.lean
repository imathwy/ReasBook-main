import Mathlib
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_23_1 (from Chap10) -/
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

/-! ### Lemma_10_23_2 (from Chap10) -/
universe u v

section Modules

open CategoryTheory
open LocalizedModule
open Module.FinitePresentation
open ShortComplex.ShortExact

local notation "Away" => LocalizedModule.Away

variable {R : Type u} [CommRing R]
variable (s : Finset R)

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type v} [AddCommGroup M'] [Module R M']
variable {M'' : Type v} [AddCommGroup M''] [Module R M'']

-- Proof sketch: if every away-localization of `M` is zero, then every element of `M` maps to zero
-- after localizing at each generator in `s`; apply the local-to-global criterion
-- `Module.eq_zero_of_isLocalized_span` to conclude every element is zero.
/-- Lemma 10.23.2 (1): if the elements of `s` generate the unit ideal and each localization
`M_{f}` for `f ∈ s` is the zero module, then `M` is the zero module. -/
theorem module_subsingleton_of_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, Subsingleton (Away f.1 M)) :
    Subsingleton M := by
  rw [subsingleton_iff_forall_eq 0]
  intro x
  exact Module.eq_zero_of_isLocalized_span (s : Set R) hs
    (fun f ↦ Away f.1 M)
    (fun f ↦ mkLinearMap (Submonoid.powers f.1) M)
    x
    fun f ↦ Subsingleton.elim _ _

/- Locality of finite generation over a standard principal-open cover. This is exactly the
canonical theorem `Module.Finite.of_localizationSpan_finite`. -/
recall Module.Finite.of_localizationSpan_finite

-- Proof sketch: choose a finite presentation of `M` by a finite free module, localize its kernel,
-- use finite presentation of each `M_f` together with the exactness criterion of Lemma 10.5.3, and
-- descend finite generation of the kernel from the cover back to `R`.
/-- Lemma 10.23.2 (2): if the elements of `s` generate the unit ideal and each localization
`M_{f}` is finitely presented over `R_{f}`, then `M` is finitely presented over `R`. -/
theorem module_finitePresentation_of_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, Module.FinitePresentation (Localization.Away f.1)
      (Away f.1 M)) :
    Module.FinitePresentation R M := by
  letI : Module.Finite R M := Module.Finite.of_localizationSpan_finite s hs fun f ↦ by
    letI := h f
    infer_instance
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  have hker : Module.Finite R (LinearMap.ker π) := by
    let κ : ∀ g : s, LinearMap.ker π →ₗ[R]
        Submodule.localized'
          (Localization.Away g.1)
          (Submonoid.powers g.1)
          (mkLinearMap (Submonoid.powers g.1) (Fin n → R))
          (LinearMap.ker π) := fun g ↦
      Submodule.toLocalized'
        (Localization.Away g.1)
        (Submonoid.powers g.1)
        (mkLinearMap (Submonoid.powers g.1) (Fin n → R))
        (LinearMap.ker π)
    letI : ∀ g : s, IsLocalizedModule (Submonoid.powers g.1) (κ g) := fun g ↦ inferInstance
    exact Module.Finite.of_localizationSpan_finite' s hs κ fun g ↦ by
      letI := h g
      let πg : Away g.1 (Fin n → R) →ₗ[Localization.Away g.1] Away g.1 M :=
        LocalizedModule.map (Submonoid.powers g.1) π
      have hπg : Function.Surjective πg := by
        simpa [πg] using LocalizedModule.map_surjective (Submonoid.powers g.1) π hπ
      refine Module.Finite.of_fg ?_
      rw [LinearMap.localized'_ker_eq_ker_localizedMap
        (Localization.Away g.1)
        (Submonoid.powers g.1)
        (mkLinearMap (Submonoid.powers g.1) (Fin n → R))
        (mkLinearMap (Submonoid.powers g.1) M)
        π]
      exact fg_ker πg hπg
  letI : Module.Finite R (LinearMap.ker π) := hker
  exact Module.finitePresentation_of_surjective π hπ Submodule.FG.of_finite

/- Locality of module isomorphisms over a standard principal-open cover. This is exactly the
canonical theorem `bijective_of_localized_span`. -/
recall bijective_of_localized_span

/-- Lemma 10.23.2 (3): if the elements of `s` generate the unit ideal and the localized complex
`0 → M''_{f} → M_{f} → M'_{f} → 0` is exact for every `f ∈ s`, then the original complex
`0 → M'' → M → M' → 0` is exact. -/
theorem shortComplex_shortExact_of_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤) (S : ShortComplex (ModuleCat.{max u v} R))
    (h : ∀ f : s, (S.map
      (ModuleCat.localizedModuleFunctor (Submonoid.powers f.1))).ShortExact) :
    S.ShortExact := by
  have hexact : ∀ f : s,
      Function.Exact
        ((IsLocalizedModule.map
          (Submonoid.powers f.1)
          (S.X₁.localizedModuleMkLinearMap (Submonoid.powers f.1))
          (S.X₂.localizedModuleMkLinearMap (Submonoid.powers f.1))) S.f.hom)
        ((IsLocalizedModule.map
          (Submonoid.powers f.1)
          (S.X₂.localizedModuleMkLinearMap (Submonoid.powers f.1))
          (S.X₃.localizedModuleMkLinearMap (Submonoid.powers f.1))) S.g.hom) := fun f ↦ by
    simpa [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap,
      IsLocalizedModule.mapExtendScalars] using
      (moduleCat_exact_iff_function_exact _).1 (h f).exact
  have hinj : ∀ f : s,
      Function.Injective
        (((IsLocalizedModule.map
          (Submonoid.powers f.1)
          (S.X₁.localizedModuleMkLinearMap (Submonoid.powers f.1))
          (S.X₂.localizedModuleMkLinearMap (Submonoid.powers f.1))) S.f.hom)) := fun f ↦ by
    simpa [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap,
      IsLocalizedModule.mapExtendScalars] using (h f).moduleCat_injective_f
  have hsurj : ∀ f : s,
      Function.Surjective
        (((IsLocalizedModule.map
          (Submonoid.powers f.1)
          (S.X₂.localizedModuleMkLinearMap (Submonoid.powers f.1))
          (S.X₃.localizedModuleMkLinearMap (Submonoid.powers f.1))) S.g.hom)) := fun f ↦ by
    simpa [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap,
      IsLocalizedModule.mapExtendScalars] using (h f).moduleCat_surjective_g
  refine ModuleCat.shortComplex_shortExact S ?_ ?_ ?_
  · exact exact_of_isLocalized_span (s : Set R) hs
      (fun f ↦ S.X₁.localizedModule (Submonoid.powers f.1))
      (fun f ↦ S.X₁.localizedModuleMkLinearMap (Submonoid.powers f.1))
      (fun f ↦ S.X₂.localizedModule (Submonoid.powers f.1))
      (fun f ↦ S.X₂.localizedModuleMkLinearMap (Submonoid.powers f.1))
      (fun f ↦ S.X₃.localizedModule (Submonoid.powers f.1))
      (fun f ↦ S.X₃.localizedModuleMkLinearMap (Submonoid.powers f.1))
      S.f.hom S.g.hom hexact
  · exact injective_of_isLocalized_span (s : Set R) hs
      (fun f ↦ S.X₁.localizedModule (Submonoid.powers f.1))
      (fun f ↦ S.X₁.localizedModuleMkLinearMap (Submonoid.powers f.1))
      (fun f ↦ S.X₂.localizedModule (Submonoid.powers f.1))
      (fun f ↦ S.X₂.localizedModuleMkLinearMap (Submonoid.powers f.1))
      S.f.hom hinj
  · exact surjective_of_isLocalized_span (s : Set R) hs
      (fun f ↦ S.X₂.localizedModule (Submonoid.powers f.1))
      (fun f ↦ S.X₂.localizedModuleMkLinearMap (Submonoid.powers f.1))
      (fun f ↦ S.X₃.localizedModule (Submonoid.powers f.1))
      (fun f ↦ S.X₃.localizedModuleMkLinearMap (Submonoid.powers f.1))
      S.g.hom hsurj

end Modules

section Rings

variable {R : Type u} [CommRing R]
variable (s : Finset R)

/- Locality of the Noetherian property over a standard principal-open cover. This is exactly the
canonical theorem `AlgebraicGeometry.isNoetherianRing_of_away`. -/
recall AlgebraicGeometry.isNoetherianRing_of_away

end Rings

section Algebras

/- Finite type is local on the source for a standard principal-open cover. This is exactly the
canonical theorem `Algebra.FiniteType.of_span_eq_top_source`. -/
recall Algebra.FiniteType.of_span_eq_top_source

/- Finite presentation of an algebra is local on the source for a standard principal-open cover.
The owner declaration is the ring-hom locality theorem
`RingHom.finitePresentation_isLocal`; the tensor-product model `Localization.Away f ⊗[R] S` of
the localized algebra is only a bridge to this owner statement when needed. -/
recall RingHom.finitePresentation_isLocal

end Algebras

/-! ### Lemma_10_23_3 (from Chap10) -/
/- Lemma 10.23.3 (1): if a finite list of elements of `S` generates the unit ideal and each
principal localization `S_g` is of finite type over `R`, then `S` is of finite type over `R`.
This is exactly the canonical locality theorem
`Algebra.FiniteType.of_span_eq_top_target`. -/
recall Algebra.FiniteType.of_span_eq_top_target

/- Lemma 10.23.3 (2): if a finite list of elements of `S` generates the unit ideal and each
principal localization `S_g` is of finite presentation over `R`, then `S` is of finite
presentation over `R`. This is exactly the canonical locality theorem
`Algebra.FinitePresentation.of_span_eq_top_target`. -/
recall Algebra.FinitePresentation.of_span_eq_top_target
