import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 00EO]
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
@[stacks 00EO]
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
@[stacks 00EO]
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
