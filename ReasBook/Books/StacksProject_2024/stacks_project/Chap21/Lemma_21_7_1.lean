import StacksProject_2024.stacks_project.Chap18.Remark_18_19_7
import StacksProject_2024.stacks_project.Chap21.SheafOfModulesForgetPreservesInjectiveObjects
import StacksProject_2024.stacks_project.Chap21.Lemma_21_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

/- Domain-style sampling for Lemma 21.7.1:
- primary domain: localized restriction of module sheaves on a ringed site and preservation of
  injective objects by the resulting functor;
- sampled owner declarations:
  `Functor.PreservesInjectiveObjects`,
  `CategoryTheory.sheafOfModulesForgetPreservesInjectiveObjects`,
  `Functor.injective_obj_of_injective`,
  `SheafOfModules.pushforward`;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical localized
  restriction functor `SheafOfModules.pushforward (𝟙 (𝒪.over U))`, reusing the Chapter 21 support
  instance `CategoryTheory.sheafOfModulesForgetPreservesInjectiveObjects` for the ambient forgetful
  functor;
- primitive data: only the ring-valued sheaf `𝒪` and the object `U : C`;
- derived API: the source-facing objectwise injectivity statement and the cohomology comparison.

Source/core/bridge triage:
- `source-facing`: the textbook assertions that restriction to `(Over U, 𝒪.over U)`
  sends injectives to injectives and computes cohomology over `U`;
- `core/canonical`: `Functor.PreservesInjectiveObjects` for
  `SheafOfModules.pushforward (𝟙 (𝒪.over U))`, together with the shared support instance
  `CategoryTheory.sheafOfModulesForgetPreservesInjectiveObjects`;
- `bridge/view`: the objectwise injectivity corollary below. -/

/-- Helper for Lemma 21.7.1: the presheaf-level localized restriction functor preserves injective
objects because it is right adjoint to exact extension by zero. -/
-- Proof sketch: use the Chapter 18 exactness owner for presheaf extension by zero on `Over U`,
-- then apply Lemma `12.29.1` to the canonical pullback-pushforward adjunction.
private instance presheaf_localizedRestriction_preservesInjectiveObjects
    (𝒪 : Sheaf J RingCat.{u}) (U : C) :
    (PresheafOfModules.pushforward.{u} (𝟙 ((Over.forget U).op ⋙ 𝒪.obj))).PreservesInjectiveObjects := by
  simpa using CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint
    (PresheafOfModules.pullbackPushforwardAdjunction (𝟙 ((Over.forget U).op ⋙ 𝒪.obj)))
    (presheafLocalizedExtensionByZero_exact 𝒪.obj U)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Helper for Lemma 21.7.1: a localized `𝒪.over U`-module is injective once its underlying
presheaf of modules is injective. -/
-- Proof sketch: forget a monomorphism in `SheafOfModules (𝒪.over U)` to presheaves, extend there
-- using injectivity of the underlying presheaf object, and reuse the same morphism in the full
-- sheaf subcategory.
private lemma injective_of_injective_underlying_presheaf
    (𝒪 : Sheaf J RingCat.{u}) (U : C) (M : SheafOfModules (𝒪.over U))
    (hM : Injective ((SheafOfModules.forget (𝒪.over U)).obj M)) :
    Injective M := by
  let F := SheafOfModules.forget (𝒪.over U)
  letI : F.Faithful := inferInstance
  refine ⟨fun g f ↦ ?_⟩
  intro hf
  -- Forget the extension problem to presheaf modules.
  let f' := F.map f
  let g' := F.map g
  have hf' : Mono f' := by
    simpa [f'] using (show Mono f from hf)
  obtain ⟨h', hh'⟩ := hM.factors g' f'
  -- The presheaf morphism is already a morphism of sheaf modules.
  refine ⟨SheafOfModules.Hom.mk h', ?_⟩
  apply F.map_injective
  simpa [f', g'] using hh'

/-- Lemma 21.7.1 (1), owner form: restriction to the localized ringed site preserves injective
objects. -/
-- Proof sketch: restriction to the localized ringed site is right adjoint to extension by zero,
-- and extension by zero is exact; apply the standard adjunction criterion that a right adjoint to
-- an exact functor preserves injective objects.
@[stacks 03F3]
instance ringedSite_localizationModuleRestriction_preservesInjectiveObjects
    (𝒪 : Sheaf J RingCat.{u}) (U : C) :
    (SheafOfModules.pushforward.{u} (𝟙 (𝒪.over U))).PreservesInjectiveObjects where
  injective_obj {ℐ} hℐ := by
    -- First forget the ambient injective sheaf module to an injective presheaf module.
    let K := PresheafOfModules.pushforward.{u} (𝟙 ((Over.forget U).op ⋙ 𝒪.obj))
    letI : K.PreservesInjectiveObjects :=
      presheaf_localizedRestriction_preservesInjectiveObjects 𝒪 U
    have hUnderlying :
        Injective
          ((SheafOfModules.forget (𝒪.over U)).obj
            ((SheafOfModules.pushforward.{u} (𝟙 (𝒪.over U))).obj ℐ)) := by
      have hForget : Injective ((SheafOfModules.forget 𝒪).obj ℐ) :=
        injective_as_presheaf_of_modules ℐ hℐ
      simpa [K] using K.injective_obj_of_injective hForget
    -- Then descend injectivity back from presheaf modules to sheaf modules.
    exact injective_of_injective_underlying_presheaf 𝒪 U _ hUnderlying

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Lemma 21.7.1 (1), objectwise form: if `ℐ` is an injective `𝒪`-module on a ringed
site `(C, 𝒪)`, then its restriction to the localized ringed site
`(Over U, 𝒪.over U)` is an injective `𝒪.over U`-module. -/
@[stacks 03F3]
theorem ringedSite_localizationModuleRestriction_injective
    (𝒪 : Sheaf J RingCat.{u}) (U : C) (ℐ : SheafOfModules.{u} 𝒪)
    (hℐ : Injective ℐ) :
    Injective (ℐ.over U) := by
  simpa [SheafOfModules.over] using
    (SheafOfModules.pushforward.{u} (𝟙 (𝒪.over U))).injective_obj_of_injective hℐ

-- Proof sketch: compare the canonical module-valued cohomology owner
-- `SheafOfModules.cohomologyAtObjectFunctor` on `(C, 𝒪)` at `U` with the same
-- owner on the localized site `(Over U, 𝒪.over U)` at the terminal object
-- `Over.mk (𝟙 U)`. Part (1) supplies injective objects after restriction, and the underived
-- sections functors agree on the nose.
omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Lemma 21.7.1 (2), owner form: the canonical module-valued cohomology owner at `U` agrees with
the corresponding owner on the localized ringed site at the terminal slice object. -/
@[stacks 03F3]
theorem ringedSite_localizationModuleRestriction_cohomologyAtObject_isomorphic
    (𝒪 : Sheaf J RingCat.{u}) (U : C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt (Sheaf J AddCommGrpCat.{u})]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [HasExt (Sheaf (J.over U) AddCommGrpCat.{u})]
    (ℱ : SheafOfModules.{u} 𝒪) (p : ℕ) :
    IsIsomorphic
      ((SheafOfModules.cohomologyAtObjectFunctor 𝒪 p U).obj ℱ)
      ((SheafOfModules.cohomologyAtObjectFunctor (𝒪.over U) p
        (Over.mk (𝟙 U))).obj (ℱ.over U)) := by
  sorry

-- Proof sketch: transport the owner-form comparison through the canonical Chapter 21 bridge
-- `SheafOfModules.cohomologyAtObject_isomorphic` on both sites. This yields the source-facing
-- comparison of cohomology over `U` with cohomology at the terminal object of the localized site.
omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Lemma 21.7.1 (2), terminal-object form: the cohomology of the underlying abelian sheaf of
`ℱ` over `U` agrees with the cohomology of the restricted module on the localized site,
evaluated at the terminal object `Over.mk (𝟙 U)`. -/
@[stacks 03F3]
theorem ringedSite_localizationModuleRestriction_cohomologyAtTerminal_isomorphic
    (𝒪 : Sheaf J RingCat.{u}) (U : C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt (Sheaf J AddCommGrpCat.{u})]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [HasExt (Sheaf (J.over U) AddCommGrpCat.{u})]
    (ℱ : SheafOfModules.{u} 𝒪) (p : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' p U)
      (((SheafOfModules.toSheaf (𝒪.over U)).obj (ℱ.over U)).H' p (Over.mk (𝟙 U))) := by
  sorry

-- Proof sketch: identify the terminal-object cohomology on the slice site with the usual global
-- cohomology of the restricted underlying abelian sheaf, then compose with the terminal-object
-- comparison above.
omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Lemma 21.7.1 (2): for an `𝒪`-module `ℱ` on a ringed site
`(C, 𝒪)` and an object `U : C`, the cohomology of `ℱ` over `U`
agrees with the global cohomology of the restricted module on the localized ringed site
`(Over U, 𝒪.over U)`. -/
@[stacks 03F3]
theorem ringedSite_localizationModuleRestriction_cohomologyOver_eq
    (𝒪 : Sheaf J RingCat.{u}) (U : C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt (Sheaf J AddCommGrpCat.{u})]
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [HasExt (Sheaf (J.over U) AddCommGrpCat.{u})]
    (ℱ : SheafOfModules.{u} 𝒪) (p : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' p U)
      (AddCommGrpCat.of (((SheafOfModules.toSheaf (𝒪.over U)).obj (ℱ.over U)).H p)) := by
  sorry
