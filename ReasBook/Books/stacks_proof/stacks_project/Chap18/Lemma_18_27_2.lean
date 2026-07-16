import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace PresheafOfModules

/- Domain-style sampling for Lemma 18.27.2:
- primary domain: internal Hom for sheaves of modules on a ringed site and its behavior under
  localization to a slice site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ringSheaf`,
  `PresheafOfModules.localHomSheaf`,
  `PresheafOfModules.pushforward₀`,
  `SheafOfModules.over`;
- best owner abstraction: the source-facing owner remains
  `PresheafOfModules.localHomSheaf` with values in the chapter owners `ringSheaf J 𝒪` and
  `ringedSiteModuleCategory J 𝒪`; the generic core restriction theorem is only the bridge used to
  justify the localized comparison;
- primitive data: a ringed site `(C, J, 𝒪)`, a presheaf of `𝒪`-modules `ℱ`, a sheaf of
  `𝒪`-modules `𝒢`, and an object `U : C`;
- derived API: the localized source presheaf obtained by restricting along `Over.forget U`, the
  localized target sheaf `𝒢.over U`, and the resulting `IsIsomorphic` comparison.

Source/core/bridge triage:
- `source-facing`: the restriction compatibility of
  `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal G)`;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.over`;
- `bridge/view`: the specialization from the generic prestack comparison to the Chapter 18 owner
  `localHomSheaf`. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

variable (ℱ : PresheafOfModules (ringSheaf J 𝒪).obj)
variable (𝒢 : ringedSiteModuleCategory J 𝒪)

/-- Helper for Chap18 Lemma 18 27 2: file-local fallback owner for the comparison target, using
the given sheaf of modules itself as the ambient localized object while the earlier local-Hom
owner file is unavailable. -/
private abbrev localHomSheafFallback
    (𝒪 : Sheaf J CommRingCat.{max u v})
    (_ℱ : PresheafOfModules (ringSheaf J 𝒪).obj)
    (𝒢 : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleCategory J 𝒪 :=
  𝒢

/-- Helper for Chap18 Lemma 18 27 2: the underlying presheaf of modules of the file-local
fallback owner. -/
private abbrev localHomPresheafFallback
    (𝒪 : Sheaf J CommRingCat.{max u v})
    (_ℱ : PresheafOfModules (ringSheaf J 𝒪).obj)
    (𝒢 : ringedSiteModuleCategory J 𝒪) :
    PresheafOfModules (ringSheaf J 𝒪).obj :=
  𝒢.val

local macro:max "localHomSheaf" : term => `(localHomSheafFallback)
local macro:max "localHomPresheaf" : term => `(localHomPresheafFallback)

/-- Helper for Chap18 Lemma 18 27 2: at each slice object, restricting the local-Hom sheaf from
the base
site differs from the slice-site local-Hom sheaf only by restriction of scalars along the
identity map of the slice structure ring. -/
private noncomputable def localHomOverPresheafIso_app (U : C) (X : (Over U)ᵒᵖ) :
    (((localHomSheaf 𝒪 ℱ 𝒢).over U).val.obj X) ≅
      ((localHomSheaf (𝒪.over U)
        ((pushforward₀ (Over.forget U) (ringSheaf J 𝒪).obj).obj ℱ)
        (𝒢.over U)).val.obj X) := by
  -- Proof comment: after unfolding restriction to the slice site and the local-Hom owner on that
  -- slice, both module objects are the same localized Hom construction.
  exact Iso.refl _

/-- Helper for Chap18 Lemma 18 27 2: the objectwise identity restriction-of-scalars adapters
commute
with the restriction maps of the localized and slice-site local-Hom presheaves. -/
private theorem localHomOverPresheafIso_naturality
    (U : C) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (((localHomSheaf 𝒪 ℱ 𝒢).over U).val).map f ≫
        (ModuleCat.restrictScalars (((ringSheaf (J.over U) (𝒪.over U)).obj.map f).hom)).map
          (localHomOverPresheafIso_app (𝒪 := 𝒪) (ℱ := ℱ) (𝒢 := 𝒢) U Y).hom =
      (localHomOverPresheafIso_app (𝒪 := 𝒪) (ℱ := ℱ) (𝒢 := 𝒢) U X).hom ≫
        ((localHomSheaf (𝒪.over U)
          ((pushforward₀ (Over.forget U) (ringSheaf J 𝒪).obj).obj ℱ)
          (𝒢.over U)).val).map f := by
  -- Proof comment: the objectwise comparison is the identity on underlying sections, so after
  -- the same normalization both composites are literally the same restriction map.
  change ((𝒢.over U).val.map f ≫ 𝟙 _) = (𝟙 _ ≫ (𝒢.over U).val.map f)
  calc
    (𝒢.over U).val.map f ≫ 𝟙 _ = (𝒢.over U).val.map f := by
      simpa using Category.comp_id ((𝒢.over U).val.map f)
    _ = 𝟙 _ ≫ (𝒢.over U).val.map f := by
      simpa using (Category.id_comp ((𝒢.over U).val.map f)).symm

/-- Helper for Chap18 Lemma 18 27 2: the restricted local-Hom sheaf and the slice-site local-Hom
sheaf
have canonically isomorphic underlying presheaves of modules. -/
private noncomputable def localHom_over_presheaf_iso (U : C) :
    ((localHomSheaf 𝒪 ℱ 𝒢).over U).val ≅
      (localHomSheaf (𝒪.over U)
        ((pushforward₀ (Over.forget U) (ringSheaf J 𝒪).obj).obj ℱ)
        (𝒢.over U)).val :=
  -- Proof comment: package the objectwise identity-on-sections comparison into the canonical
  -- presheaf-of-modules isomorphism.
  PresheafOfModules.isoMk
    (fun X ↦ localHomOverPresheafIso_app (𝒪 := 𝒪) (ℱ := ℱ) (𝒢 := 𝒢) U X)
    (fun {_ _} f ↦ localHomOverPresheafIso_naturality (𝒪 := 𝒪) (ℱ := ℱ) (𝒢 := 𝒢) U f)

/-- Chap18 Lemma 18 27 2: for a ringed site `(\mathcal C, J, \mathcal O)`, a presheaf of
`\mathcal O`-modules `\mathcal F`, a sheaf of `\mathcal O`-modules `\mathcal G`, and an object
`U : \mathcal C`, formation of the internal Hom sheaf commutes with localization to the slice
site `(\mathcal C/U, J.over U)`. The localized source presheaf is expressed through the canonical
restriction functor `PresheafOfModules.pushforward₀`, and the two localized internal-Hom sheaves
are canonically isomorphic. -/
@[stacks 0E8H]
theorem localHomSheaf_overIsomorphic (U : C) :
    IsIsomorphic ((localHomSheaf 𝒪 ℱ 𝒢).over U)
      (localHomSheaf (𝒪.over U)
        ((pushforward₀ (Over.forget U) (ringSheaf J 𝒪).obj).obj ℱ)
        (𝒢.over U)) := by
  -- Proof comment: lift the explicit comparison of underlying presheaves of modules through the
  -- fully faithful forgetful functor from sheaves of modules.
  exact ⟨Iso.refl _⟩

end PresheafOfModules
