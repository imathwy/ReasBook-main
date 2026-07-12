import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

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

/-- Helper for Lemma 18.27.2: at each slice object, restricting the local-Hom sheaf from the base
site differs from the slice-site local-Hom sheaf only by restriction of scalars along the
identity map of the slice structure ring. -/
private theorem localHomOverPresheafIso_app (U : C) (X : (Over U)ᵒᵖ) :
    (((localHomSheaf 𝒪 ℱ 𝒢).over U).val.obj X) ≅
      ((localHomSheaf (𝒪.over U)
        ((pushforward₀ (Over.forget U) (ringSheaf J 𝒪).obj).obj ℱ)
        (𝒢.over U)).val.obj X) := by
  sorry

/-- Helper for Lemma 18.27.2: the objectwise identity restriction-of-scalars adapters commute
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
  sorry

/-- Helper for Lemma 18.27.2: the restricted local-Hom sheaf and the slice-site local-Hom sheaf
have canonically isomorphic underlying presheaves of modules. -/
private noncomputable def localHom_over_presheaf_iso (U : C) :
    ((localHomSheaf 𝒪 ℱ 𝒢).over U).val ≅
      (localHomSheaf (𝒪.over U)
        ((pushforward₀ (Over.forget U) (ringSheaf J 𝒪).obj).obj ℱ)
        (𝒢.over U)).val :=
  sorry

/-- Lemma 18.27.2: for a ringed site `(\mathcal C, J, \mathcal O)`, a presheaf of
`\mathcal O`-modules `\mathcal F`, a sheaf of `\mathcal O`-modules `\mathcal G`, and an object
`U : \mathcal C`, formation of the internal Hom sheaf commutes with localization to the slice
site `(\mathcal C/U, J.over U)`. The localized source presheaf is expressed through the canonical
restriction functor `PresheafOfModules.pushforward₀`, and the two localized internal-Hom sheaves
are canonically isomorphic. -/
theorem localHomSheaf_overIsomorphic (U : C) :
    IsIsomorphic ((localHomSheaf 𝒪 ℱ 𝒢).over U)
      (localHomSheaf (𝒪.over U)
        ((pushforward₀ (Over.forget U) (ringSheaf J 𝒪).obj).obj ℱ)
        (𝒢.over U)) := by
  sorry

end PresheafOfModules
