import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Lemma_18_44_1
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped LocalizedPresheaf

noncomputable section

universe u v

section

namespace CategoryTheory.Presheaf.SubmonoidPresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

variable (𝒮 : SubmonoidPresheaf O.obj)

local notation "Mod(" O ")" => ringedSiteModuleCategory J O

/-- Helper for Lemma 18.44.2: the localization structure map packaged in the same-site
pushforward form required by `SheafOfModules.pullbackPushforwardAdjunction`. -/
private abbrev sameSiteStructureMap :
    ringSheaf J O ⟶
      ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj
        (ringSheaf J ((presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf)) :=
  show ringSheaf J O ⟶
      ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj
        (ringSheaf J ((presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf)) from
    ringSheafMap 𝒮.toSheafifiedLocalizationPresheaf

variable
  [(SheafOfModules.pushforward (sameSiteStructureMap (J := J) (𝒮 := 𝒮))).IsRightAdjoint]

variable (ℱ : Mod(O))

/- Domain-style sampling for Lemma 18.44.2:
- primary domain: sheafified localization of module sheaves along a multiplicative subpresheaf of
  the structure sheaf on a fixed site;
- sampled owner declarations:
  `CategoryTheory.Presheaf.SubmonoidPresheaf.toSheafifiedLocalizationPresheaf`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`,
  `SheafOfModules.RingedSite.restrictionAlong`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: use the canonical pullback object for the localization structure map as
  the source-facing owner `(𝒮⁻¹ℱ)^#[J]`, so the universal property is exactly the adjunction
  universal property for pullback/pushforward on the same site;
- primitive data: a multiplicative subpresheaf `𝒮 : SubmonoidPresheaf O.obj` and an
  `O`-module sheaf `ℱ : ringedSiteModuleCategory J O`;
- derived API: the pullback owner `(𝒮⁻¹ℱ)^#[J]` and the canonical localization morphism
  `toSheafifiedLocalizedModule 𝒮 ℱ`.

Source/core/bridge triage:
- `source-facing`: the localized module `(𝒮⁻¹ℱ)^#[J]` and its universal property;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction` for
  `ringedSiteStructureMap 𝒮.toSheafifiedLocalizationPresheaf`;
- `bridge/view`: the notation `(𝒮⁻¹ℱ)^#[J]`, which packages the canonical pullback owner in the
  source-facing localization notation. -/

/- Lemma 18.44.2, owner form: the localized module `(𝒮⁻¹ℱ)^#[J]` is the pullback of `ℱ` along
the canonical ring-sheaf map `\mathcal O ⟶ (\mathcal S^{-1}\mathcal O)^#[J]`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/-- Helper for Lemma 18.44.2: the localized module notation `(𝒮⁻¹ℱ)^#[J]` denotes the canonical
pullback owner along the sheafified localization of the structure sheaf. -/
noncomputable abbrev sheafifiedLocalizedModule
    (ℱ : Mod(O)) :
    ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf) :=
  (SheafOfModules.pullback
    (sameSiteStructureMap (J := J) (𝒮 := 𝒮))).obj ℱ

namespace SheafifiedLocalizedModule

scoped syntax:lead "(" ident noWs "⁻¹" term ")^#[" term "]" : term

scoped macro_rules
  | `(($𝒮⁻¹ $ℱ)^#[$_J]) =>
      `(CategoryTheory.Presheaf.SubmonoidPresheaf.sheafifiedLocalizedModule $𝒮 $ℱ)

end SheafifiedLocalizedModule

open scoped SheafifiedLocalizedModule

/- The source-facing notation is intentionally kept on the theorem surface. -/
#check
  (𝒮⁻¹ℱ)^#[J]

variable (𝒢 : ringedSiteModuleCategory J ((presheafToSheaf J CommRingCat).obj 𝒮.localizationPresheaf))

/-- The canonical localization morphism
`\mathcal F \to (\mathcal S^{-1}\mathcal F)^#`,
viewed on the source side by restriction of scalars along
`\mathcal O \to (\mathcal S^{-1}\mathcal O)^#[J]`. -/
noncomputable abbrev toSheafifiedLocalizedModule (ℱ : Mod(O)) :
    ℱ ⟶ (restrictionAlong 𝒮.toSheafifiedLocalizationPresheaf).obj ((𝒮⁻¹ℱ)^#[J]) :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (sameSiteStructureMap (J := J) (𝒮 := 𝒮))).unit.app ℱ

/-- Lemma 18.44.2 (2): every morphism from `\mathcal F` into an
`(\mathcal S^{-1}\mathcal O)^#[J]`-module `\mathcal G`, after restricting scalars along
`\mathcal O ⟶ (\mathcal S^{-1}\mathcal O)^#[J]`, factors uniquely through the canonical
localization morphism `\mathcal F \to (\mathcal S^{-1}\mathcal F)^#`. -/
theorem existsUnique_sheafifiedLocalizedModuleLift
    (η : ℱ ⟶ (restrictionAlong 𝒮.toSheafifiedLocalizationPresheaf).obj 𝒢) :
    ∃! γ : (𝒮⁻¹ℱ)^#[J] ⟶ 𝒢,
      toSheafifiedLocalizedModule 𝒮 ℱ ≫
          (restrictionAlong 𝒮.toSheafifiedLocalizationPresheaf).map γ =
        η := by
  let adj :=
    SheafOfModules.pullbackPushforwardAdjunction
      (sameSiteStructureMap (J := J) (𝒮 := 𝒮))
  let e := adj.homEquiv ℱ 𝒢
  refine ⟨e.symm η, ?_, ?_⟩
  · -- Proof comment: the defining property of the adjunction transpose is exactly the desired
    -- factorization through the unit map after rewriting the theorem statement into the
    -- adjunction Hom-equivalence normal form.
    change e (e.symm η) = η
    simpa using e.apply_symm_apply η
  · intro γ hγ
    -- Proof comment: a competing lift has the same transpose, so the Hom-equivalence forces it
    -- to equal the chosen transpose of `η`.
    change e γ = η at hγ
    exact ((Equiv.symm_apply_eq e).2 hγ.symm).symm

end CategoryTheory.Presheaf.SubmonoidPresheaf

end
