import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_44_1 (from Chap18) -/
open CategoryTheory Opposite
open scoped LocalizedPresheaf

noncomputable section

universe u v

namespace CategoryTheory
namespace Presheaf
namespace SubmonoidPresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.44.1:
- primary domain: localization of presheaves and sheaves of commutative rings on a Grothendieck
  site;
- sampled owner declarations:
  `CategoryTheory.Presheaf.SubmonoidPresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.localizationPresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf`,
  `CategoryTheory.Sheaf.PresheafOfModules.commRingSheafification`,
  `sheafificationAdjunction`;
- best owner abstraction: on the source-facing side, the public owner should be the
  submonoid-presheaf together with its localization presheaf and canonical map; on the sheaf side,
  the canonical owner is `PresheafOfModules.commRingSheafification`, with
  `sheafificationAdjunction` supplying the universal sheafification bridge;
- primitive data: a presheaf of commutative rings and a compatible multiplicative subset on each
  object of the site;
- derived API: the localization presheaf, the canonical map into it, and the sheafified universal
  property.

Source/core/bridge triage:
- `source-facing`: the site-level localization presheaf and the universal property of its
  sheafification;
- `core/canonical`: the owner pair `Presheaf.SubmonoidPresheaf.localizationPresheaf` and
  `Presheaf.SubmonoidPresheaf.toLocalizationPresheaf`, together with
  `PresheafOfModules.commRingSheafification` and `sheafificationAdjunction`;
- `bridge/view`: the canonical morphism from the given sheaf `𝒪` to the sheafification of
  `𝒮.localizationPresheaf`.

This file is therefore now purely the sheafification bridge: the presheaf-level owner lives in
`CategoryTheory.Presheaf.SubmonoidPresheaf`, and the declarations here extend that owner by the
sheafified canonical map and its universal property. -/

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒮 : SubmonoidPresheaf 𝒪.obj)

/-- The canonical morphism of sheaves of commutative rings from `𝒪` to the sheafification of
`𝒮⁻¹𝒪`. -/
noncomputable def toSheafifiedLocalizationPresheaf :
    𝒪 ⟶ PresheafOfModules.commRingSheafification J (𝒮⁻¹ 𝒪) :=
  (asIso ((sheafificationAdjunction J CommRingCat.{max u v}).counit.app 𝒪)).inv ≫
    (presheafToSheaf J CommRingCat.{max u v}).map 𝒮.toLocalizationPresheaf

/-- A morphism of sheaves of commutative rings sends the local sections of `𝒮` to units if every
chosen section becomes invertible after applying its component on each object of the site. -/
def SectionsMapToUnits {𝒜 : Sheaf J CommRingCat.{max u v}} (η : 𝒪 ⟶ 𝒜) : Prop :=
  ∀ ⦃U : Cᵒᵖ⦄ (s : 𝒮.obj U), IsUnit ((η.hom.app U).hom s.1)

-- Proof sketch: the canonical map `𝒪 ⟶ 𝒮⁻¹𝒪` inverts every section of `𝒮` objectwise; after
-- sheafification, the sheafification adjunction turns objectwise factorization through the
-- localization into a unique sheaf morphism from the sheafification of `𝒮⁻¹𝒪`.
/-- Lemma 18.44.1: the canonical morphism from `𝒪` to the sheafification of `𝒮⁻¹𝒪` sends every
local section of `𝒮` to a unit and is initial among morphisms of sheaves of commutative rings out
of `𝒪` that invert `𝒮`. -/
theorem sheafifiedLocalizationPresheaf_is_universal :
    𝒮.SectionsMapToUnits 𝒮.toSheafifiedLocalizationPresheaf ∧
      ∀ ⦃𝒜 : Sheaf J CommRingCat.{max u v}⦄ (η : 𝒪 ⟶ 𝒜),
        𝒮.SectionsMapToUnits η →
          ∃! γ : PresheafOfModules.commRingSheafification J (𝒮⁻¹ 𝒪) ⟶ 𝒜,
            𝒮.toSheafifiedLocalizationPresheaf ≫ γ = η := sorry

end SubmonoidPresheaf
end Presheaf
end CategoryTheory

/-! ### Lemma_18_44_2 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Presheaf
open SheafOfModules.RingedSite
open scoped LocalizedPresheaf

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}
variable (𝒮 : CategoryTheory.Presheaf.SubmonoidPresheaf O.obj)

/- Domain-style sampling for Lemma 18.44.2:
- primary domain: localization of sheaves of modules along a multiplicative subpresheaf of the
  structure sheaf on a fixed site;
- sampled owner declarations:
  `CategoryTheory.Presheaf.SubmonoidPresheaf`,
  `CategoryTheory.Presheaf.SubmonoidPresheaf.toSheafifiedLocalizationPresheaf`,
  `SheafOfModules.RingedSite.ringedSiteStructureMap`,
  `SheafOfModules.pullbackIso`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: the source-facing owner is the localized module presheaf and its
  sheafification over `(𝒮⁻¹𝒪)^#`, while the canonical bridge layer is the same-site pullback along
  `ringedSiteStructureMap 𝒮.toSheafifiedLocalizationPresheaf`;
- primitive data: a multiplicative subpresheaf
  `𝒮 : CategoryTheory.Presheaf.SubmonoidPresheaf O.obj` and an
  `O`-module sheaf `ℱ`;
- derived API: the localized module presheaf, its sheafification, the invertibility condition on
  targets over `(𝒮⁻¹𝒪)^#`, and the comparison/Hom-equivalence obtained from the canonical pullback
  owners.

Source/core/bridge triage:
- `source-facing`: the presheaf localization `𝒮⁻¹ℱ`, its sheafification, and the universal
  property against targets on which the sections of `𝒮` act invertibly;
- `core/canonical`: `SheafOfModules.pullbackIso` and
  `SheafOfModules.pullbackPushforwardAdjunction`;
- `bridge/view`: the public same-site `RingCat`-valued localization bridge
  `ringedSiteStructureMap 𝒮.toSheafifiedLocalizationPresheaf`.

This file therefore keeps the localization owner from Lemma 18.44.1 on the public surface and
uses the generic pullback/adjunction API only to express the canonical comparison and Hom-set
equivalence for that owner. -/

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The localization map `\mathcal O \to (\mathcal S^{-1}\mathcal O)^#` sends every distinguished
local section of `𝒮` to a unit. This is the invertibility hypothesis used in the module
localization universal property. -/
theorem toSheafifiedLocalizationPresheaf_sectionsMapToUnits :
    𝒮.SectionsMapToUnits 𝒮.toSheafifiedLocalizationPresheaf :=
  𝒮.sheafifiedLocalizationPresheaf_is_universal.1

variable [(PresheafOfModules.pushforward
  (ringedSiteStructureMap
    𝒮.toSheafifiedLocalizationPresheaf).hom).IsRightAdjoint]
variable [(SheafOfModules.pushforward
  (ringedSiteStructureMap
    𝒮.toSheafifiedLocalizationPresheaf)).IsRightAdjoint]

/- Lemma 18.44.2 (1), owner form: the sheafified localization `(𝒮⁻¹ℱ)^#` is canonically
identified with the same-site pullback of `ℱ` along
`\mathcal O \to (\mathcal S^{-1}\mathcal O)^#`. -/
recall SheafOfModules.pullbackIso

/- Lemma 18.44.2 (1): for an `O`-module sheaf `ℱ`, the source-facing sheafification
`(𝒮⁻¹ℱ)^#` is the canonical sheaf pullback of `ℱ` along the localization map from
Lemma `18.44.1`. -/
#check
  (fun (ℱ : SheafOfModules (ringSheaf J O)) ↦
    ((SheafOfModules.pullbackIso
      (ringedSiteStructureMap
        𝒮.toSheafifiedLocalizationPresheaf)).app ℱ).symm)

/- Lemma 18.44.2 (2), owner form: the universal property is the Hom-set equivalence induced by
the comparison above and the canonical pullback/pushforward adjunction for the localization map. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 18.44.2 (2): for a module sheaf `𝒢` over the sheafification of `𝒮⁻¹𝒪`, morphisms from
the sheafification of `𝒮⁻¹ℱ` to `𝒢` are canonically equivalent to `O`-linear morphisms from `ℱ`
to `𝒢` viewed by restriction of scalars along `\mathcal O \to (\mathcal S^{-1}\mathcal O)^#`; by
`toSheafifiedLocalizationPresheaf_sectionsMapToUnits`, this is exactly the source-facing universal
property for targets on which the sections of `𝒮` act invertibly. -/
#check
  (fun (ℱ : SheafOfModules (ringSheaf J O))
      (𝒢 : SheafOfModules
        (ringSheaf J (PresheafOfModules.commRingSheafification J (𝒮⁻¹ O)))) ↦
    (((SheafOfModules.pullbackIso
      (ringedSiteStructureMap
        𝒮.toSheafifiedLocalizationPresheaf)).app ℱ).symm.homCongr
      (Iso.refl 𝒢)).trans
    ((SheafOfModules.pullbackPushforwardAdjunction
      (ringedSiteStructureMap
        𝒮.toSheafifiedLocalizationPresheaf)).homEquiv ℱ 𝒢))

end
