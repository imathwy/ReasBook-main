import Mathlib
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.«18_44_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

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
