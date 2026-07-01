import Mathlib
import stacks_project.Chap18.Definition_18_23_1
import stacks_project.Chap18.Lemma_18_19_2
import stacks_project.Chap21.Lemma_21_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite

noncomputable section

universe v u

set_option quotPrecheck false in
local notation:20 X " ⟹ " Y:19 => (ihom X).obj Y

/- Domain-style sampling for Lemma 18.27.6:
- primary domain: tensor-internal-Hom adjunctions in braided monoidal closed categories;
- inspected owner declarations:
  `CategoryTheory.ihom`,
  `MonoidalClosed.curry`,
  `MonoidalClosed.uncurry`,
  `MonoidalClosed.internalHomAdjunction₂.homEquiv`,
  `ringedSiteModuleCategory`;
- best owner abstraction:
  the canonical owner is mathlib's internal-Hom adjunction with internal-Hom object
  `𝒢 ⟹ ℋ`, and the Stacks source orientation `Hom(ℱ ⊗ 𝒢, ℋ) ≃ Hom(ℱ, Hom(𝒢, ℋ))`
  is obtained by transporting that owner along the braiding;
- primitive data:
  objects `ℱ 𝒢 ℋ` in a braided monoidal closed category;
- derived API:
  the source-oriented Hom-set equivalence itself, together with its presheaf and ringed-site
  specializations.

Source/core/bridge triage:
- `source-facing`: the source-oriented equivalence
  `(ℱ ⊗ 𝒢 ⟶ ℋ) ≃ (ℱ ⟶ (𝒢 ⟹ ℋ))`;
- `core/canonical`: `MonoidalClosed.internalHomAdjunction₂.homEquiv`, equivalently
  `MonoidalClosed.curry` / `MonoidalClosed.uncurry`;
- `bridge/view`: transport across the braiding isomorphism
  `β_ ℱ 𝒢 : ℱ ⊗ 𝒢 ≅ 𝒢 ⊗ ℱ`.
-/

section Generic

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
variable [MonoidalClosed A]
variable (ℱ 𝒢 ℋ : A)

/- Lemma 18.27.6: the textbook bijection
`Hom(ℱ ⊗ 𝒢, ℋ) ≃ Hom(ℱ, Hom(𝒢, ℋ))`
is the canonical internal-Hom adjunction, transported from the owner orientation
`Hom(𝒢 ⊗ ℱ, ℋ) ≃ Hom(ℱ, Hom(𝒢, ℋ))` along the braiding. -/
#check
  (show (ℱ ⊗ 𝒢 ⟶ ℋ) ≃ (ℱ ⟶ (𝒢 ⟹ ℋ)) from
    ((β_ ℱ 𝒢).homCongr (Iso.refl ℋ)).trans
      ((MonoidalClosed.internalHomAdjunction₂.homEquiv :
        (𝒢 ⊗ ℱ ⟶ ℋ) ≃ (ℱ ⟶ (𝒢 ⟹ ℋ)))))

end Generic

section PresheafModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [BraidedCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (ℱ 𝒢 ℋ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

/- Presheaf-module specialization of Lemma 18.27.6. -/
#check
  (show (ℱ ⊗ 𝒢 ⟶ ℋ) ≃
      (ℱ ⟶ (𝒢 ⟹ ℋ)) from
    ((β_ ℱ 𝒢).homCongr (Iso.refl ℋ)).trans
      ((MonoidalClosed.internalHomAdjunction₂.homEquiv :
        (𝒢 ⊗ ℱ ⟶ ℋ) ≃
          (ℱ ⟶ (𝒢 ⟹ ℋ)))))

end PresheafModules

section RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [MonoidalCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [BraidedCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (_root_.ringedSiteModuleCategory J 𝒪)]
variable (ℱ 𝒢 ℋ : _root_.ringedSiteModuleCategory J 𝒪)

/- Ringed-site-module specialization of Lemma 18.27.6. -/
#check
  (show (ℱ ⊗ 𝒢 ⟶ ℋ) ≃
      (ℱ ⟶ (𝒢 ⟹ ℋ)) from
    ((β_ ℱ 𝒢).homCongr (Iso.refl ℋ)).trans
      ((MonoidalClosed.internalHomAdjunction₂.homEquiv :
        (𝒢 ⊗ ℱ ⟶ ℋ) ≃
          (ℱ ⟶ (𝒢 ⟹ ℋ)))))

end RingedSite
