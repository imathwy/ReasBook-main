import StacksProject_2024.Chap21.Lemma_21_20_7_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite.Hom
open scoped RingedSite.Hom

noncomputable section

universe u

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD]
variable (𝒪D : Sheaf JD RingCat.{u})

/-- The inverse-image ring sheaf `g⁻¹ 𝒪D` on `C`. -/
abbrev inverseImageRingSheaf
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{u}) :
    Sheaf JC RingCat.{u} :=
  (u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D

/-- The inverse-image ringed-site morphism
`g : (C, g⁻¹ 𝒪D) ⟶ (D, 𝒪D)`. -/
abbrev moduleInverseImageHom
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
  (𝒪D : Sheaf JD RingCat.{u}) :
    RingedSite.ofRingSheaf JD 𝒪D ⟶
      RingedSite.ofRingSheaf JC (inverseImageRingSheaf JC JD u 𝒪D) where
  base := u
  isMorphismOfSites := by
    sorry
  structureSheafMap := 𝟙 (inverseImageRingSheaf JC JD u 𝒪D)

@[simp] theorem moduleInverseImageHom_base
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{u}) :
    (moduleInverseImageHom JC JD u 𝒪D).base = u :=
  rfl

@[simp] theorem moduleInverseImageHom_structureSheafMap
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{u}) :
    (moduleInverseImageHom JC JD u 𝒪D).structureSheafMap = 𝟙 (inverseImageRingSheaf JC JD u 𝒪D) :=
  rfl

end

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [HasExt (Sheaf JC AddCommGrpCat.{u})]
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable (𝒪D : Sheaf JD RingCat.{u})

local notation "𝒪C" => inverseImageRingSheaf JC JD u 𝒪D
local notation "g^*" =>
  SheafOfModules.pushforward
    (RingedSite.Hom.structureSheafMap (moduleInverseImageHom JC JD u 𝒪D))

/- Domain-style sampling:
- primary domain: inverse image on sheaves of modules over a morphism of sites, with the
  acyclicity conclusion expressed on the canonical cohomology owner `F.H' p U`;
- sampled owner declarations:
  `inverseImageRingSheaf`,
  `moduleInverseImageHom`,
  `RingedSite.Hom.(^*)`,
  `SheafOfModules.toSheaf`,
  `Sheaf.H'`,
  `sheafPushforwardContinuous_cohomologyAtObject_isomorphic`,
  `higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings`,
  `ringedSiteModuleCechCohomology_isZero_of_injective_succ`;
- best owner abstraction:
  `source-facing`: Lemma `21.37.1`, asserting vanishing of higher cohomology of `g^{-1} ℐ`;
  `core/canonical`: the ringed-site morphism `g = moduleInverseImageHom JC JD u 𝒪D`, its
    inverse-image owner `g^*`, the underlying abelian-sheaf owner `SheafOfModules.toSheaf 𝒪C`,
    and the cohomology owner `F.H' p U`;
  `bridge/view`: the internal construction of `g` from the identity map on the inverse-image ring
    sheaf, used only to expose the canonical inverse-image owner `g^*`.
- primitive data: the continuous and cocontinuous functor `u`, the ring sheaf `𝒪D`, the
  injective module `ℐ`, and the object `U`;
- derived API: vanishing of `H^p(U, g^{-1} ℐ)` for `p > 0`. -/

-- Proof sketch: for each covering family of `U`, continuity sends it to a covering family of
-- `u.obj U`, and cocontinuity identifies the iterated fibre products so that the Čech complexes
-- for `g⁻¹ ℐ` on `C` and for `ℐ` on `D` agree. Lemma `21.12.3` gives vanishing of the positive
-- Čech cohomology of `ℐ`, and Lemma `21.10.9` upgrades this to vanishing of the higher cohomology
-- groups over `U`.
/-- Lemma 21.37.1: if `u : C ⥤ D` is continuous and cocontinuous, `𝒪D` is a sheaf of rings on
`D`, and `ℐ` is an injective `𝒪D`-module, then the inverse image `g⁻¹ ℐ`, formalized by the
canonical inverse-image owner `g^*` and viewed as an abelian sheaf through
`SheafOfModules.toSheaf 𝒪C`, has vanishing higher cohomology over every object `U : C`. -/
@[stacks 0D6X]
theorem higherCohomology_isZero_moduleInverseImage_of_injective
    (ℐ : SheafOfModules 𝒪D) (hℐ : Injective ℐ)
    (U : C) (p : ℕ) (hp : 0 < p) :
    IsZero
      (((SheafOfModules.toSheaf 𝒪C).obj ((g^*).obj ℐ)).H' p U) := sorry

end

end CategoryTheory
