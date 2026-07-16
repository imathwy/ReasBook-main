import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_23_3

open AlgebraicGeometry
open CategoryTheory
open Opposite TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- The morphism from the target unit module to the pullback of `ℱ` induced by a global section of
that pullback. -/
abbrev pullbackSectionMap
    (α : 𝒪 ⟶ 𝒪') (ℱ : Mod(𝒪))
    [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]
    (s : ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ).sections) :
    unitModule J 𝒪' ⟶ (SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ :=
  ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ).unitHomEquiv.symm s

/-- A section of the pullback of `ℱ` along `α` is regular when its induced unit-module morphism
is a monomorphism. -/
abbrev IsRegularSection
    (α : 𝒪 ⟶ 𝒪') (ℱ : Mod(𝒪))
    [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]
    (s : ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ).sections) : Prop :=
  Mono (pullbackSectionMap α ℱ s)

/-- Companion to `SheafOfModules.RingedSite.IsRegularSection`: unfolding the owner gives the mono
condition on the induced unit-module morphism. -/
theorem isRegularSection_iff_mono
    (α : 𝒪 ⟶ 𝒪') (ℱ : Mod(𝒪))
    [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]
    (s : ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj ℱ).sections) :
    IsRegularSection α ℱ s ↔ Mono (pullbackSectionMap α ℱ s) :=
  Iff.rfl

end SheafOfModules.RingedSite

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

local notation "JX" => Opens.grothendieckTopology X.toTopCat
local notation "ModX" => ringedSiteModuleCategory JX X.𝒪
local notation "MerModX" => ringedSiteModuleCategory JX (meromorphicFunctionSheaf X)
local notation "KX" => (unitModule JX (meromorphicFunctionSheaf X) : MerModX)

-- Semantic recall: Definition 31.23.7 is a source-facing meromorphic specialization of the
-- regular-section mono condition from Definition 31.14.6. The induced morphism
-- `\mathcal K_X ⟶ \mathcal K_X(\mathcal L)` is named explicitly for downstream reuse.

/-- The morphism `\mathcal K_X \to \mathcal K_X(\mathcal F)` induced by a meromorphic section of
`\mathcal F`. -/
abbrev meromorphicSectionMap
    (ℱ : ModX) (s : X.meromorphicSections ℱ) :
    KX ⟶ X.meromorphicSectionSheaf ℱ :=
  SheafOfModules.RingedSite.pullbackSectionMap X.toMeromorphicFunctionSheafHom ℱ s

/-- Definition 31.23.7: for a locally ringed space `X`, a meromorphic section `s` is regular if
the induced map `\mathcal K_X \to \mathcal K_X(\mathcal F)` is injective. In the source this is
applied to an invertible `\mathcal O_X`-module `\mathcal L`; the owner is stated for arbitrary
`\mathcal O_X`-modules because the defining mono condition depends only on the induced morphism.
This is the meromorphic analogue of the mono condition defining regular sections in
Definition 31.14.6. -/
@[stacks 02OX]
abbrev IsRegularMeromorphicSection (ℱ : ModX) (s : X.meromorphicSections ℱ) : Prop :=
  SheafOfModules.RingedSite.IsRegularSection X.toMeromorphicFunctionSheafHom ℱ s

/-- Companion to Definition 31.23.7: a meromorphic section is regular exactly when the induced
morphism `\mathcal K_X \to \mathcal K_X(\mathcal L)` is a monomorphism. -/
theorem isRegularMeromorphicSection_iff_mono (ℱ : ModX) (s : X.meromorphicSections ℱ) :
    IsRegularMeromorphicSection X ℱ s ↔ Mono (X.meromorphicSectionMap ℱ s) :=
  SheafOfModules.RingedSite.isRegularSection_iff_mono X.toMeromorphicFunctionSheafHom ℱ s

end AlgebraicGeometry.LocallyRingedSpace
