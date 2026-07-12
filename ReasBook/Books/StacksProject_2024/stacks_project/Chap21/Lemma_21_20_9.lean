import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Functor
import StacksProject_2024.Chap21.SheafModuleDerivedTensor
import StacksProject_2024.Chap21.Lemma_21_20_1_Owner

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped SheafModuleDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)
variable [HasSheafify (J.over U) AddCommGrpCat.{u}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "ModU" => ringedSiteModuleCategory (J.over U) (𝒪.over U)
local notation "DMod" => DerivedCategory Mod
local notation "DModU" => DerivedCategory ModU

/-- Helper for Lemma 21.20.9: the derived localized lower-shriek functor on the slice site. -/
private noncomputable def localizedLowerShriekDerived : DModU ⥤ DMod :=
  (ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory

local notation "LjD" => localizedLowerShriekDerived J 𝒪 U

/- Domain-style sampling for Lemma 21.20.9:
- primary domain: tensor compatibility for the derived localized lower shriek on the slice site
  `(C / U, J.over U)`;
- sampled owner declarations:
  `ringedSiteLocalizedLowerShriek`,
  `CategoryTheory.Functor.mapDerivedCategory`,
  `Functor.Monoidal`,
  `Functor.Monoidal.μIso`;
- best owner abstraction:
  `source-facing`: the localized tensor comparison for the derived localized lower shriek;
  `core/canonical`: the exact derived owner
  `(ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory`;
  `bridge/view`: the monoidal comparison `Functor.Monoidal.μIso` for that exact derived functor,
  written below with the source-facing tensor surface `⊗^L`.

Source/core/bridge triage:
- `source-facing`: the comparison
  `Lj_{U!}(K ⊗^L L) ≅ Lj_{U!} K ⊗^L Lj_{U!} L`;
- `core/canonical`: `Functor.mapDerivedCategory` on the exact localized lower shriek;
- `bridge/view`: `Functor.Monoidal.μIso` together with the scoped derived-tensor notation
  `SheafModuleDerivedTensor`.
-/

variable [CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [CategoryWithHomology (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [HasCountableCoproducts (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory J 𝒪))]
variable [MonoidalCategory (DerivedCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U)))]

/-- Lemma 21.20.9: for `K`, `L : D(ModU)`, the derived localized lower shriek carries
`K ⊗^L L` to the tensor product of the localized lower shrieks of `K` and `L`. This is the
source-facing `IsIsomorphic` form of the canonical monoidal comparison supplied by
`Functor.Monoidal.μIso` for `(ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory`. -/
@[stacks 0GL1]
theorem ringedSiteLocalizedLowerShriek_derivedTensor_isomorphic
    [hLjAdditive : (ringedSiteLocalizedLowerShriek J 𝒪 U).Additive]
    [Functor.Monoidal LjD] (K L : DModU) :
    IsIsomorphic
      ((LjD).obj (K ⊗^L L))
      (((LjD).obj K) ⊗^L ((LjD).obj L)) := by
  -- The source-facing comparison is exactly the monoidal structure isomorphism on the derived
  -- localized lower shriek.
  exact ⟨(Functor.Monoidal.μIso LjD K L).symm⟩

end

end SheafOfModules.RingedSite
