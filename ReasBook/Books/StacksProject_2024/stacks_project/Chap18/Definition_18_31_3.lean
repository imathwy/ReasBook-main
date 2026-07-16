import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open RingedSite.Hom
open SheafOfModules.RingedSite
open scoped RingedSite.Hom

noncomputable section

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JC.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'
local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory JC 𝒪

/- Domain-style sampling for Definition 18.31.3:
- primary domain: relative flatness of a sheaf of modules along a morphism of commutative ringed
  sites, expressed by restricting scalars along the inverse-image structure-sheaf map;
- sampled owner declarations:
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom.(·⁻¹𝒪)`,
  `RingedSite.Hom.(^♯)`,
  `SheafOfModules.RingedSite.IsFlat`,
  `restrictionAlong`;
- best owner abstraction: `SheafOfModules.RingedSite.IsFlat`; this numbered item is only the
  source-language specialization of that owner to the restricted module
  `((restrictionAlong (f^♯)).obj ℱ)`, so it is a bridge/view item, not a second owner;
- primitive data: the morphism `f : X ⟶ Y` and the `\mathcal O_X`-module `ℱ`;
- derived API: the inverse-image commutative structure sheaf `f⁻¹𝒪`, the map `f^♯`, and the
  restricted module over `f^{-1}\mathcal O_Y`.

Source/core/bridge triage:
- `source-facing`: the statement that `ℱ` is flat over `Y`;
- `core/canonical`: `IsFlat ((restrictionAlong (f^♯)).obj ℱ)`;
- `bridge/view`: this file, which should expose that canonical expression directly rather than
  keep a parallel alias.
-/

variable (f : X ⟶ Y) (ℱ : Mod(𝒪))

/- Definition 18.31.3: for a morphism of ringed sites `f : X ⟶ Y`, an `\mathcal O_X`-module
`\mathcal F` is flat over `Y` exactly when the restricted module over `f^{-1}\mathcal O_Y`,
obtained via `f^♯`, is flat in the canonical owner
`SheafOfModules.RingedSite.IsFlat`. -/
#check (IsFlat ((restrictionAlong (f^♯)).obj ℱ))

end SheafOfModules
