import Mathlib
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

/- Domain-style sampling for Definition 18.31.3:
- primary domain: relative flatness of a sheaf of modules along a morphism of ringed sites,
  expressed by restricting scalars along the inverse-image structure-sheaf map;
- sampled owner declarations:
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.restrictScalars`,
  `SheafOfModules.flat_over` from `Definition_17_20_3`;
- best owner abstraction: the source-facing owner should be the bundled morphism
  `f : RingedSite.Hom X Y`, where `X := RingedSite.ofCommRingSheaf JC 𝒪` and
  `Y := RingedSite.ofCommRingSheaf JD 𝒪'`; the inverse-image structure-sheaf map is only a thin
  bridge needed to restrict scalars;
- primitive data: the bundled ringed-site morphism `f : X ⟶ Y` and the `\mathcal O`-module `ℱ`;
- derived API: the inverse-image commutative structure-sheaf map of `f` and the relative
  flatness predicate `flatOver`.

Source/core/bridge triage:
- `source-facing`: the relative flatness predicate `flatOver f ℱ`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat` for a sheaf of modules over a fixed
  structure sheaf;
- `bridge/view`: the inverse-image structure-sheaf map
  `inverseImageStructureSheafMap f` and the resulting restricted module
  `((SheafOfModules.restrictScalars
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).map
        (inverseImageStructureSheafMap f))).obj ℱ)`,
  viewed as a module over `f^{-1}\mathcal O'`.
-/

local instance base_isContinuous (f : X ⟶ Y) : Functor.IsContinuous f.base JD JC :=
  f.isMorphismOfSites.toIsContinuous

private abbrev pushforwardCommRingMap
    (f : X ⟶ Y) :
    𝒪' ⟶ (f.base.sheafPushforwardContinuous CommRingCat.{u} JD JC).obj 𝒪 :=
  Functor.preimage (sheafCompose JD (forget₂ CommRingCat RingCat))
    (show ringSheaf JD 𝒪' ⟶
        ringSheaf JD ((f.base.sheafPushforwardContinuous CommRingCat.{u} JD JC).obj 𝒪) from
      f.structureSheafMap)

/-- The inverse-image form `f^{-1}\mathcal O_Y \to \mathcal O_X` of the structure-sheaf map of a
bundled morphism of ringed sites `f : X ⟶ Y`, in the commutative setting
`X = RingedSite.ofCommRingSheaf JC 𝒪` and `Y = RingedSite.ofCommRingSheaf JD 𝒪'`. -/
abbrev inverseImageStructureSheafMap
    (f : X ⟶ Y) :
    (f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪' ⟶ 𝒪 :=
  ((f.base.sheafAdjunctionContinuous CommRingCat.{u} JD JC).homEquiv _ _).symm
    (pushforwardCommRingMap f)

/-- Definition 18.31.3: for a morphism of ringed sites `f : X ⟶ Y`, an `\mathcal O_X`-module
`\mathcal F` is flat over `Y` when, after restricting scalars along the inverse-image
structure-sheaf map `f^{-1}\mathcal O_Y \to \mathcal O_X`, it is a flat
`f^{-1}\mathcal O_Y`-module. -/
abbrev flatOver
    (f : X ⟶ Y) (ℱ : ringedSiteModuleCategory JC 𝒪) : Prop :=
  IsFlat ((f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪')
    ((SheafOfModules.restrictScalars
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).map
        (inverseImageStructureSheafMap f))).obj ℱ)

end RingedSite.Hom
