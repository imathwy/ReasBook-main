import Mathlib
import StacksProject_2024.Chap18.Definition_18_31_3
import StacksProject_2024.Chap18.Definition_18_35_1
import StacksProject_2024.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom

section

variable {C : Type u} [SmallCategory C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf JC CommRingCat.{u})]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (f : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪')

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

local instance (f : X ⟶ Y) : Functor.IsContinuous f.base JD JC :=
  f.isMorphismOfSites.toIsContinuous

/- Domain-style sampling for Definition 18.35.4:
- primary domain: naive cotangent complexes of site-presented morphisms of ringed topoi;
- sampled owner declarations:
  `RingedSite.Hom`,
  `RingedSite.Hom.inverseImageStructureSheafMap`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`;
- best owner abstraction: the source-facing owner is the bundled morphism of ringed sites
  `f : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪'`; the inverse-image
  structure-sheaf map is derived data via `inverseImageStructureSheafMap f`, and the naive
  cotangent complex is the Chapter 18 site-level owner `naiveCotangent` applied to that
  inverse-image map;
- primitive data: the bundled morphism `f`;
- derived API: the inverse-image structure-sheaf map, the induced `Under` object
  `Under.mk (inverseImageStructureSheafMap f)`, and the resulting two-term complex concentrated in
  degrees `-1` and `0`.

Source/core/bridge triage:
- `source-facing`: `RingedSite.Hom.naiveCotangentComplex`, written as `NL(f)`;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`;
- `bridge/view`: `inverseImageStructureSheafMap f`, converting the bundled ringed-site morphism to
  the sheaf morphism to which the site-level naive cotangent owner applies.

This item should therefore be organized around the bundled owner `RingedSite.Hom`, not around the
raw site data `(f.base, 𝒪, 𝒪', fSharp)`. -/

private abbrev sourceSheaf (f : X ⟶ Y) :
    Sheaf JC CommRingCat.{u} :=
  (f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪'

private abbrev sourceUnder (f : X ⟶ Y) :
    Under ((f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪') :=
  Under.mk (inverseImageStructureSheafMap f)

/-- Definition 18.35.4: for a bundled morphism of ringed sites
`f : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪'` presenting a morphism of
ringed topoi, the naive cotangent complex `NL_f` is the site-level naive cotangent complex
`NL_{\mathcal O_X / f^{-1}\mathcal O_Y}` from Definition `18.35.1`, specialized along the
inverse-image structure-sheaf map `f^{-1}\mathcal O_Y ⟶ \mathcal O_X`. -/
abbrev naiveCotangentComplex :
    CochainComplex (ringedSiteModuleCategory JC 𝒪) ℤ :=
  naiveCotangent (sourceSheaf f) (sourceUnder f)

end

/- Source-facing notation for the naive cotangent complex of a morphism of ringed sites. -/
scoped syntax:max "NL(" term ")" : term

scoped macro_rules
  | `(NL($f)) => `(RingedSite.Hom.naiveCotangentComplex $f)

open scoped RingedSite.Hom

section

variable {C : Type u} [SmallCategory C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf JC CommRingCat.{u})]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
variable (f : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪')

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

local instance (f : X ⟶ Y) : Functor.IsContinuous f.base JD JC :=
  f.isMorphismOfSites.toIsContinuous

/-- The naive cotangent complex of `f` is the Chapter 18 site-level owner applied to the
inverse-image structure-sheaf morphism `f^{-1}\mathcal O_Y ⟶ \mathcal O_X`. -/
theorem naiveCotangentComplex_def :
    NL(f) =
      naiveCotangent
        ((f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪')
        (Under.mk (inverseImageStructureSheafMap f)) :=
  rfl

end

end RingedSite.Hom
