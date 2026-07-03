import Mathlib
import StacksProject_2024.Chap18.Definition_18_31_3
import StacksProject_2024.Chap18.Definition_18_40_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {E : Type u} [Category.{u} E]
variable {JC : GrothendieckTopology C}
variable {JD : GrothendieckTopology D}
variable {JE : GrothendieckTopology E}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JE.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JD CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪X : Sheaf JC CommRingCat.{u}}
variable {𝒪Y : Sheaf JD CommRingCat.{u}}
variable {𝒪Z : Sheaf JE CommRingCat.{u}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪X
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪Y
local notation "Z" => RingedSite.ofCommRingSheaf JE 𝒪Z

local instance instBaseIsContinuousLemma184010 {A B : RingedSite.{u, u}} (f : A ⟶ B) :
    Functor.IsContinuous f.base B.siteTopology A.siteTopology :=
  f.isMorphismOfSites.toIsContinuous

/- Domain-style sampling for Lemma 18.40.10:
- primary domain: composition of site-presented morphisms of locally ringed topoi;
- sampled owner declarations:
  `RingedSite.Hom.comp`,
  `RingedSite.Hom.inverseImageStructureSheafMap`,
  `CategoryTheory.IsMorphismOfLocallyRingedTopoi`,
  `CategoryTheory.isMorphismOfLocallyRingedTopoi_iff`;
- best owner abstraction: the bundled source-facing morphism owner `RingedSite.Hom`;
- primitive data: the bundled ringed-site morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the inverse-image structure-sheaf maps
  `inverseImageStructureSheafMap f`,
  `inverseImageStructureSheafMap g`, and
  `inverseImageStructureSheafMap (f ≫ g)`, together with the Chapter 18 class
  `CategoryTheory.IsMorphismOfLocallyRingedTopoi`; the needed sheaf-pushforward right adjoints are
  canonical derived instances from continuity and `HasWeakSheafify`, not primitive theorem data.

Source/core/bridge triage:
- `source-facing`: the closure statement that the composite of two morphisms of locally ringed
  topoi is again such a morphism;
- `core/canonical`: `CategoryTheory.IsMorphismOfLocallyRingedTopoi`;
- `bridge/view`: `RingedSite.Hom.inverseImageStructureSheafMap`, converting the bundled ringed-site
  morphism to the inverse-image form expected by the canonical owner.

Accordingly, this file should not introduce a second owner such as `CommRingedToposIn` or
`CommRingedToposMorphismIn`; the textbook statement lives directly on `RingedSite.Hom.comp`. -/

variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsLocallyRingedSite 𝒪X]
variable [IsLocallyRingedSite 𝒪Y]
variable [IsLocallyRingedSite 𝒪Z]
variable [IsMorphismOfLocallyRingedTopoi
  f.base 𝒪X 𝒪Y (inverseImageStructureSheafMap f)]
variable [IsMorphismOfLocallyRingedTopoi
  g.base 𝒪Y 𝒪Z (inverseImageStructureSheafMap g)]

-- Proof sketch: by Definition `18.40.9`, the locally ringed condition is the cartesianness of the
-- inverse-image units square. That condition is stable under composition because pullback along the
-- composite inverse-image functor is the composite of the pullbacks for `f` and `g`, and the
-- cartesian-units squares compose.
/-- Lemma 18.40.10: the composite of two morphisms of locally ringed topoi is again a morphism of
locally ringed topoi. -/
@[instance]
theorem isMorphismOfLocallyRingedTopoi_comp :
    IsMorphismOfLocallyRingedTopoi
      (f ≫ g).base 𝒪X 𝒪Z (inverseImageStructureSheafMap (f ≫ g)) := sorry

end

end RingedSite.Hom
