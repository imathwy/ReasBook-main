import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import StacksProject_2024.Chap34.Definition_34_5_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
- `lean_leansearch` was attempted for the smooth-site owner/API but was unavailable due to HTTP
  429 rate limiting. The current file therefore follows the verified local analogue
  `Definition_34_6_8`, using the canonical owner `Scheme.overGrothendieckTopology` on `Over S`
  together with the canonical smooth morphism property `Smooth`, the affine full subcategory
  `ObjectProperty.FullSubcategory`, the Chapter 34 source-facing owner `StandardSmoothCovering`
  for affine standard smooth coverings, and the canonical `Pretopology`/`GrothendieckTopology`
  owners for the affine-site coverage data.
-/

/-- Definition 34.5.8 (1): the big smooth site of a scheme `S` is the canonical smooth
Grothendieck topology on the over category `Over S`. -/
abbrev bigSmoothSite (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  S.overGrothendieckTopology @Smooth

/-- The big smooth site is exactly the smooth Grothendieck topology on `Over S`. -/
theorem bigSmoothSite_def (S : Scheme.{u}) :
    bigSmoothSite S = S.overGrothendieckTopology @Smooth :=
  rfl

/-- Definition 34.5.8 (2): the big affine smooth site of `S` is the full subcategory of `Over S`
whose objects have affine underlying source scheme. -/
abbrev bigAffineSmoothSite (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun U : Over S ↦ IsAffine U.left)

/-- Every object of the big affine smooth site has affine underlying scheme. -/
instance bigAffineSmoothSite.instIsAffineObj {S : Scheme.{u}} (U : bigAffineSmoothSite S) :
    IsAffine U.obj.left :=
  U.property

/-- The covering families of the big affine smooth site are the standard smooth coverings of the
underlying affine target scheme. -/
abbrev bigAffineSmoothCovering {S : Scheme.{u}} (U : bigAffineSmoothSite S) :=
  StandardSmoothCovering U.obj.left

/-- A covering family in the big affine smooth site is a smooth covering family of the underlying
affine target in the Chapter 34 fixed-target owner. -/
theorem bigAffineSmoothCovering_smoothCovering
    {S : Scheme.{u}} {U : bigAffineSmoothSite S} (𝒰 : bigAffineSmoothCovering U) :
    Scheme.SmoothCovering (𝒰.toOverFamily.obj) :=
  𝒰.smoothCovering

/-- A covering family in the big affine smooth site covers the underlying affine target. -/
theorem bigAffineSmoothCovering_iUnion_range_eq_univ
    {S : Scheme.{u}} {U : bigAffineSmoothSite S} (𝒰 : bigAffineSmoothCovering U) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ :=
  𝒰.iUnion_range_eq_univ

/-- The `j`-th member of a standard smooth covering of an affine `S`-scheme, viewed as an object
of the big affine smooth site over `S`. -/
def StandardSmoothCovering.siteObj {S : Scheme.{u}} {U : bigAffineSmoothSite S}
    (𝒰 : bigAffineSmoothCovering U) (j : Fin 𝒰.n) : bigAffineSmoothSite S where
  obj := Over.mk (𝒰.map j ≫ U.obj.hom)
  property := 𝒰.isAffine j

/-- The `j`-th arrow of a standard smooth covering, viewed in the affine over-site of `S`. -/
def StandardSmoothCovering.siteMap {S : Scheme.{u}} {U : bigAffineSmoothSite S}
    (𝒰 : bigAffineSmoothCovering U) :
    ∀ j : Fin 𝒰.n, StandardSmoothCovering.siteObj 𝒰 j ⟶ U :=
  fun j ↦
    ObjectProperty.homMk <|
      Over.homMk (𝒰.map j) (by rfl)

/-- A presieve on the big affine smooth site is covering when it is presented by a standard smooth
covering of the underlying affine target scheme. -/
def bigAffineSmoothPresieveCovering {S : Scheme.{u}} {U : bigAffineSmoothSite S}
    (R : Presieve U) : Prop :=
  ∃ 𝒰 : bigAffineSmoothCovering U,
    R =
      Presieve.ofArrows
        (StandardSmoothCovering.siteObj 𝒰)
        (StandardSmoothCovering.siteMap 𝒰)

/-- A standard smooth covering presents a covering presieve on the big affine smooth site. -/
theorem bigAffineSmoothPresieveCovering_of_standardCover
    {S : Scheme.{u}} {U : bigAffineSmoothSite S} (𝒰 : bigAffineSmoothCovering U) :
    bigAffineSmoothPresieveCovering
      (Presieve.ofArrows
        (StandardSmoothCovering.siteObj 𝒰)
        (StandardSmoothCovering.siteMap 𝒰)) :=
  ⟨𝒰, rfl⟩

/-- Affine objects in `Over S` are closed under isomorphisms. -/
instance bigAffineSmoothSite_isClosedUnderIsomorphisms (S : Scheme.{u}) :
    IsClosedUnderIsomorphisms (fun X : Over S ↦ IsAffine X.left) where
  of_iso := by
    intro X Y e hX
    exact (IsAffine.iff_of_isIso e.hom.left).mp hX

/-- Affine objects in `Over S` are closed under pullbacks. -/
instance bigAffineSmoothSite_isClosedUnderLimitsOfShape_walkingCospan (S : Scheme.{u}) :
    IsClosedUnderLimitsOfShape
      (fun X : Over S ↦ IsAffine X.left) WalkingCospan := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  let X := F.obj WalkingCospan.left
  let Y := F.obj WalkingCospan.right
  let Z := F.obj WalkingCospan.one
  let f : X ⟶ Z := F.map WalkingCospan.Hom.inl
  let g : Y ⟶ Z := F.map WalkingCospan.Hom.inr
  let e := HasLimit.isoOfNatIso (diagramIsoCospan F)
  let epb := PreservesPullback.iso (Over.forget S) f g
  have hpull : IsAffine (limit (cospan f g)).left := by
    exact
      (IsAffine.iff_of_isIso epb.hom).mpr
        (Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine f.left g.left)
  exact
    (IsAffine.iff_of_isIso e.hom.left).mpr hpull

/-- The big affine smooth site has pullbacks. -/
instance bigAffineSmoothSite_hasPullbacks (S : Scheme.{u}) :
    HasPullbacks (bigAffineSmoothSite S) :=
  CategoryTheory.Limits.hasLimitsOfShape_of_closedUnderLimits
    WalkingCospan
    (fun X : Over S ↦ IsAffine X.left)

/-- Singleton isomorphisms are covering families in the big affine smooth site. -/
theorem bigAffineSmoothPresieveCovering_hasIsos
    {S : Scheme.{u}} :
    ∀ ⦃U V : bigAffineSmoothSite S⦄ (f : V ⟶ U) [IsIso f],
      bigAffineSmoothPresieveCovering (Presieve.singleton f) := sorry

/-- Big affine smooth coverings are stable under pullback. -/
theorem bigAffineSmoothPresieveCovering_pullbacks
    {S : Scheme.{u}} :
    ∀ ⦃U V : bigAffineSmoothSite S⦄ (f : V ⟶ U) (R : Presieve U),
      bigAffineSmoothPresieveCovering R →
        bigAffineSmoothPresieveCovering (Presieve.pullbackArrows f R) := sorry

/-- Big affine smooth coverings are stable under refinement. -/
theorem bigAffineSmoothPresieveCovering_transitive
    {S : Scheme.{u}} :
    ∀ ⦃U : bigAffineSmoothSite S⦄ (R : Presieve U)
      (Ti : ∀ ⦃V⦄ (f : V ⟶ U), R f → Presieve V),
      bigAffineSmoothPresieveCovering R →
        (∀ ⦃V⦄ (f : V ⟶ U) (H : R f), bigAffineSmoothPresieveCovering (Ti f H)) →
          bigAffineSmoothPresieveCovering (Presieve.bind R Ti) := sorry

/-- Definition 34.5.8 (2): the big affine smooth site of `S` carries the pretopology whose
covering presieves are presented by standard smooth coverings of affine `S`-schemes. -/
def bigAffineSmoothPretopology (S : Scheme.{u}) : Pretopology (bigAffineSmoothSite S) :=
  { coverings := fun _ ↦ { R | bigAffineSmoothPresieveCovering R }
    has_isos := bigAffineSmoothPresieveCovering_hasIsos
    pullbacks := bigAffineSmoothPresieveCovering_pullbacks
    transitive := bigAffineSmoothPresieveCovering_transitive }

/-- The Grothendieck topology on the big affine smooth site generated by standard smooth
coverings. -/
abbrev bigAffineSmoothTopology (S : Scheme.{u}) :
    GrothendieckTopology (bigAffineSmoothSite S) :=
  (bigAffineSmoothPretopology S).toGrothendieck

end AlgebraicGeometry
