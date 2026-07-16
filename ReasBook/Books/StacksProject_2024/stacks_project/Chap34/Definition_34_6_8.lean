import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import StacksProject_2024.stacks_project.Chap34.Definition_34_6_1
import StacksProject_2024.stacks_project.Chap34.Definition_34_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry

private abbrev affineOverObjects (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun U ↦ IsAffine U.left

/- Semantic recall / owner check:
- `lean_leansearch` recalled the canonical site owner `Scheme.overGrothendieckTopology` on
  `Over S` and the affine full-subcategory owner `ObjectProperty.FullSubcategory`.
- `Definition_34_6_1` already owns the source-facing syntomic morphism property, and
  `Definition_34_6_5` owns the affine standard syntomic covering data and its direct companions.
  This file therefore keeps only the site-level owners built from those earlier Chapter 34
  declarations.
-/

/-- Definition 34.6.8 (1): the big syntomic site of a scheme `S` is the canonical syntomic
Grothendieck topology on the over category `Over S`. -/
abbrev bigSyntomicSite (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  S.overGrothendieckTopology (@Syntomic)

/-- The big syntomic site is exactly the syntomic Grothendieck topology on `Over S`. -/
theorem bigSyntomicSite_def (S : Scheme.{u}) :
    bigSyntomicSite S = S.overGrothendieckTopology (@Syntomic) :=
  rfl

/-- Definition 34.6.8 (2): the big affine syntomic site of `S` has as objects the affine
`S`-schemes inside `Over S`. -/
abbrev bigAffineSyntomicSite (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (affineOverObjects S)

/-- Objects of the big affine syntomic site have affine underlying scheme. -/
instance bigAffineSyntomicSite.instIsAffineObj {S : Scheme.{u}} (U : bigAffineSyntomicSite S) :
    IsAffine U.obj.left :=
  U.property

/-- The inclusion functor from the big affine syntomic site of `S` to the over category
`Over S`. -/
abbrev bigAffineSyntomicForget (S : Scheme.{u}) : bigAffineSyntomicSite S ⥤ Over S :=
  ObjectProperty.ι (affineOverObjects S)

@[simp] theorem bigAffineSyntomicForget_obj (S : Scheme.{u}) (U : bigAffineSyntomicSite S) :
    (bigAffineSyntomicForget S).obj U = U.obj :=
  rfl

@[simp] theorem bigAffineSyntomicForget_map (S : Scheme.{u})
    {U V : bigAffineSyntomicSite S} (f : U ⟶ V) :
    (bigAffineSyntomicForget S).map f = f.hom :=
  rfl

/-- Definition 34.6.8 (4): on the affine full subcategory of `Over S`, a covering family
of an affine object is a standard syntomic covering of its underlying affine scheme. -/
abbrev bigAffineSyntomicCovering {S : Scheme.{u}} (U : bigAffineSyntomicSite S) :=
  StandardSyntomicCovering U.obj.left

/-- A covering family in the big affine syntomic site is a syntomic covering family of the
underlying affine target in the Chapter 34 fixed-target owner. -/
theorem bigAffineSyntomicCovering_mem_syntomic_precoverage
    {S : Scheme.{u}} {U : bigAffineSyntomicSite S} (𝒰 : bigAffineSyntomicCovering U) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈
      (Scheme.precoverage (@Syntomic)).coverings U.obj.left :=
  𝒰.mem_syntomic_precoverage

/-- A covering family in the big affine syntomic site covers the underlying affine target. -/
theorem bigAffineSyntomicCovering_iUnion_range_eq_univ
    {S : Scheme.{u}} {U : bigAffineSyntomicSite S} (𝒰 : bigAffineSyntomicCovering U) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ :=
  𝒰.iUnion_range_eq_univ

/-- The `j`-th member of a standard syntomic covering of an affine `S`-scheme, viewed as an
object of the big affine syntomic site over `S`. -/
def StandardSyntomicCovering.siteObj {S : Scheme.{u}} {U : bigAffineSyntomicSite S}
    (𝒰 : bigAffineSyntomicCovering U) (j : Fin 𝒰.n) : bigAffineSyntomicSite S where
  obj := Over.mk (𝒰.map j ≫ U.obj.hom)
  property := 𝒰.isAffine j

/-- The `j`-th arrow of a standard syntomic covering, viewed in the affine over-site of `S`. -/
def StandardSyntomicCovering.siteMap {S : Scheme.{u}} {U : bigAffineSyntomicSite S}
    (𝒰 : bigAffineSyntomicCovering U) :
    ∀ j : Fin 𝒰.n, StandardSyntomicCovering.siteObj 𝒰 j ⟶ U :=
  fun j ↦
    ObjectProperty.homMk <|
      Over.homMk (𝒰.map j) (by rfl)

/-- A presieve on the big affine syntomic site is covering when it is presented by a standard
syntomic covering of the underlying affine target scheme. -/
def bigAffineSyntomicPresieveCovering {S : Scheme.{u}} {U : bigAffineSyntomicSite S}
    (R : Presieve U) : Prop :=
  ∃ 𝒰 : bigAffineSyntomicCovering U,
    R =
      Presieve.ofArrows
        (StandardSyntomicCovering.siteObj 𝒰)
        (StandardSyntomicCovering.siteMap 𝒰)

/-- A standard syntomic covering presents a covering presieve on the big affine syntomic site. -/
theorem bigAffineSyntomicPresieveCovering_of_standardCover
    {S : Scheme.{u}} {U : bigAffineSyntomicSite S} (𝒰 : bigAffineSyntomicCovering U) :
    bigAffineSyntomicPresieveCovering
      (Presieve.ofArrows
        (StandardSyntomicCovering.siteObj 𝒰)
        (StandardSyntomicCovering.siteMap 𝒰)) :=
  ⟨𝒰, rfl⟩

/-- The canonical restricted syntomic precoverage on affine `S`-schemes. -/
abbrev bigAffineSyntomicPrecoverage (S : Scheme.{u}) : Precoverage (bigAffineSyntomicSite S) :=
  (bigSyntomicSite S).toPrecoverage.comap (bigAffineSyntomicForget S)

/-- A presieve on the affine slice is covering for the restricted syntomic precoverage exactly
when its image in `Over S` is covering for the canonical big syntomic precoverage. -/
@[simp] theorem mem_bigAffineSyntomicPrecoverage_iff
    {S : Scheme.{u}} {U : bigAffineSyntomicSite S} {R : Presieve U} :
    R ∈ bigAffineSyntomicPrecoverage S U ↔
      R.map (bigAffineSyntomicForget S) ∈ (bigSyntomicSite S).toPrecoverage U.obj := by
  rw [bigAffineSyntomicPrecoverage, Precoverage.mem_comap_iff]
  rfl

/-- Every source-facing standard syntomic covering presieve is covering for the canonical
restricted syntomic precoverage on affine `S`-schemes. -/
theorem bigAffineSyntomicPresieveCovering_mem_precoverage
    {S : Scheme.{u}} {U : bigAffineSyntomicSite S} {R : Presieve U}
    (hR : bigAffineSyntomicPresieveCovering R) :
    R ∈ bigAffineSyntomicPrecoverage S U := sorry

/-- Affine objects in `Over S` are closed under isomorphisms. -/
instance bigAffineSyntomicSite_isClosedUnderIsomorphisms (S : Scheme.{u}) :
    IsClosedUnderIsomorphisms (affineOverObjects S) where
  of_iso := by
    intro X Y e hX
    exact (IsAffine.iff_of_isIso e.hom.left).mp hX

/-- Affine objects in `Over S` are closed under pullbacks. -/
instance bigAffineSyntomicSite_isClosedUnderLimitsOfShape_walkingCospan (S : Scheme.{u}) :
    IsClosedUnderLimitsOfShape (affineOverObjects S) WalkingCospan := by
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

/-- The big affine syntomic site has pullbacks. -/
instance bigAffineSyntomicSite_hasPullbacks (S : Scheme.{u}) :
    HasPullbacks (bigAffineSyntomicSite S) :=
  CategoryTheory.Limits.hasLimitsOfShape_of_closedUnderLimits
    WalkingCospan
    (affineOverObjects S)

/-- Singleton isomorphisms are covering families in the big affine syntomic site. -/
theorem bigAffineSyntomicPresieveCovering_hasIsos
    {S : Scheme.{u}} {U V : bigAffineSyntomicSite S} (f : V ⟶ U) [IsIso f] :
    bigAffineSyntomicPresieveCovering (Presieve.singleton f) := sorry

/-- Big affine syntomic coverings are stable under pullback. -/
theorem bigAffineSyntomicPresieveCovering_pullbacks
    {S : Scheme.{u}} {U V : bigAffineSyntomicSite S} (f : V ⟶ U) (R : Presieve U)
    (hR : bigAffineSyntomicPresieveCovering R) :
    bigAffineSyntomicPresieveCovering (Presieve.pullbackArrows f R) := sorry

/-- Big affine syntomic coverings are stable under refinement. -/
theorem bigAffineSyntomicPresieveCovering_transitive
    {S : Scheme.{u}} {U : bigAffineSyntomicSite S} (R : Presieve U)
    (Ti : ∀ ⦃V⦄, (f : V ⟶ U) → R f → Presieve V)
    (hR : bigAffineSyntomicPresieveCovering R)
    (hTi : ∀ ⦃V⦄ (f : V ⟶ U) (H : R f), bigAffineSyntomicPresieveCovering (Ti f H)) :
    bigAffineSyntomicPresieveCovering (Presieve.bind R Ti) := sorry

/-- Definition 34.6.8 (3): the big affine syntomic site of `S` carries the pretopology whose
covering presieves are presented by standard syntomic coverings of affine `S`-schemes. -/
def bigAffineSyntomicPretopology (S : Scheme.{u}) : Pretopology (bigAffineSyntomicSite S) :=
  { coverings := fun _ ↦ { R | bigAffineSyntomicPresieveCovering R }
    has_isos := bigAffineSyntomicPresieveCovering_hasIsos
    pullbacks := bigAffineSyntomicPresieveCovering_pullbacks
    transitive := bigAffineSyntomicPresieveCovering_transitive }

/-- The Grothendieck topology on the big affine syntomic site generated by standard syntomic
coverings. -/
abbrev bigAffineSyntomicTopology (S : Scheme.{u}) :
    GrothendieckTopology (bigAffineSyntomicSite S) :=
  (bigAffineSyntomicPretopology S).toGrothendieck

/-- Unfolding `bigAffineSyntomicTopology` recovers the Grothendieck topology generated by the
standard syntomic pretopology on affine `S`-schemes. -/
theorem bigAffineSyntomicTopology_def (S : Scheme.{u}) :
    bigAffineSyntomicTopology S = (bigAffineSyntomicPretopology S).toGrothendieck :=
  rfl

end AlgebraicGeometry
