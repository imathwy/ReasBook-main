import Mathlib
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits.CompleteLattice
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme

/- Semantic recall:
`lean_leansearch` recalled the existing owners
`Scheme.zariskiTopology`, `Scheme.overGrothendieckTopology`,
`Scheme.smallGrothendieckTopology`, and `Scheme.AffineZariskiSite.grothendieckTopology`.
For Definition 34.3.7 we reuse the canonical big/small Zariski topology owners, but we keep the
affine variants source-faithful as full subcategories with explicit standard-cover data because
mathlib's `Scheme.AffineZariskiSite` uses basic-open arrows rather than arbitrary inclusions. -/

private abbrev affineOverObjects (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X ↦ IsAffine X.left

private abbrev affineOpenObjects (S : Scheme.{u}) : ObjectProperty S.Opens :=
  fun U ↦ IsAffineOpen U

private instance opensOrderTop (S : Scheme.{u}) : OrderTop S.Opens :=
  (inferInstance : CompleteLattice S.Opens).toOrderTop

private instance opensHasFiniteLimits (S : Scheme.{u}) : HasFiniteLimits S.Opens :=
  hasFiniteLimits_of_semilatticeInf_orderTop

private instance affineOverObjects_isClosedUnderIsomorphisms (S : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (affineOverObjects S) where
  of_iso := by
    intro X Y e hX
    exact (IsAffine.iff_of_isIso e.hom.left).mp hX

private instance affineOpenObjects_isClosedUnderIsomorphisms (S : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (affineOpenObjects S) where
  of_iso := by
    intro U V e hU
    let hUV : U = V := le_antisymm e.hom.le e.inv.le
    simpa [hUV] using hU

private instance affineOpenObjects_isClosedUnderLimitsOfShape_walkingCospan (S : Scheme.{u}) :
    ObjectProperty.IsClosedUnderLimitsOfShape (affineOpenObjects S) WalkingCospan := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  let U := F.obj WalkingCospan.left
  let V := F.obj WalkingCospan.right
  have hInf : IsAffineOpen (U ⊓ V) := by
    have hPre : IsAffineOpen (V.ι ⁻¹ᵁ U) :=
      (hF WalkingCospan.left).preimage V.ι
    have hImage : IsAffineOpen (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) :=
      (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion V.ι).mpr hPre
    simpa [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm] using hImage
  let e := HasLimit.isoOfNatIso (diagramIsoCospan F)
  refine ObjectProperty.prop_of_iso (affineOpenObjects S) e.symm ?_
  change IsAffineOpen (pullback (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr))
  simpa [pullback_eq_inf] using hInf

section ZariskiSites

variable (S : Scheme.{u})

/-- The underlying category of the big Zariski site of a scheme. -/
abbrev bigZariskiSite :=
  Over S

/-- Definition 34.3.7 (1): the big Zariski site of `S` is the slice category `Over S` endowed
with the Zariski topology localized from `Scheme`. -/
@[stacks 020T]
abbrev bigZariskiTopology : GrothendieckTopology S.bigZariskiSite :=
  Scheme.zariskiTopology.over S

/-- The underlying category of the small Zariski site of a scheme. -/
abbrev smallZariskiSite :=
  (IsOpenImmersion : MorphismProperty Scheme.{u}).Over ⊤ S

/-- Definition 34.3.7 (2): the small Zariski site of `S` is the full subcategory of
`(Sch/S)_{Zar}` on open immersions, with coverings induced from the big Zariski site. -/
@[stacks 020T]
abbrev smallZariskiTopology : GrothendieckTopology S.smallZariskiSite :=
  S.smallGrothendieckTopology IsOpenImmersion

/-- The big Zariski site of `S` is the localized Zariski topology on `Over S`. -/
theorem bigZariskiTopology_eq_over :
    S.bigZariskiTopology = Scheme.zariskiTopology.over S :=
  rfl

/-- The small Zariski site of `S` carries the induced topology on open immersions over `S`. -/
theorem smallZariskiTopology_eq_small :
    S.smallZariskiTopology = S.smallGrothendieckTopology IsOpenImmersion :=
  rfl

/-- The canonical functor sending an open subset `U ⊆ S` to the corresponding open immersion
`U ⟶ S`, viewed as an object of the small Zariski site of `S`. -/
abbrev smallZariskiOpenFunctor : S.Opens ⥤ S.smallZariskiSite where
  obj U :=
    MorphismProperty.Over.mk ⊤ U.ι (inferInstance : IsOpenImmersion U.ι)
  map {U V} i :=
    MorphismProperty.Over.homMk
      (S.homOfLE i.le) (by simpa using (Scheme.homOfLE_ι S i.le))
  map_id X := by
    ext
    exact Scheme.homOfLE_rfl _ _
  map_comp f g := by
    ext
    exact (S.homOfLE_homOfLE f.le g.le).symm

/-- The canonical forgetful functor from the small Zariski site of `S` to `Over S`. -/
abbrev smallZariskiForget : S.smallZariskiSite ⥤ Over S :=
  MorphismProperty.Over.forget IsOpenImmersion ⊤ S

/-- The canonical forgetful functor from the small Zariski site of `S` to schemes. -/
abbrev smallZariskiToScheme : S.smallZariskiSite ⥤ Scheme :=
  smallZariskiForget S ⋙ Over.forget S

end ZariskiSites

section AffineZariskiSites

variable (S : Scheme.{u})

/-- Definition 34.3.7 (3): the big affine Zariski site of `S` is the full subcategory of
`(Sch/S)_{Zar}` on objects whose source scheme is affine. -/
@[stacks 020T]
abbrev bigAffineZariskiSite :=
  ObjectProperty.FullSubcategory (affineOverObjects S)

/-- Every object of the big affine Zariski site has affine source scheme. -/
theorem bigAffineZariskiSite_obj_isAffine (U : S.bigAffineZariskiSite) :
    IsAffine U.obj.left :=
  U.property

/-- The canonical inclusion functor from the big affine Zariski site of `S` to the big Zariski
site of `S`. -/
abbrev bigAffineZariskiInclusion : S.bigAffineZariskiSite ⥤ S.bigZariskiSite :=
  (affineOverObjects S).ι

/-- The canonical functor from the big affine Zariski site of `S` to schemes. -/
abbrev bigAffineZariskiToScheme : S.bigAffineZariskiSite ⥤ Scheme :=
  bigAffineZariskiInclusion S ⋙ Over.forget S

/-- Definition 34.3.7 (4): a covering in the big affine Zariski site is a standard Zariski
covering of an affine `S`-scheme by finitely many distinguished opens. The chosen finite family of
generators is companion data for the source-facing covering notion below. -/
@[stacks 020T]
structure BigAffineZariskiStandardCover (U : S.bigAffineZariskiSite) where
  /-- The number of distinguished opens in the chosen standard cover. -/
  n : ℕ
  /-- The global sections defining the standard distinguished opens. -/
  generator : let X := U.obj.left; Fin n → Γ(X, ⊤)
  /-- The distinguished opens associated to the generators cover the affine source scheme. -/
  cover : let X := U.obj.left; (⊤ : X.Opens) = ⨆ i, X.basicOpen (generator i)

/-- A big affine standard cover can be viewed as its indexed family of distinguished opens. -/
instance bigAffineZariskiStandardCoverCoeFun
    {S : Scheme.{u}} {U : S.bigAffineZariskiSite} :
    CoeFun (BigAffineZariskiStandardCover S U) (fun 𝒰 ↦
      Fin 𝒰.n → let X := U.obj.left; X.Opens) where
  coe := fun 𝒰 i ↦
    let X := U.obj.left
    X.basicOpen (𝒰.generator i)

/-- The distinguished opens in a big affine standard cover have supremum `⊤`. -/
theorem BigAffineZariskiStandardCover.iSup_eq_top
    {S : Scheme.{u}} {U : S.bigAffineZariskiSite} (𝒰 : BigAffineZariskiStandardCover S U) :
    (⨆ i, 𝒰 i) = (⊤ : let X := U.obj.left; X.Opens) :=
  𝒰.cover.symm

/-- The `i`-th distinguished open in a big affine standard Zariski cover, viewed as an affine
`S`-scheme. -/
def BigAffineZariskiStandardCover.siteObj {U : S.bigAffineZariskiSite}
    (𝒰 : BigAffineZariskiStandardCover S U) (i : Fin 𝒰.n) : S.bigAffineZariskiSite where
  obj := Over.mk ((𝒰 i).ι ≫ U.obj.hom)
  property := by
    let _ : IsAffine U.obj.left := U.property
    simpa using (inferInstance : IsAffine (𝒰 i))

/-- The `i`-th distinguished-open immersion in a big affine standard Zariski cover, viewed as a
morphism in the affine over-site of `S`. -/
def BigAffineZariskiStandardCover.siteMap {U : S.bigAffineZariskiSite}
    (𝒰 : BigAffineZariskiStandardCover S U) (i : Fin 𝒰.n) :
    BigAffineZariskiStandardCover.siteObj S 𝒰 i ⟶ U :=
  ObjectProperty.homMk <|
    Over.homMk (𝒰 i).ι (by rfl)

/-- Definition 34.3.7 (4): a presieve on the big affine Zariski site is covering when it is
presented by a finite standard distinguished-open covering. -/
@[stacks 020T]
def bigAffineZariskiCovering {U : S.bigAffineZariskiSite} (R : Presieve U) : Prop :=
  ∃ 𝒰 : BigAffineZariskiStandardCover S U,
    R =
      Presieve.ofArrows
        (BigAffineZariskiStandardCover.siteObj S 𝒰)
        (BigAffineZariskiStandardCover.siteMap S 𝒰)

/-- A big affine standard Zariski cover presents a covering presieve on `S.bigAffineZariskiSite`.
-/
theorem bigAffineZariskiCovering_ofStandardCover {U : S.bigAffineZariskiSite}
    (𝒰 : BigAffineZariskiStandardCover S U) :
    S.bigAffineZariskiCovering
      (Presieve.ofArrows
        (BigAffineZariskiStandardCover.siteObj S 𝒰)
        (BigAffineZariskiStandardCover.siteMap S 𝒰)) :=
  ⟨𝒰, rfl⟩

/-- Affine objects in `Over S` are closed under pullbacks. -/
instance bigAffineZariskiSite_isClosedUnderLimitsOfShape_walkingCospan :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (affineOverObjects S) WalkingCospan := by
  sorry

/-- The big affine Zariski site has pullbacks. -/
instance bigAffineZariskiSite_hasPullbacks : HasPullbacks S.bigAffineZariskiSite :=
  inferInstance

/-- Singleton isomorphisms are covering families in the big affine Zariski site. -/
theorem bigAffineZariskiCovering_hasIsos
    {U V : S.bigAffineZariskiSite} (f : V ⟶ U) [IsIso f] :
    S.bigAffineZariskiCovering (Presieve.singleton f) := sorry

/-- Big affine Zariski coverings are stable under pullback. -/
theorem bigAffineZariskiCovering_pullbacks
    {U V : S.bigAffineZariskiSite} (f : V ⟶ U) (R : Presieve U) :
    S.bigAffineZariskiCovering R →
      S.bigAffineZariskiCovering (Presieve.pullbackArrows f R) := sorry

/-- Big affine Zariski coverings are stable under refinement. -/
theorem bigAffineZariskiCovering_transitive
    {U : S.bigAffineZariskiSite} (R : Presieve U)
    (Ti : ∀ ⦃V⦄, (f : V ⟶ U) → R f → Presieve V) :
    S.bigAffineZariskiCovering R →
      (∀ ⦃V⦄ (f : V ⟶ U) (H : R f), S.bigAffineZariskiCovering (Ti f H)) →
        S.bigAffineZariskiCovering (Presieve.bind R Ti) := sorry

/-- The restricted big Zariski precoverage on affine `S`-schemes. -/
abbrev bigAffineZariskiPrecoverage : Precoverage S.bigAffineZariskiSite :=
  Precoverage.comap (bigAffineZariskiInclusion S) (bigZariskiTopology S).toPrecoverage

/-- A presieve on the affine slice is covering for the restricted big Zariski precoverage exactly
when its image in `Over S` is covering for the canonical big Zariski precoverage. -/
@[simp] theorem mem_bigAffineZariskiPrecoverage_iff
    {U : S.bigAffineZariskiSite} {R : Presieve U} :
    R ∈ bigAffineZariskiPrecoverage S U ↔
      R.map (bigAffineZariskiInclusion S) ∈ (bigZariskiTopology S).toPrecoverage U.obj := by
  rw [bigAffineZariskiPrecoverage, Precoverage.mem_comap_iff]
  rfl

/-- Every source-facing standard big affine Zariski covering presieve is covering for the
canonical restricted big Zariski precoverage. -/
theorem bigAffineZariskiCovering_mem_precoverage
    {U : S.bigAffineZariskiSite} {R : Presieve U}
    (hR : S.bigAffineZariskiCovering R) :
    R ∈ bigAffineZariskiPrecoverage S U := sorry

/-- `bigAffineZariskiCovering` unfolds to the source-facing standard-cover presentation from the
definition. -/
theorem bigAffineZariskiCovering_iff
    {U : S.bigAffineZariskiSite} {R : Presieve U} :
    S.bigAffineZariskiCovering R ↔
      ∃ 𝒰 : BigAffineZariskiStandardCover S U,
        R =
          Presieve.ofArrows
            (BigAffineZariskiStandardCover.siteObj S 𝒰)
            (BigAffineZariskiStandardCover.siteMap S 𝒰) :=
  Iff.intro (fun h ↦ h) (fun h ↦ h)

/-- Definition 34.3.7 (4): the big affine Zariski topology is the Grothendieck topology on affine
`S`-schemes obtained by restricting the big Zariski site along the affine inclusion. The
standard-cover predicate above is the source-facing covering description on this site. -/
@[stacks 020T]
abbrev bigAffineZariskiTopology : GrothendieckTopology S.bigAffineZariskiSite :=
  (bigAffineZariskiPrecoverage S).toGrothendieck

/-- Definition 34.3.7 (5): the small affine Zariski site of `S` is the full subcategory of
`S_{Zar}` on affine opens of `S`. -/
@[stacks 020T]
abbrev smallAffineZariskiSite :=
  ObjectProperty.FullSubcategory (affineOpenObjects S)

/-- Every object of the small affine Zariski site is an affine open of `S`. -/
theorem smallAffineZariskiSite_obj_isAffineOpen (U : S.smallAffineZariskiSite) :
    IsAffineOpen U.obj :=
  U.property

/-- The canonical forgetful functor from the small affine Zariski site of `S` to affine opens of
`S`. -/
abbrev smallAffineZariskiToOpens : S.smallAffineZariskiSite ⥤ S.Opens :=
  (affineOpenObjects S).ι

/-- The canonical inclusion functor from the small affine Zariski site of `S` to the small
Zariski site of `S`. -/
abbrev smallAffineZariskiInclusion : S.smallAffineZariskiSite ⥤ S.smallZariskiSite :=
  smallAffineZariskiToOpens S ⋙ smallZariskiOpenFunctor S

/-- The canonical functor from the small affine Zariski site of `S` to schemes. -/
abbrev smallAffineZariskiToScheme : S.smallAffineZariskiSite ⥤ Scheme :=
  smallAffineZariskiInclusion S ⋙ smallZariskiToScheme S

/-- The small affine Zariski site of `S` has pullbacks. -/
instance smallAffineZariskiSite_hasPullbacks : HasPullbacks S.smallAffineZariskiSite :=
  inferInstance

/-- The canonical functor from the small affine Zariski site of `S` to schemes preserves
pullbacks. -/
instance smallAffineZariskiToScheme_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (smallAffineZariskiToScheme S) := by
  change
    PreservesLimitsOfShape WalkingCospan
      (smallAffineZariskiInclusion S ⋙ smallZariskiToScheme S)
  infer_instance

/-- Definition 34.3.7 (6): a covering in the small affine Zariski site is a standard Zariski
covering of an affine open `U ⊆ S` by finitely many distinguished opens inside `U`. The chosen
finite family of generators is companion data for the source-facing covering notion below. -/
@[stacks 020T]
structure SmallAffineZariskiStandardCover (U : S.smallAffineZariskiSite) where
  /-- The number of distinguished opens in the chosen standard cover. -/
  n : ℕ
  /-- The sections on `U` defining the distinguished opens of the cover. -/
  generator : Fin n → Γ(S, U.obj)
  /-- The distinguished opens associated to the generators cover `U`. -/
  cover : U.obj = ⨆ i, S.basicOpen (generator i)

/-- A small affine standard cover can be viewed as its indexed family of distinguished opens. -/
instance smallAffineZariskiStandardCoverCoeFun
    {S : Scheme.{u}} {U : S.smallAffineZariskiSite} :
    CoeFun (SmallAffineZariskiStandardCover S U) (fun 𝒰 ↦ Fin 𝒰.n → S.Opens) where
  coe := fun 𝒰 i ↦ S.basicOpen (𝒰.generator i)

/-- The distinguished opens in a small affine standard cover have supremum `U`. -/
theorem SmallAffineZariskiStandardCover.iSup_eq
    {S : Scheme.{u}} {U : S.smallAffineZariskiSite} (𝒰 : SmallAffineZariskiStandardCover S U) :
    (⨆ i, 𝒰 i) = U.obj :=
  𝒰.cover.symm

/-- The `i`-th distinguished open in a small affine standard Zariski cover, viewed as an affine
open of `S`. -/
def SmallAffineZariskiStandardCover.siteObj {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) (i : Fin 𝒰.n) : S.smallAffineZariskiSite where
  obj := 𝒰 i
  property := U.property.basicOpen (𝒰.generator i)

/-- The inclusion of the `i`-th distinguished open in a small affine standard Zariski cover. -/
def SmallAffineZariskiStandardCover.siteMap {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) (i : Fin 𝒰.n) :
    SmallAffineZariskiStandardCover.siteObj S 𝒰 i ⟶ U :=
  ObjectProperty.homMk <|
    homOfLE (by
      simpa [SmallAffineZariskiStandardCover.iSup_eq 𝒰] using
        (le_iSup (fun j ↦ 𝒰 j) i))

/-- Definition 34.3.7 (6): a presieve on the small affine Zariski site is covering when it is
presented by a finite standard distinguished-open covering. -/
@[stacks 020T]
def smallAffineZariskiCovering {U : S.smallAffineZariskiSite} (R : Presieve U) : Prop :=
  ∃ 𝒰 : SmallAffineZariskiStandardCover S U,
    R =
      Presieve.ofArrows
        (SmallAffineZariskiStandardCover.siteObj S 𝒰)
        (SmallAffineZariskiStandardCover.siteMap S 𝒰)

/-- A small affine standard Zariski cover presents a covering presieve on
`S.smallAffineZariskiSite`. -/
theorem smallAffineZariskiCovering_ofStandardCover {U : S.smallAffineZariskiSite}
    (𝒰 : SmallAffineZariskiStandardCover S U) :
    S.smallAffineZariskiCovering
      (Presieve.ofArrows
        (SmallAffineZariskiStandardCover.siteObj S 𝒰)
        (SmallAffineZariskiStandardCover.siteMap S 𝒰)) :=
  ⟨𝒰, rfl⟩

/-- Singleton isomorphisms are covering families in the small affine Zariski site. -/
theorem smallAffineZariskiCovering_hasIsos
    {U V : S.smallAffineZariskiSite} (f : V ⟶ U) [IsIso f] :
    S.smallAffineZariskiCovering (Presieve.singleton f) := sorry

/-- Small affine Zariski coverings are stable under pullback. -/
theorem smallAffineZariskiCovering_pullbacks
    {U V : S.smallAffineZariskiSite} (f : V ⟶ U) (R : Presieve U) [R.HasPullbacks f] :
    S.smallAffineZariskiCovering R →
      S.smallAffineZariskiCovering (Presieve.pullbackArrows f R) := sorry

/-- Small affine Zariski coverings are stable under refinement. -/
theorem smallAffineZariskiCovering_transitive
    {U : S.smallAffineZariskiSite} (R : Presieve U)
    (Ti : ∀ ⦃V⦄, (f : V ⟶ U) → R f → Presieve V) :
    S.smallAffineZariskiCovering R →
      (∀ ⦃V⦄ (f : V ⟶ U) (H : R f), S.smallAffineZariskiCovering (Ti f H)) →
        S.smallAffineZariskiCovering (Presieve.bind R Ti) := sorry

/-- The restricted Zariski precoverage on affine opens of `S`. -/
abbrev smallAffineZariskiPrecoverage : Precoverage S.smallAffineZariskiSite :=
  Precoverage.comap (smallAffineZariskiToOpens S) (Opens.grothendieckTopology ↑S).toPrecoverage

/-- A presieve on affine opens is covering for the restricted Zariski precoverage exactly when
its image in `S.Opens` is covering for the canonical precoverage of opens. -/
@[simp] theorem mem_smallAffineZariskiPrecoverage_iff
    {U : S.smallAffineZariskiSite} {R : Presieve U} :
    R ∈ smallAffineZariskiPrecoverage S U ↔
      R.map (smallAffineZariskiToOpens S) ∈
        (Opens.grothendieckTopology ↑S).toPrecoverage U.obj := by
  rw [smallAffineZariskiPrecoverage, Precoverage.mem_comap_iff]
  rfl

/-- Every source-facing standard small affine Zariski covering presieve is covering for the
canonical restricted Zariski precoverage on affine opens. -/
theorem smallAffineZariskiCovering_mem_precoverage
    {U : S.smallAffineZariskiSite} {R : Presieve U}
    (hR : S.smallAffineZariskiCovering R) :
    R ∈ smallAffineZariskiPrecoverage S U := sorry

/-- `smallAffineZariskiCovering` unfolds to the source-facing standard-cover presentation from
the definition. -/
theorem smallAffineZariskiCovering_iff
    {U : S.smallAffineZariskiSite} {R : Presieve U} :
    S.smallAffineZariskiCovering R ↔
      ∃ 𝒰 : SmallAffineZariskiStandardCover S U,
        R =
          Presieve.ofArrows
            (SmallAffineZariskiStandardCover.siteObj S 𝒰)
            (SmallAffineZariskiStandardCover.siteMap S 𝒰) :=
  Iff.intro (fun h ↦ h) (fun h ↦ h)

/-- Definition 34.3.7 (6): the small affine Zariski topology is the Grothendieck topology on
affine opens obtained by restricting the canonical topology on `S.Opens`. The standard-cover
predicate above is the source-facing covering description on this site. -/
@[stacks 020T]
abbrev smallAffineZariskiTopology : GrothendieckTopology S.smallAffineZariskiSite :=
  (smallAffineZariskiPrecoverage S).toGrothendieck

end AffineZariskiSites

end Scheme
end AlgebraicGeometry
