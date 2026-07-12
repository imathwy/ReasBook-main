import Mathlib
import StacksProject_2024.Chap06.Definition_6_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Definition 17.20.1:
- primary domain: flatness of morphisms of ringed spaces, expressed stalkwise;
- sampled owner declarations:
  `AlgebraicGeometry.Flat`,
  `AlgebraicGeometry.Flat.stalkMap`,
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`;
- owner abstraction: the project-level owner for ringed-space morphisms is the global predicate
  `RingedSpace.Hom.IsFlat`, while the scheme specialization is already owned upstream by
  `AlgebraicGeometry.Flat`;
- primitive data: the family of flat stalk maps;
- derived API: the pointwise source-facing predicate `FlatAt`, the owner projection
  `RingedSpace.Hom.IsFlat.flatAt`, and the scheme bridge
  `Scheme.Hom.isFlat_iff_flat`.

Source/core/bridge triage:
- `source-facing`: `FlatAt`;
- `core/canonical`: `IsFlat`;
- `bridge/view`: `Scheme.Hom.isFlat_iff_flat`.

The public owner should therefore be `IsFlat`, with `FlatAt` retained only as the pointwise view
named in the source, and the scheme specialization connected directly to the mathlib owner
`AlgebraicGeometry.Flat`. -/

/-- Definition 17.20.1: a morphism of ringed spaces is flat at `x` when the induced stalk map
`\mathcal O_{Y, f(x)} \to \mathcal O_{X, x}` is a flat ring homomorphism. -/
@[stacks 02N3]
abbrev FlatAt (x : X) : Prop :=
  (f.hom.stalkMap x).hom.Flat

/-- A morphism of ringed spaces is flat when it is flat at every point of the source. -/
@[mk_iff]
class IsFlat : Prop where
  flatAt (x : X) : FlatAt f x

end RingedSpace.Hom

namespace AlgebraicGeometry

open CategoryTheory
open RingedSpace.Hom

/-- Helper for Definition 17.20.1: the unique stalk of `pointRingedSpace x` is the stalk of the
skyscraper presheaf on `TopCat.of PUnit` with value `X.presheaf.stalk x`. -/
lemma pointRingedSpaceStalk_eq_skyscraperStalk {X : RingedSpace.{u}} (x : X)
    [hP : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U)] :
    (pointRingedSpace x).presheaf.stalk PUnit.unit =
      (skyscraperPresheaf (X := TopCat.of PUnit) PUnit.unit (X.presheaf.stalk x)).stalk
        PUnit.unit := by
  classical
  -- Normalize the point ringed space back to the defining skyscraper sheaf.
  simp [pointRingedSpace, skyscraperSheaf]
  have hinst :
      hP = fun U : TopologicalSpace.Opens (TopCat.of PUnit) =>
        Classical.propDecidable (PUnit.unit ∈ U) := Subsingleton.elim _ _
  cases hinst
  rfl

/-- Helper for Definition 17.20.1: the unique stalk of `pointRingedSpace x` identifies
canonically with `X.presheaf.stalk x`. -/
noncomputable def pointRingedSpaceStalkIso {X : RingedSpace.{u}} (x : X)
    [hP : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U)] :
    (pointRingedSpace x).presheaf.stalk PUnit.unit ≅ X.presheaf.stalk x :=
  (CategoryTheory.eqToIso (pointRingedSpaceStalk_eq_skyscraperStalk (x := x))) ≪≫
    (skyscraperPresheafStalkOfSpecializes (X := TopCat.of PUnit) PUnit.unit
      (X.presheaf.stalk x) (specializes_rfl : PUnit.unit ⤳ PUnit.unit))

/-- Helper for Definition 17.20.1: `pointRingedSpaceStalkIso` is exactly the transport from the
point-space stalk to the skyscraper stalk, followed by the canonical skyscraper stalk
identification. -/
lemma pointRingedSpaceStalkIso_hom {X : RingedSpace.{u}} (x : X)
    [hP : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U)] :
    (pointRingedSpaceStalkIso (x := x)).hom =
      eqToHom (pointRingedSpaceStalk_eq_skyscraperStalk (x := x)) ≫
        (skyscraperPresheafStalkOfSpecializes (X := TopCat.of PUnit) PUnit.unit
          (X.presheaf.stalk x)
          (show @Specializes _ (TopCat.of PUnit).str PUnit.unit PUnit.unit from specializes_rfl)).hom := by
  -- Unfold the composite once so later proofs can rewrite away the stalk-identification transport.
  rfl

/-- Helper for Definition 17.20.1: on the one-point space, the skyscraper germ into the unique
stalk is the expected `eqToHom` after composing with the canonical stalk identification. -/
lemma pointSkyscraperGerm_comp_stalkOfSpecializes_hom {X : RingedSpace.{u}} (x : X)
    [hP : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U)]
    {U : TopologicalSpace.Opens (TopCat.of PUnit)} (hU : PUnit.unit ∈ U) :
    (skyscraperPresheaf (X := TopCat.of PUnit) PUnit.unit (X.presheaf.stalk x)).germ U PUnit.unit hU ≫
      (skyscraperPresheafStalkOfSpecializes (X := TopCat.of PUnit) PUnit.unit
        (X.presheaf.stalk x)
        (show @Specializes _ (TopCat.of PUnit).str PUnit.unit PUnit.unit from specializes_rfl)).hom =
      eqToHom (by simp [hU]) := by
  -- The one-point skyscraper germ is the generic skyscraper computation specialized to `PUnit`.
  simpa [hU] using
    (germ_skyscraperPresheafStalkOfSpecializes_hom
      (X := TopCat.of PUnit) (p₀ := PUnit.unit) (A := X.presheaf.stalk x)
      (h := (show @Specializes _ (TopCat.of PUnit).str PUnit.unit PUnit.unit from specializes_rfl))
      (U := U) (hU := hU))

/-- Helper for Definition 17.20.1: an open of the one-point space that contains the unique point
is the top open. -/
lemma pointSpaceOpen_eq_top {U : TopologicalSpace.Opens (TopCat.of PUnit)} (hU : PUnit.unit ∈ U) :
    U = ⊤ := by
  -- The one-point space has no other opens containing its unique point.
  ext y
  cases y
  simpa using hU

/-- Helper for Definition 17.20.1: after identifying the unique stalk of `pointRingedSpace x`
with `X.presheaf.stalk x`, the germ from an open of the one-point space is the canonical
transport into that stalk. -/
lemma pointRingedSpaceGerm_comp_pointRingedSpaceStalkIso_hom {X : RingedSpace.{u}} (x : X)
    [hP : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U)]
    {U : TopologicalSpace.Opens (TopCat.of PUnit)} (hU : PUnit.unit ∈ U) :
    (pointRingedSpace x).presheaf.germ U PUnit.unit hU ≫ (pointRingedSpaceStalkIso (x := x)).hom =
      eqToHom (by
        have htop : U = ⊤ := pointSpaceOpen_eq_top hU
        simpa [htop, pointRingedSpace, skyscraperSheaf]) := by
  classical
  -- Collapse the source open to `⊤` inside the helper, where the dependent transport is harmless.
  cases pointSpaceOpen_eq_top hU
  rw [pointRingedSpaceStalkIso_hom]
  have hinst :
      hP = fun U : TopologicalSpace.Opens (TopCat.of PUnit) =>
        Classical.propDecidable (PUnit.unit ∈ U) := Subsingleton.elim _ _
  cases hinst
  simpa [pointRingedSpace, skyscraperSheaf, Category.assoc] using
    (pointSkyscraperGerm_comp_stalkOfSpecializes_hom (x := x) (U := ⊤) (hU := hU))

/-- Helper for Definition 17.20.1: every open containing `x` pulls back along `pointInclusion x`
to the top open of the one-point space. -/
lemma pointInclusion_preimage_eq_top {X : RingedSpace.{u}} (x : X)
    {U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace} (hxU : x ∈ U) :
    ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) = ⊤ := by
  -- The source has one point, and that point maps to `x`.
  ext y
  cases y
  simpa using hxU

/-- Helper for Definition 17.20.1: after normalizing the pulled-back open of the one-point space,
the section map of `pointInclusion x` followed by the point-space germ/stalk comparison matches
the stalk/skyscraper adjunction unit on `U`. -/
lemma pointInclusionSectionApp_comp_germ_comp_pointRingedSpaceStalkIso_hom
    {X : RingedSpace.{u}} (x : X)
    [hX : (U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) → Decidable (x ∈ U)]
    [hP : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U)]
    {U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace} (hxU : x ∈ U) :
    (pointInclusion x).hom.c.app (Opposite.op U) ≫
        (pointRingedSpace x).presheaf.germ
          ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) PUnit.unit
          (by simpa [pointInclusion_hom_base_apply] using hxU) ≫
        (pointRingedSpaceStalkIso (x := x)).hom =
      (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom.app (Opposite.op U)) ≫
        eqToHom (if_pos hxU) := by
  have hxP : PUnit.unit ∈ ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) := by
    -- Rewrite membership in the pulled-back open into membership of `x` in the ambient open.
    simpa [pointInclusion_hom_base_apply] using hxU
  have hgerm :
      (pointRingedSpace x).presheaf.germ
          ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) PUnit.unit hxP ≫
        (pointRingedSpaceStalkIso (x := x)).hom =
      eqToHom (if_pos hxU) := by
    -- Collapse the pulled-back open to `⊤` and use the one-point germ computation already proved.
    simpa [pointInclusion_hom_base_apply, pointInclusion_preimage_eq_top (x := x) hxU] using
      (pointRingedSpaceGerm_comp_pointRingedSpaceStalkIso_hom
        (x := x)
        (U := ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U))
        (hU := hxP))
  -- Route correction: normalize the entire section-map composite so the target is in the exact
  -- right-hand side normal form of `germ_fromStalk`.
  have hprecomp :
      (pointInclusion x).hom.c.app (Opposite.op U) ≫
          ((pointRingedSpace x).presheaf.germ
              ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) PUnit.unit hxP ≫
            (pointRingedSpaceStalkIso (x := x)).hom) =
        (pointInclusion x).hom.c.app (Opposite.op U) ≫ eqToHom (if_pos hxU) := by
    -- First rewrite only the point-space germ/stalk tail, keeping the actual section map fixed.
    simpa [Category.assoc] using
      congrArg (fun k => (pointInclusion x).hom.c.app (Opposite.op U) ≫ k) hgerm
  calc
    (pointInclusion x).hom.c.app (Opposite.op U) ≫
        (pointRingedSpace x).presheaf.germ
          ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) PUnit.unit
          (by simpa [pointInclusion_hom_base_apply] using hxU) ≫
        (pointRingedSpaceStalkIso (x := x)).hom
      =
        (pointInclusion x).hom.c.app (Opposite.op U) ≫ eqToHom (if_pos hxU) := by
          simpa [Category.assoc] using hprecomp
    _ =
        (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom.app (Opposite.op U)) ≫
          eqToHom (if_pos hxU) := by
            simpa [pointInclusion_def, Category.assoc]

/-- Helper for Definition 17.20.1: after identifying the point-space stalk with
`X.presheaf.stalk x`, the stalk map of `pointInclusion x` is the adjunction map
`fromStalk x ((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom`. -/
lemma pointInclusionStalkMap_comp_pointRingedSpaceStalkIso_hom {X : RingedSpace.{u}} (x : X)
    [hX : (U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) → Decidable (x ∈ U)]
    [hP : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U)] :
    ((pointInclusion x).hom.stalkMap PUnit.unit) ≫ (pointRingedSpaceStalkIso (x := x)).hom =
      StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
        (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom) := by
  -- Compare both stalk morphisms after precomposing with every germ from `X.presheaf`.
  refine X.presheaf.stalk_hom_ext fun U hxU ↦ ?_
  calc
    X.presheaf.germ U ((pointInclusion x).hom.base PUnit.unit) hxU ≫
        (pointInclusion x).hom.stalkMap PUnit.unit ≫ (pointRingedSpaceStalkIso (x := x)).hom
      =
        (pointInclusion x).hom.c.app (Opposite.op U) ≫
          (pointRingedSpace x).presheaf.germ
            ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) PUnit.unit hxU ≫
            (pointRingedSpaceStalkIso (x := x)).hom := by
          -- The first step is the general stalk-map/germ compatibility.
          simpa [Category.assoc] using
            congrArg (fun k => k ≫ (pointRingedSpaceStalkIso (x := x)).hom)
              (PresheafedSpace.stalkMap_germ
                (α := (pointInclusion x).hom) (U := U) (x := PUnit.unit) hxU)
    _ =
        X.presheaf.germ U ((pointInclusion x).hom.base PUnit.unit) hxU ≫
          StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
            (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom) := by
          have hxU' : x ∈ U := by
            -- Rewrite the stalk-extensionality binder to the ambient point spelling used by
            -- `germ_fromStalk`.
            simpa [pointInclusion_hom_base_apply] using hxU
          have hsection :
              (pointInclusion x).hom.c.app (Opposite.op U) ≫
                  (pointRingedSpace x).presheaf.germ
                    ((TopologicalSpace.Opens.map (pointInclusion x).hom.base).obj U) PUnit.unit
                    hxU ≫
                  (pointRingedSpaceStalkIso (x := x)).hom
                =
                  (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom.app
                    (Opposite.op U)) ≫
                    eqToHom (if_pos hxU') := by
            -- First align the point-inclusion section map with the normal form used by
            -- the stalk/skyscraper adjunction.
            simpa [pointInclusion_hom_base_apply] using
              (pointInclusionSectionApp_comp_germ_comp_pointRingedSpaceStalkIso_hom
                (x := x) (U := U) hxU')
          have hfromStalk :
              (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom.app
                  (Opposite.op U)) ≫
                eqToHom (if_pos hxU') =
              X.presheaf.germ U ((pointInclusion x).hom.base PUnit.unit) hxU ≫
                StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
                  (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom) := by
            -- Then apply the standard adjunction computation in the same spelling world.
            simpa [Category.assoc, pointInclusion_hom_base_apply] using
              (StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk
                (p₀ := x)
                (f := ((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom)
                (U := U)
                (hU := hxU')).symm
          exact hsection.trans hfromStalk

/-- The point inclusion `i_x : ({x}, \mathcal O_{X, x}) ⟶ (X, \mathcal O_X)` is flat. -/
theorem pointInclusion_isFlat {X : RingedSpace.{u}} (x : X) :
    RingedSpace.Hom.IsFlat (pointInclusion x) := by
  classical
  letI : (U : TopologicalSpace.Opens ↑↑X.toPresheafedSpace) → Decidable (x ∈ U) :=
    fun U ↦ Classical.propDecidable (x ∈ U)
  letI : (U : TopologicalSpace.Opens (TopCat.of PUnit)) → Decidable (PUnit.unit ∈ U) :=
    fun U ↦ Classical.propDecidable (PUnit.unit ∈ U)
  refine ⟨fun y ↦ ?_⟩
  -- Reduce the stalkwise flatness check to the unique point of `pointRingedSpace x`.
  cases y
  -- Route correction: identify the point-space stalk with `X.presheaf.stalk x`, then use the
  -- adjunction unit/counit normalization instead of unfolding the unavailable owner name.
  have hfrom :
      StalkSkyscraperPresheafAdjunctionAuxs.fromStalk x
          (((stalkSkyscraperSheafAdjunction x).unit.app X.sheaf).hom) =
        𝟙 (X.presheaf.stalk x) := by
    -- The unit of the stalk/skyscraper adjunction is `toSkyscraperPresheaf` of the identity.
    simpa [StalkSkyscraperPresheafAdjunctionAuxs.unit_app] using
      (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper
        (p₀ := x) (f := 𝟙 (X.presheaf.stalk x)))
  have hEq :
      ((pointInclusion x).hom.stalkMap PUnit.unit) = (pointRingedSpaceStalkIso (x := x)).inv := by
    -- The canonical stalk identification turns the point-inclusion stalk map into the identity.
    apply (cancel_mono (pointRingedSpaceStalkIso (x := x)).hom).1
    rw [pointInclusionStalkMap_comp_pointRingedSpaceStalkIso_hom (x := x), hfrom,
      ← Iso.inv_hom_id (pointRingedSpaceStalkIso (x := x))]
    rfl
  -- Flatness is invariant under bijective ring maps, and the inverse of an isomorphism is
  -- bijective.
  rw [RingedSpace.Hom.FlatAt, hEq]
  simpa using
    RingHom.Flat.of_bijective
      (pointRingedSpaceStalkIso (x := x)).symm.commRingCatIsoToRingEquiv.bijective

end AlgebraicGeometry

namespace Scheme.Hom

open RingedSpace.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Under the scheme specialization, the ringed-space flatness owner agrees with mathlib's
canonical scheme-theoretic flatness predicate. -/
theorem isFlat_iff_flat :
    IsFlat f.toLRSHom.toShHom ↔ Flat f := by
  rw [Flat.iff_flat_stalkMap]
  constructor
  · intro hf x
    simpa using hf.flatAt x
  · intro hf
    exact ⟨fun x ↦ by simpa using hf x⟩

instance [Flat f] : IsFlat f.toLRSHom.toShHom :=
  (isFlat_iff_flat f).2 inferInstance

instance [IsFlat f.toLRSHom.toShHom] : Flat f :=
  (isFlat_iff_flat f).1 inferInstance

end Scheme.Hom
