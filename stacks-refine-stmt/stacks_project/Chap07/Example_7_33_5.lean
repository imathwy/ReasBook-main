import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat
open TopologicalSpace
open CategoryTheory.Limits
open Opposite

universe u v

namespace CategoryTheory

open GrothendieckTopology.Point.Hom
open GrothendieckTopology.Point.ofIsCofiltered

variable {X : TopCat.{u}}

/- Domain-style sampling for Example 7.33.5:
- primary domain: points of the opens site of a topological space and the identification of their
  site-theoretic fibers with ordinary stalks;
- sampled owner API:
  `Opens.pointGrothendieckTopology`,
  `GrothendieckTopology.Point.ofIsCofiltered`,
  `TopCat.Presheaf.stalk`,
  `GrothendieckTopology.Point.Hom.presheafFiber`;
- source/core/bridge triage:
  `source-facing`: the textbook point of `X_{Zar}` attached to `x` together with its fiber and
    stalk descriptions;
  `core/canonical`: `Opens.pointGrothendieckTopology x` and `TopCat.Presheaf.stalk`;
  `bridge/view`: the neighborhood-site point built from `OpenNhds.inclusion x` and the resulting
    comparison isomorphism on presheaf fibers.

Primitive data are only the point `x`, the neighborhood inclusion functor, and the presheaf/sheaf
whose fiber is being computed. The singleton-or-empty description of fibers is derived API from
the canonical point owner, while the stalk comparison is a bridge from the site point to the
usual neighborhood-colimit presentation of stalks.
-/

@[simp] theorem Opens.pointGrothendieckTopology_fiber_nonempty_iff (x : X) (U : Opens X) :
    Nonempty ((Opens.pointGrothendieckTopology x).fiber.obj U) ↔ x ∈ U := by
  simp [Opens.pointGrothendieckTopology]

theorem Opens.pointGrothendieckTopology_fiber_isEmpty (x : X) (U : Opens X) (hx : x ∉ U) :
    IsEmpty ((Opens.pointGrothendieckTopology x).fiber.obj U) := by
  refine ⟨fun t ↦ hx t.down.down⟩

/- Example 7.33.5: for a point `x : X`, the corresponding point of the opens site `X_{Zar}` is
the canonical mathlib point `Opens.pointGrothendieckTopology x`. Its fiber over an open `U` is
empty when `x ∉ U` and nonempty exactly when `x ∈ U`; the singleton claim then follows from the
upstream instance `Subsingleton ((Opens.pointGrothendieckTopology x).fiber.obj U)`. The companion
declarations here are `Opens.pointGrothendieckTopology_fiber_isEmpty` and
`Opens.pointGrothendieckTopology_fiber_nonempty_iff`. -/
recall Opens.pointGrothendieckTopology

private instance (x : X) : InitiallySmall.{u} (OpenNhds x) :=
  initiallySmall_of_essentiallySmall (OpenNhds x)

private theorem openNhdsInclusion_coverLift (x : X) :
    ∀ ⦃U : Opens X⦄ (R : Sieve U) (_ : R ∈ Opens.grothendieckTopology X U)
      ⦃V : OpenNhds x⦄ (f : (OpenNhds.inclusion x).obj V ⟶ U),
      ∃ (Y : Opens X) (g : Y ⟶ U) (_ : R g) (W : OpenNhds x) (q : W ⟶ V)
        (a : (OpenNhds.inclusion x).obj W ⟶ Y),
        a ≫ g = (OpenNhds.inclusion x).map q ≫ f := by
  intro U R hR V f
  obtain ⟨Y, g, hg, hy⟩ := hR x (f.le V.2)
  let Yx : OpenNhds x := ⟨Y, hy⟩
  refine ⟨Y, g, hg, Yx ⊓ V, OpenNhds.infLERight Yx V, OpenNhds.infLELeft Yx V, ?_⟩
  subsingleton

private noncomputable def openNhdsPoint (x : X) :
    (Opens.grothendieckTopology X).Point :=
  GrothendieckTopology.Point.ofIsCofiltered
    (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x)

private noncomputable def pointGrothendieckTopology_hom_openNhdsPoint (x : X) :
    Opens.pointGrothendieckTopology x ⟶ openNhdsPoint x where
  hom.app U z := by
    classical
    let z' : (fiber (OpenNhds.inclusion x)).obj U := by
      simpa [openNhdsPoint, GrothendieckTopology.Point.ofIsCofiltered] using z
    let hsurj := fiberMk_jointly_surjective z'
    let V := Classical.choose hsurj
    let f := Classical.choose (Classical.choose_spec hsurj)
    exact ULift.up (PLift.up (f.le V.2))
  hom.naturality _ _ _ := by
    ext z
    subsingleton

private noncomputable def openNhdsPoint_hom_pointGrothendieckTopology (x : X) :
    openNhdsPoint x ⟶ Opens.pointGrothendieckTopology x where
  hom.app U z := by
    change ULift (PLift (x ∈ U)) at z
    let Ux : OpenNhds x := ⟨U, z.down.down⟩
    exact fiberMk (show (OpenNhds.inclusion x).obj Ux ⟶ U from 𝟙 U)
  hom.naturality _ _ _ := by
    ext z
    subsingleton

private noncomputable def pointGrothendieckTopologyIsoOpenNhdsPoint (x : X) :
    Opens.pointGrothendieckTopology x ≅ openNhdsPoint x where
  hom := pointGrothendieckTopology_hom_openNhdsPoint x
  inv := openNhdsPoint_hom_pointGrothendieckTopology x
  hom_inv_id := by
    ext U z
    subsingleton
  inv_hom_id := by
    ext U z
    subsingleton

section

variable {C : Type v} [Category.{u} C] [HasColimits C]

private noncomputable def pointGrothendieckTopology_presheafFiber_iso_openNhdsPoint
    (x : X) :
    ((Opens.pointGrothendieckTopology x).presheafFiber : X.Presheaf C ⥤ C) ≅
      ((openNhdsPoint x).presheafFiber : X.Presheaf C ⥤ C) where
  hom := (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv.presheafFiber
  inv := (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom.presheafFiber
  hom_inv_id := by
    calc
      (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv.presheafFiber ≫
          (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom.presheafFiber =
          ((pointGrothendieckTopologyIsoOpenNhdsPoint x).hom ≫
              (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv).presheafFiber := by
            exact
              (presheafFiber_comp
                (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom
                (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv).symm
      _ = presheafFiber (𝟙 (Opens.pointGrothendieckTopology x)) := by
        rw [(pointGrothendieckTopologyIsoOpenNhdsPoint x).hom_inv_id]
      _ = 𝟙 (((Opens.pointGrothendieckTopology x).presheafFiber : X.Presheaf C ⥤ C)) := by
        exact presheafFiber_id (Opens.pointGrothendieckTopology x)
  inv_hom_id := by
    calc
      (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom.presheafFiber ≫
          (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv.presheafFiber =
          ((pointGrothendieckTopologyIsoOpenNhdsPoint x).inv ≫
              (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom).presheafFiber := by
            exact
              (presheafFiber_comp
                (pointGrothendieckTopologyIsoOpenNhdsPoint x).inv
                (pointGrothendieckTopologyIsoOpenNhdsPoint x).hom).symm
      _ = presheafFiber (𝟙 (openNhdsPoint x)) := by
        rw [(pointGrothendieckTopologyIsoOpenNhdsPoint x).inv_hom_id]
      _ = 𝟙 (((openNhdsPoint x).presheafFiber : X.Presheaf C ⥤ C)) := by
        exact presheafFiber_id (openNhdsPoint x)

private noncomputable def openNhdsPoint_presheafFiber_iso_stalkFunctor
    (x : X) :
    ((openNhdsPoint x).presheafFiber : X.Presheaf C ⥤ C) ≅ TopCat.Presheaf.stalkFunctor C x :=
  NatIso.ofComponents
    (fun P ↦
      IsColimit.coconePointUniqueUpToIso
        (GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone
          (OpenNhds.inclusion x) (openNhdsInclusion_coverLift x) P)
        (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ P)))
    (fun {P Q} g ↦ by
      sorry)

noncomputable def pointGrothendieckTopology_presheafFiber_iso_stalkFunctor
    (x : X) :
    ((Opens.pointGrothendieckTopology x).presheafFiber : X.Presheaf C ⥤ C) ≅
      TopCat.Presheaf.stalkFunctor C x :=
  pointGrothendieckTopology_presheafFiber_iso_openNhdsPoint x ≪≫
    openNhdsPoint_presheafFiber_iso_stalkFunctor x

noncomputable def pointGrothendieckTopology_presheafFiber_obj_iso_stalk
    (x : X) (P : X.Presheaf C) :
    (((Opens.pointGrothendieckTopology x).presheafFiber : X.Presheaf C ⥤ C)).obj P ≅
      TopCat.Presheaf.stalk P x :=
  (pointGrothendieckTopology_presheafFiber_iso_stalkFunctor x).app P

noncomputable def pointGrothendieckTopology_sheafFiber_obj_iso_stalk
    (x : X) (F : X.Sheaf C) :
    (((Opens.pointGrothendieckTopology x).sheafFiber : X.Sheaf C ⥤ C)).obj F ≅
      TopCat.Presheaf.stalk F.presheaf x :=
  (Functor.isoWhiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X) C)
    (pointGrothendieckTopology_presheafFiber_iso_stalkFunctor x)).app F

end

/- The associated textbook stalk is the usual stalk of a presheaf on `X`, formalized in mathlib as
`TopCat.Presheaf.stalk`. For the canonical opens-site point `Opens.pointGrothendieckTopology x`,
the main comparison is the natural isomorphism
`pointGrothendieckTopology_presheafFiber_iso_stalkFunctor`, whose componentwise presheaf and sheaf
forms are `pointGrothendieckTopology_presheafFiber_obj_iso_stalk` and
`pointGrothendieckTopology_sheafFiber_obj_iso_stalk`. -/
recall TopCat.Presheaf.stalk

end CategoryTheory
