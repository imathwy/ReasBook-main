import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_15_2
import StacksProject_2024.Chap07.Lemma_7_32_7
import StacksProject_2024.Chap07.Lemma_7_34_3

open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor
open GrothendieckTopology
open GrothendieckTopology.Point

universe u v w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.32.8:
- primary domain: points of Grothendieck sites and the induced points of the associated topoi;
- sampled owner API:
  `GrothendieckTopology.Point.comap`,
  `Point.sheafFiberComapIso`,
  `MorphismOfTopoiIn.typePushforward`,
  `MorphismOfTopoiIn.typeInverseImage`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`, together with the
  topos-point bridge functors `typePushforward` and `typeInverseImage` from Definition 7.32.1;
- source/core/bridge triage:
  `source-facing`: the fiber functor of a site point `p : J.Point` and the induced composite
    point of `Sh(C)`;
  `core/canonical`: the mathlib/project owners `Point.comap`, `Point.sheafFiberComapIso`, and the
    chapter bridge owners `MorphismOfTopoiIn.typePushforward` / `typeInverseImage`;
  `bridge/view`: the comparison isomorphisms identifying the composite point determined by
    `p.fiber` with `p.toToposPoint`.

Primitive data are only the site point `p`. Continuity, representable flatness, and the
`IsMorphismOfSites` structure on `p.fiber` are derived from that owner data, while the two
comparison isomorphisms should be stated on the canonical `typePushforward` / `typeInverseImage`
surface rather than on their expanded `typeEquiv`-whiskered formulas.
-/

/- Lemma 7.32.8 (1): after replacing the powerset site from Remark 7.15.3 by the canonically
equivalent jointly surjective site on `Type`, the corresponding sheaf category is equivalent to
`Sh(pt)`, identified here with `Type`, via the standard equivalence `typeEquiv`. -/
recall typeEquiv : Type w ≌ Sheaf typesGrothendieckTopology (Type w)

instance (p : Point.{w} J) :
    Functor.IsContinuous p.fiber J typesGrothendieckTopology := sorry

instance (p : Point.{w} J) :
    RepresentablyFlat p.fiber := sorry

/-
Lemma 7.32.8 (2): for a point `p` of the site `(C, J)`, the underlying fiber functor
`p.fiber : C ⥤ Type` defines a morphism of sites from the canonical surjective site on `Type`
to `(C, J)`.
-/
instance (p : Point.{w} J) :
    IsMorphismOfSites J typesGrothendieckTopology p.fiber := by
  infer_instance

private theorem pointFiber_typesSite_coverPreserving
    (p : Point.{w} J) :
    CoverPreserving J typesGrothendieckTopology p.fiber :=
  ⟨fun {X} {S} hS x ↦ by
    rcases p.jointly_surjective S hS x with ⟨Y, f, hf, y, hy⟩
    exact ⟨Y, f, fun _ ↦ y, hf, funext fun _ ↦ hy.symm⟩⟩

section

variable (p : Point.{w} J)
variable [LocallySmall.{w} C]
variable [HasSheafify J (Type w)]
variable [HasSheafify typesGrothendieckTopology (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, HasLeftKanExtension p.fiber.op P]
variable [PreservesFiniteLimits
  (lan p.fiber.op : (Cᵒᵖ ⥤ Type w) ⥤ Type wᵒᵖ ⥤ Type w)]

-- Proof sketch: clause (2) yields a morphism of topoi from sheaves on the canonical type site to
-- `Sh(C)`, and composing this with the canonical point of `Sh(pt)` coming from `typeEquiv`
-- produces the point `p.toToposPoint` from Lemma 7.32.7. The companion isomorphism identifies
-- the inverse-image functor of the composite with that of `p.toToposPoint`.
/-- Lemma 7.32.8: after identifying `Sh(pt)` with sheaves on `Type` via `typeEquiv`, the
composite of the morphism of topoi induced by `p.fiber` with this canonical point of `Sh(pt)` is
canonically identified with the point `p.toToposPoint` of `Sh(C)`. -/
noncomputable def pointFiber_typesSite_compositeToposPoint_pushforwardIso
    :
    (((p.fiber.morphismOfTopoiInOfContinuous J typesGrothendieckTopology).comp
        (MorphismOfTopoiIn.id typesGrothendieckTopology)).typePushforward ≅
      (p.toToposPoint).typePushforward) := by
  change typeEquiv.{w}.functor ⋙
      p.fiber.sheafPushforwardContinuous (Type w) J typesGrothendieckTopology ≅
    (p.toToposPoint).typePushforward
  let hcover : CoverPreserving J typesGrothendieckTopology p.fiber :=
    pointFiber_typesSite_coverPreserving p
  letI : InitiallySmall (p.fiber ⋙ typesPoint.fiber).Elements := by
    change InitiallySmall p.fiber.Elements
    infer_instance
  have hcomap : typesPoint.comap p.fiber hcover = p :=
    typesPoint_comap_eq p hcover
  simpa [hcomap, toToposPoint] using
    Functor.isoWhiskerRight typesPointSkyscraperSheafFunctorIso
      (p.fiber.sheafPushforwardContinuous (Type w) J typesGrothendieckTopology) ≪≫
      typesPoint.skyscraperSheafFunctorCompSheafPushforwardContinuous
        p.fiber hcover (Type w) ≪≫
      (toToposPoint_pointPushforwardIso p).symm

-- Proof sketch: the comparison produced by `pointFiber_typesSite_compositeToposPoint_pushforwardIso`
-- is itself an isomorphism, so its forward natural transformation is an isomorphism.
/-- The forward natural transformation in Lemma 7.32.8 is an isomorphism. -/
theorem pointFiber_typesSite_compositeToposPoint_pushforwardIso_hom_isIso :
    IsIso (pointFiber_typesSite_compositeToposPoint_pushforwardIso p).hom := sorry

/-- The inverse-image functor of the composite point from Lemma 7.32.8 is canonically
identified with the inverse-image functor of `p.toToposPoint`. -/
noncomputable def pointFiber_typesSite_compositeToposPoint_inverseImageIso
    :
    (((p.fiber.morphismOfTopoiInOfContinuous J typesGrothendieckTopology).comp
        (MorphismOfTopoiIn.id typesGrothendieckTopology)).typeInverseImage ≅
      (p.toToposPoint).typeInverseImage) := by
  change p.fiber.sheafPullback (Type w) J typesGrothendieckTopology ⋙ typeEquiv.{w}.inverse ≅
    (p.toToposPoint).typeInverseImage
  let hcover : CoverPreserving J typesGrothendieckTopology p.fiber :=
    pointFiber_typesSite_coverPreserving p
  letI : InitiallySmall (p.fiber ⋙ typesPoint.fiber).Elements := by
    change InitiallySmall p.fiber.Elements
    infer_instance
  have hcomap : typesPoint.comap p.fiber hcover = p :=
    typesPoint_comap_eq p hcover
  simpa [hcomap] using
    (Functor.isoWhiskerLeft (p.fiber.sheafPullback (Type w) J typesGrothendieckTopology)
      typesPointSheafFiberIso).symm ≪≫
      (sheafFiberComapIso typesPoint p.fiber hcover (Type w)).symm ≪≫
      (toToposPoint_pointInverseImageIso p).symm

end

end CategoryTheory
