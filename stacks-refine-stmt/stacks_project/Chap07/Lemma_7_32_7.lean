import Mathlib
import stacks_project.Chap07.Definition_7_32_1
import stacks_project.Chap07.Remark_7_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor

universe u v w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn
open scoped GrothendieckTopology.SheafifiedRepresentable

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

/-- A point of the site `(C, J)` canonically defines a point of the topos `Sh(C)`. -/
noncomputable def toToposPoint
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    MorphismOfTopoiIn J typesGrothendieckTopology.{w} where
  inverseImageFunctor :=
    let _ : PreservesFiniteLimits (p.sheafFiber ⋙ typeEquiv.{w}.functor) := inferInstance
    LeftExactFunctor.of (p.sheafFiber ⋙ typeEquiv.{w}.functor)
  pushforward := typeEquiv.{w}.inverse ⋙ p.skyscraperSheafFunctor
  adjunction := p.skyscraperSheafAdjunction.comp typeEquiv.{w}.toAdjunction

/-- The `Type`-valued inverse-image functor of the point induced by a site point recovers the
usual stalk functor. -/
noncomputable def toToposPoint_pointInverseImageIso
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    p.toToposPoint.typeInverseImage ≅ p.sheafFiber :=
  (Functor.associator p.sheafFiber typeEquiv.{w}.functor typeEquiv.{w}.inverse).symm ≪≫
    (Functor.isoWhiskerLeft p.sheafFiber typeEquiv.{w}.unitIso.symm) ≪≫
      Functor.rightUnitor p.sheafFiber

/-- The `Type`-valued direct-image functor of the point induced by a site point recovers the
usual skyscraper functor. -/
noncomputable def toToposPoint_pointPushforwardIso
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    p.toToposPoint.typePushforward ≅ p.skyscraperSheafFunctor :=
  (Functor.associator typeEquiv.{w}.functor typeEquiv.{w}.inverse p.skyscraperSheafFunctor).symm ≪≫
    (Functor.isoWhiskerRight typeEquiv.{w}.unitIso.symm p.skyscraperSheafFunctor) ≪≫
      Functor.leftUnitor p.skyscraperSheafFunctor

/-- The canonical point of the jointly surjective site on `Type`. -/
noncomputable def typesPoint : Point.{w} typesGrothendieckTopology.{w} where
  fiber := 𝟭 (Type w)
  jointly_surjective {X} R hR x :=
    ⟨PUnit, fun _ ↦ x, hR x, PUnit.unit, rfl⟩

private noncomputable abbrev typesPointBaseObj : typesPoint.fiber.Elements :=
  typesPoint.fiber.elementsMk PUnit PUnit.unit

private instance (Y : typesPoint.fiber.Elements) : Unique (typesPointBaseObj ⟶ Y) := by
  let g : typesPointBaseObj ⟶ Y := ⟨fun _ ↦ Y.2, rfl⟩
  refine { default := g, uniq := ?_ }
  intro f
  apply CategoryOfElements.ext typesPoint.fiber f g
  funext u
  cases u
  simpa [g] using f.2

private noncomputable def typesPointInitial : IsInitial typesPointBaseObj :=
  IsInitial.ofUnique _

private noncomputable abbrev typesPointTerminalObj : typesPoint.fiber.Elementsᵒᵖ :=
  op typesPointBaseObj

private noncomputable def typesPointTerminal : IsTerminal typesPointTerminalObj :=
  terminalOpOfInitial typesPointInitial

private noncomputable def typesPointPresheafFiberObjIso (P : Type wᵒᵖ ⥤ Type w) :
    typesPoint.presheafFiber.obj P ≅ P.obj (op PUnit) := by
  let Q := (CategoryOfElements.π typesPoint.fiber).op ⋙ P
  change colimit Q ≅ Q.obj typesPointTerminalObj
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal typesPointTerminal Q)

private lemma toPresheafFiber_typesPointPresheafFiberObjIso_hom
    (P : Type wᵒᵖ ⥤ Type w) (X : Type w) (x : X) :
    typesPoint.toPresheafFiber X x P ≫ (typesPointPresheafFiberObjIso P).hom =
      P.map (show PUnit ⟶ X from fun _ ↦ x).op := by
  simpa [typesPointPresheafFiberObjIso, GrothendieckTopology.Point.presheafFiber,
    typesPointTerminalObj, typesPointTerminal] using
    (colimit.comp_coconePointUniqueUpToIso_hom
      (hc := colimitOfDiagramTerminal typesPointTerminal
        ((CategoryOfElements.π typesPoint.fiber).op ⋙ P))
      (op (typesPoint.fiber.elementsMk X x)))

private noncomputable def typesPointPresheafFiberIso :
    typesPoint.presheafFiber ≅ (evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit) := by
  refine NatIso.ofComponents (fun P ↦ typesPointPresheafFiberObjIso P) ?_
  intro P Q f
  apply typesPoint.presheafFiber_hom_ext
  intro X x
  rw [toPresheafFiber_naturality_assoc]
  calc
    (f.app (op X) ≫ typesPoint.toPresheafFiber X x Q) ≫ (typesPointPresheafFiberObjIso Q).hom =
        f.app (op X) ≫
          (typesPoint.toPresheafFiber X x Q ≫ (typesPointPresheafFiberObjIso Q).hom) := by
            simp [Category.assoc]
    _ = f.app (op X) ≫ Q.map (show PUnit ⟶ X from fun _ ↦ x).op := by
      rw [toPresheafFiber_typesPointPresheafFiberObjIso_hom]
    _ = P.map (show PUnit ⟶ X from fun _ ↦ x).op ≫
          ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f := by
            simpa using
              (NatTrans.naturality f
                (show op X ⟶ op PUnit from (show PUnit ⟶ X from fun _ ↦ x).op)).symm
    _ = typesPoint.toPresheafFiber X x P ≫ (typesPointPresheafFiberObjIso P).hom ≫
          ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  k ≫ ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f)
                (toPresheafFiber_typesPointPresheafFiberObjIso_hom P X x).symm

/-- The sheaf fiber of the canonical point on the jointly surjective site of types is evaluation
at `PUnit`, i.e. `typeEquiv.inverse`. -/
noncomputable def typesPointSheafFiberIso :
    typesPoint.sheafFiber ≅ typeEquiv.{w}.inverse := by
  simpa [GrothendieckTopology.Point.sheafFiber] using
    Functor.isoWhiskerLeft (sheafToPresheaf typesGrothendieckTopology (Type w))
      typesPointPresheafFiberIso

/-- The skyscraper functor of the canonical point on the jointly surjective site of types is the
canonical equivalence `typeEquiv.functor`. -/
noncomputable def typesPointSkyscraperSheafFunctorIso :
    typeEquiv.{w}.functor ≅ typesPoint.skyscraperSheafFunctor :=
  (conjugateIsoEquiv typeEquiv.{w}.symm.toAdjunction typesPoint.skyscraperSheafAdjunction)
    typesPointSheafFiberIso

/-- Comapping the canonical point of the jointly surjective site of types along the fiber functor
of a site point recovers the original point. -/
theorem typesPoint_comap_eq
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    (p : Point.{w} K)
    [RepresentablyFlat p.fiber]
    (hcover : CoverPreserving K typesGrothendieckTopology p.fiber)
    [InitiallySmall (p.fiber ⋙ typesPoint.fiber).Elements] :
    typesPoint.comap p.fiber hcover = p := by
  apply
    (show
      (typesPoint.comap p.fiber hcover = p) =
        ((typesPoint.comap p.fiber hcover).fiber = p.fiber) from
          mk.injEq _ _ _ _ _ _ _ _).mpr
  rfl

end GrothendieckTopology.Point

/- Lemma 7.32.7 (1): a point of the site `(C, J)` canonically defines a point of the topos
`Sh(C)`, and the inverse-image functor of the resulting point of the topos is the stalk functor. -/
#check GrothendieckTopology.Point.toToposPoint_pointInverseImageIso

-- Proof sketch: apply the inverse-image functor of the given topos point to the sheafified
-- representables `h_U^#` to obtain the site fiber functor `U ↦ p^{-1}(h_U^#)`, then prove this
-- functor is a site point and that its sheaf fiber recovers the original inverse-image functor.
namespace MorphismOfTopoiIn

open GrothendieckTopology.Point

/- Domain-style sampling for Lemma 7.32.7 (2):
- primary domain: points of a site and points of the associated topos, organized around the
  sheafified-representable owner layer and inverse image of points along a site morphism;
- sampled owner declarations:
  `GrothendieckTopology.Point.typesPoint`,
  `GrothendieckTopology.sheafifiedRepresentableFunctor`,
  `GrothendieckTopology.Point.comap`,
  `GrothendieckTopology.Point.sheafFiberComapIso`,
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.toToposPoint_pointInverseImageIso`;
- source/core/bridge triage:
  `source-facing`: the site point attached to a topos point by the fibers `U ↦ p^{-1}(h[U]^#[J])`;
  `core/canonical`: the chapter owners `J.sheafifiedRepresentableFunctor`, `p.typeInverseImage`,
  and `GrothendieckTopology.Point.comap`;
  `bridge/view`: the composite `J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage`, together
  with the comparison isomorphism identifying the resulting site-point sheaf fiber with the
  original inverse-image functor.

Primitive data are only the topos point `p`; the functor `U ↦ p^{-1}(h[U]^#[J])` is derived API
from the existing owners `J.sheafifiedRepresentableFunctor` and `p.typeInverseImage`, and the
associated site point should be built through the canonical point-comap owner rather than by
restating the primitive `Point` fields. -/

private theorem typePresentationFunctor_coverPreserving
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    CoverPreserving J typesGrothendieckTopology
      (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage) := by
  sorry

private instance typePresentationFunctor_representablyFlat
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    RepresentablyFlat (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage) := by
  sorry

private instance typePresentationFunctor_comap_initiallySmall
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    InitiallySmall.{max u v}
      ((J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage) ⋙ typesPoint.fiber).Elements := by
  change
    InitiallySmall.{max u v} (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements
  classical
  exact initiallySmall_of_essentiallySmall _

/-- For a point `p` of the topos `Sh(C)`, the functor `U ↦ p^{-1}(h_U^#)` defines the
associated point of the site `(C, J)`. -/
noncomputable def toSitePoint
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    GrothendieckTopology.Point.{max u v} J :=
  typesPoint.comap (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage)
    (typePresentationFunctor_coverPreserving p)

/-- Lemma 7.32.7: for a point `p` of the topos `Sh(C)`, the functor
`U ↦ p^{-1}(h_U^#)` defines a point of the site `(C, J)`, and the stalk functor of that site
point recovers the inverse-image functor of `p`. -/
noncomputable def toSitePoint_sheafFiberIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    p.toSitePoint.sheafFiber ≅ p.typeInverseImage := sorry

-- Proof sketch: evaluate the canonical natural isomorphism
-- `p.toSitePoint_sheafFiberIso` on a sheaf and use the identity law for isomorphisms.
/-- The component of `toSitePoint_sheafFiberIso` followed by its inverse is the identity. -/
theorem toSitePoint_sheafFiberIso_hom_inv_app
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (F : Sheaf J (Type (max u v))) :
    (p.toSitePoint_sheafFiberIso).hom.app F ≫ (p.toSitePoint_sheafFiberIso).inv.app F =
      𝟙 _ := sorry

end MorphismOfTopoiIn

end CategoryTheory
