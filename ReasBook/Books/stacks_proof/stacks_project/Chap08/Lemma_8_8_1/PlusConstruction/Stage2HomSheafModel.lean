import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage2HomSheafBridge

universe u v uX vX w

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace LocallyDefinedHomTotal

/-- Transport a Type-valued functor through objectwise equivalences.

This is a purely functorial helper: the maps of the transported functor are defined by
conjugating the original functor maps by the chosen objectwise equivalences. -/
noncomputable def conjugateFunctorByObjEquiv {D : Type u} [Category.{v} D]
    (P : D ⥤ Type w) (M : D → Type w) (e : ∀ X, P.obj X ≃ M X) :
    D ⥤ Type w where
  obj X := M X
  map {X Y} f s := e Y (P.map f ((e X).symm s))
  map_id := by
    intro X
    funext s
    simp only [Functor.map_id]
    exact Equiv.apply_symm_apply (e X) s
  map_comp := by
    intro X Y Z f g
    funext s
    simp only [Functor.map_comp]
    change (e Z) (P.map g (P.map f ((e X).symm s))) =
      (e Z) (P.map g ((e Y).symm ((e Y) (P.map f ((e X).symm s)))))
    rw [Equiv.symm_apply_apply]

/-- The original functor is naturally isomorphic to its objectwise-equivalence conjugate. -/
noncomputable def conjugateFunctorByObjEquivIso {D : Type u} [Category.{v} D]
    (P : D ⥤ Type w) (M : D → Type w) (e : ∀ X, P.obj X ≃ M X) :
    P ≅ conjugateFunctorByObjEquiv P M e := by
  refine NatIso.ofComponents (fun X => (e X).toIso) ?_
  intro X Y f
  funext s
  change (e Y) (P.map f s) = (e Y) (P.map f ((e X).symm ((e X) s)))
  rw [Equiv.symm_apply_apply]

/-- Any object of a slice is canonically isomorphic to the `Over.mk` object built from its
displayed structure morphism.

This small owner bridge lets the source-text stage 2.8 calculation first work over
`Over.mk f`, where `Pseudofunctor.overMapCompPresheafHomIso` applies cleanly, and then transport
back to an arbitrary test object of the slice site. -/
noncomputable def overObjectMkIso {U : C} (T : Over U) : T ≅ Over.mk T.hom :=
  Over.isoMk (Iso.refl T.left) (by simp)

/-- The source-text plus model for a stage-2 Hom section at a displayed base arrow
`f : V ⟶ U`.

After pulling `x` and `y` back along `f` using the canonical fiber pseudofunctor of the source
stage-2 projection, the model is the fixed-base plus section attached to those pulled-back
objects.  This is only the pointwise model; the presheaf-level naturality is the separate
owner-sensitive stage 2.8 bridge. -/
noncomputable def sourceStage2HomSheafModelObjAtBaseArrow
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U V : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U)
    (f : V ⟶ U) : Type _ :=
  let F := canonicalFiberPseudofunctor (pointwiseSourceFibredCategory (J := J) X).p
  let xV := (F.map f.op.toLoc).toFunctor.obj x
  let yV := (F.map f.op.toLoc).toFunctor.obj y
  ((J.over (X.p.obj xV.1.obj)).plusObj
    (locallyDefinedHomSaturatedPresheaf X
      (eqToHom xV.2 ≫ 𝟙 V ≫ eqToHom yV.2.symm))).obj
    (op (Over.mk (𝟙 (X.p.obj xV.1.obj))))

/-- Pointwise stage 2.8 comparison over a displayed base arrow.

The comparison is the composite of:
* the identity-slice transport `Over.mk f`;
* `Pseudofunctor.overMapCompPresheafHomIso`, which identifies sections over `f` with Hom
  sections between the pulled-back fiber objects;
* the canonical identity-slice Hom equivalence;
* `sourceProjectionFiberHomFixedBaseEquiv`, the fixed-base plus description.

This is deliberately not packaged as a natural isomorphism of presheaves.  That naturality is
the remaining owner-sensitive part of stage 2.8. -/
noncomputable def sourceStage2HomSheafModelObjAtBaseArrowEquiv
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U V : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U)
    (f : V ⟶ U) :
    let F := canonicalFiberPseudofunctor (pointwiseSourceFibredCategory (J := J) X).p
    ((F.presheafHom x y).obj (op (Over.mk f))) ≃
      sourceStage2HomSheafModelObjAtBaseArrow (J := J) X x y f := by
  let F := canonicalFiberPseudofunctor (pointwiseSourceFibredCategory (J := J) X).p
  let xV := (F.map f.op.toLoc).toFunctor.obj x
  let yV := (F.map f.op.toLoc).toFunctor.obj y
  let e₀ : (F.presheafHom x y).obj (op (Over.mk f)) ≃
      ((Over.map f).op ⋙ F.presheafHom x y).obj (op (Over.mk (𝟙 V))) :=
    CategoryTheory.Iso.toEquiv ((F.presheafHom x y).mapIso (overMapIdentitySliceIso f).op)
  let e₁ : (F.presheafHom x y).obj (op (Over.mk f)) ≃
      (F.presheafHom xV yV).obj (op (Over.mk (𝟙 V))) :=
    e₀.trans
      (CategoryTheory.Iso.toEquiv
        ((F.overMapCompPresheafHomIso x y f).app (op (Over.mk (𝟙 V)))))
  exact e₁.trans
    ((F.presheafHomObjHomEquiv (M := xV) (N := yV)).symm.trans
      (sourceProjectionFiberHomFixedBaseEquiv (J := J) X (U := V) xV yV))

/-- The same pointwise source-text plus model at an arbitrary slice test object. -/
noncomputable def sourceStage2HomSheafModelObj
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U)
    (T : Over U) : Type _ :=
  sourceStage2HomSheafModelObjAtBaseArrow (J := J) X x y T.hom

/-- Pointwise stage 2.8 comparison at an arbitrary slice test object.

The only additional step from `sourceStage2HomSheafModelObjAtBaseArrowEquiv` is transporting the
test object `T` to the definitional `Over.mk T.hom` owner. -/
noncomputable def sourceStage2HomSheafModelObjEquiv
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U)
    (T : Over U) :
    let F := canonicalFiberPseudofunctor (pointwiseSourceFibredCategory (J := J) X).p
    ((F.presheafHom x y).obj (op T)) ≃
      sourceStage2HomSheafModelObj (J := J) X x y T := by
  let F := canonicalFiberPseudofunctor (pointwiseSourceFibredCategory (J := J) X).p
  let eT : (F.presheafHom x y).obj (op T) ≃
      (F.presheafHom x y).obj (op (Over.mk T.hom)) :=
    CategoryTheory.Iso.toEquiv ((F.presheafHom x y).mapIso (overObjectMkIso T).op)
  exact eT.trans
    (sourceStage2HomSheafModelObjAtBaseArrowEquiv (J := J) X x y T.hom)

/-- The concrete source-text presheaf model obtained from the pointwise plus model.

The restriction maps are intentionally defined by conjugating the canonical fiber Hom presheaf
maps through `sourceStage2HomSheafModelObjEquiv`.  This supplies a genuine presheaf and a
canonical presheaf isomorphism without asserting that the plus-model restriction maps are
definitionally the same as any hand-written source-text formula. -/
noncomputable def sourceStage2HomSheafModelPresheaf
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U) :
    (Over U)ᵒᵖ ⥤ Type (max (max u v) vX) :=
  conjugateFunctorByObjEquiv
    ((canonicalFiberPseudofunctor (pointwiseSourceFibredCategory (J := J) X).p).presheafHom x y)
    (fun T : (Over U)ᵒᵖ => sourceStage2HomSheafModelObj (J := J) X x y T.unop)
    (fun T : (Over U)ᵒᵖ => sourceStage2HomSheafModelObjEquiv (J := J) X x y T.unop)

/-- Presheaf-level comparison from the canonical stage-2 fiber Hom presheaf to the concrete
source-text plus model. -/
noncomputable def sourceStage2HomSheafModelIso
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U) :
    ((canonicalFiberPseudofunctor
      (pointwiseSourceFibredCategory (J := J) X).p).presheafHom x y) ≅
      sourceStage2HomSheafModelPresheaf (J := J) X x y :=
  conjugateFunctorByObjEquivIso
    ((canonicalFiberPseudofunctor (pointwiseSourceFibredCategory (J := J) X).p).presheafHom x y)
    (fun T : (Over U)ᵒᵖ => sourceStage2HomSheafModelObj (J := J) X x y T.unop)
    (fun T : (Over U)ᵒᵖ => sourceStage2HomSheafModelObjEquiv (J := J) X x y T.unop)

/-- The remaining concrete stage 2.8 sheaf frontier for the source-text plus model.

The presheaf structure and the comparison with the canonical fiber Hom presheaf are now fixed
above.  What remains is to prove that this explicit plus-model presheaf is a sheaf. -/
structure SourceStage2HomSheafModelFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  isSheaf :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      Presheaf.IsSheaf (J.over U)
        (sourceStage2HomSheafModelPresheaf (J := J) X x y)

namespace SourceStage2HomSheafModelFrontier

/-- A sheaf proof for the concrete source-text model gives the abstract pointwise bridge. -/
noncomputable def toPointwiseBridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceStage2HomSheafModelFrontier (J := J) X) :
    PointwiseSourceHomSheafBridge (J := J) X where
  sheafModel := fun _U x y => sourceStage2HomSheafModelPresheaf (J := J) X x y
  sheafModel_isSheaf := H.isSheaf
  fiberHomIso := fun _U x y => sourceStage2HomSheafModelIso (J := J) X x y

end SourceStage2HomSheafModelFrontier

/-- Post-quotient concrete stage 2.8 frontier required by the plus-plus construction. -/
abbrev SourceStage2HomSheafModelBridge
    (X : FibredCategoryOver.{u, v, uX, vX} C) :=
  SourceStage2HomSheafModelFrontier (J := J) (separatedQuotientStage (J := J) X).quotient

/-- The concrete post-quotient model frontier supplies the abstract source stage-2 bridge. -/
noncomputable def sourceStage2HomSheafBridge_of_modelFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceStage2HomSheafModelBridge (J := J) X) :
    SourceStage2HomSheafBridge (J := J) X :=
  H.toPointwiseBridge

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
