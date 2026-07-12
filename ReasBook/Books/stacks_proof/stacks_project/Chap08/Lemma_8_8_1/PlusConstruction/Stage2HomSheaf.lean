import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCartesianFactorization
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.LocallyDefinedHomCartesianSameCover

universe u v uX vX

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

/-- Helper for Chap08 Lemma 8 8 1, source stage 2: the source locally-defined-Hom total
category has the same objects as the input fibred category after the projection is upgraded to a
fibred category. -/
noncomputable def sourceFibredCategoryObjectEquiv
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (H : SourceProjectionFiberedFrontier (J := J) X) :
    (sourceFibredCategoryOfFrontier (J := J) X H).S ≃ X.S :=
  objectEquiv (J := J) X

/-- Helper for Chap08 Lemma 8 8 1, source stage 2: the mixed-owner target of the
locally-defined-Hom construction.

The Hom type of locally defined morphisms is a plus construction in the saturated type universe,
so the target fibred category has Hom universe `max (max u v) vX`, not the original `vX`. -/
abbrev sourceStage2Owner
    (_X : FibredCategoryOver.{u, v, uX, vX} C) :=
  FibredCategoryOver.{u, v, uX, max (max u v) vX} C

/-- Helper for Chap08 Lemma 8 8 1, source stage 2: the remaining source-faithful mixed-owner
frontier for turning locally-defined morphisms into the second-stage Hom-sheafification.

The first two fields are the cartesian-lift obligations for the projection and for the canonical
old-object functor.  The last field is the Hom-sheaf statement needed by the abstract
`HomSheafificationStage` interface.  These are kept explicit because the canonical fiber
pseudofunctor uses chosen pullbacks, so replacing them by definitional equalities would hide the
owner/coherence work. -/
structure SourceHomSheafificationMixedAssembly
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Source stage 2 projection is fibred. -/
  projectionFibered : SourceProjectionFiberedFrontier (J := J) X
  /-- The old-object comparison preserves strongly cartesian arrows. -/
  oldObjectPreservesCartesian :
    (oldObjectToSourceBasedFunctor (J := J) X).PreservesStronglyCartesian
  /-- Hom presheaves of the locally-defined-Hom projection are sheaves. -/
  homPresheavesSheaves :
    ∀ (U : C) (x y :
        (sourceFibredCategoryOfFrontier (J := J) X projectionFibered).p.Fiber U),
      Presheaf.IsSheaf (J.over U)
        ((canonicalFiberPseudofunctor
          (sourceFibredCategoryOfFrontier (J := J) X projectionFibered).p).presheafHom x y)

namespace SourceHomSheafificationMixedAssembly

/-- Assemble the mixed-owner source Hom-sheafification frontier from the cartesian factorization
frontier and the Hom-sheaf calculation for the resulting source projection. -/
noncomputable def ofCartesianFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (Hcart : SourceCartesianFrontier (J := J) X)
    (hHomSheaves :
      ∀ (U : C) (x y :
          (sourceFibredCategoryOfFrontier (J := J) X
            (Hcart.sourceProjectionFiberedFrontier)).p.Fiber U),
        Presheaf.IsSheaf (J.over U)
          ((canonicalFiberPseudofunctor
            (sourceFibredCategoryOfFrontier (J := J) X
              (Hcart.sourceProjectionFiberedFrontier)).p).presheafHom x y)) :
    SourceHomSheafificationMixedAssembly (J := J) X where
  projectionFibered := Hcart.sourceProjectionFiberedFrontier
  oldObjectPreservesCartesian :=
    Hcart.oldObjectToSourceBasedFunctor_preservesStronglyCartesian
  homPresheavesSheaves := hHomSheaves

/-- Assemble the mixed-owner source Hom-sheafification frontier directly from the source
stage-2.6 local factorization statement and the Hom-sheaf calculation. -/
noncomputable def ofCartesianFactorization
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (Hfac : SourceCartesianFactorizationFrontier (J := J) X)
    (hHomSheaves :
      ∀ (U : C) (x y :
          (sourceFibredCategoryOfFrontier (J := J) X
            (Hfac.toSourceCartesianFrontier.sourceProjectionFiberedFrontier)).p.Fiber U),
        Presheaf.IsSheaf (J.over U)
          ((canonicalFiberPseudofunctor
            (sourceFibredCategoryOfFrontier (J := J) X
              (Hfac.toSourceCartesianFrontier.sourceProjectionFiberedFrontier)).p).presheafHom x y)) :
    SourceHomSheafificationMixedAssembly (J := J) X :=
  ofCartesianFrontier (J := J) Hfac.toSourceCartesianFrontier hHomSheaves

/-- Assemble the mixed-owner source Hom-sheafification frontier from the literal source-form
stage-2.6 factorization statement and the Hom-sheaf calculation. -/
noncomputable def ofStrictCartesianFactorization
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (Hfac : StrictSourceCartesianFactorizationFrontier (J := J) X)
    (hHomSheaves :
      ∀ (U : C) (x y :
          (sourceFibredCategoryOfFrontier (J := J) X
            (Hfac.toSourceCartesianFrontier.sourceProjectionFiberedFrontier)).p.Fiber U),
        Presheaf.IsSheaf (J.over U)
          ((canonicalFiberPseudofunctor
            (sourceFibredCategoryOfFrontier (J := J) X
              (Hfac.toSourceCartesianFrontier.sourceProjectionFiberedFrontier)).p).presheafHom x y)) :
    SourceHomSheafificationMixedAssembly (J := J) X :=
  ofCartesianFrontier (J := J) Hfac.toSourceCartesianFrontier hHomSheaves

/-- The mixed-owner target determined by the source stage-2 projection. -/
noncomputable def sheafified
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceHomSheafificationMixedAssembly (J := J) X) :
    sourceStage2Owner X :=
  sourceFibredCategoryOfFrontier (J := J) X H.projectionFibered

/-- Source stage 2.5 old-object comparison, stated at the based-functor frontier because the
target owner has grown. -/
noncomputable def toSourceBasedFunctor
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceHomSheafificationMixedAssembly (J := J) X) :
    X.toBasedCategory ⥤ᵇ H.sheafified.toBasedCategory :=
  oldObjectToSourceBasedFunctor (J := J) X

/-- The mixed-owner target is definitionally the source stage-2 projection. -/
@[simp]
theorem sheafified_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceHomSheafificationMixedAssembly (J := J) X) :
    H.sheafified = sourceFibredCategoryOfFrontier (J := J) X H.projectionFibered :=
  rfl

/-- The old-object comparison is definitionally the source based functor. -/
@[simp]
theorem toSourceBasedFunctor_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceHomSheafificationMixedAssembly (J := J) X) :
    H.toSourceBasedFunctor = oldObjectToSourceBasedFunctor (J := J) X :=
  rfl

end SourceHomSheafificationMixedAssembly

/-- Source stage 2.6/2.7, using the completed pointwise same-cover construction from the
Stacks proof.

This is the reusable named frontier for the argument in the draft: factor each member of the
cover through the cartesian arrow, prove overlap compatibility, recover the composite, and use
same-cover uniqueness. -/
noncomputable def pointwiseSourceCartesianFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    SourceCartesianFrontier (J := J) X :=
  (SameCoverLocalFactorization.pointwiseLocalFactorizationFrontier (J := J) X).toSourceCartesianFrontier

/-- The fibred-category frontier supplied by the pointwise same-cover construction. -/
noncomputable def pointwiseSourceProjectionFiberedFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    SourceProjectionFiberedFrontier (J := J) X :=
  (pointwiseSourceCartesianFrontier (J := J) X).sourceProjectionFiberedFrontier

/-- The mixed-owner second-stage fibred category obtained from pointwise stage 2.6/2.7. -/
noncomputable def pointwiseSourceFibredCategory
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    sourceStage2Owner X :=
  sourceFibredCategoryOfFrontier (J := J) X
    (pointwiseSourceProjectionFiberedFrontier (J := J) X)

/-- Source stage 2.8, isolated as the exact Hom-sheaf obligation for the pointwise stage-2
projection.  This is the formal counterpart of the draft's statement that the locally-defined
morphism construction is the plus construction on separated Hom presheaves. -/
def pointwiseSourceHomSheavesObligation
    (X : FibredCategoryOver.{u, v, uX, vX} C) : Prop :=
  ∀ (U : C) (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
    Presheaf.IsSheaf (J.over U)
      ((canonicalFiberPseudofunctor
        (pointwiseSourceFibredCategory (J := J) X).p).presheafHom x y)

/-- Assemble source stage 2 from the completed pointwise cartesian calculation plus the remaining
Hom-sheaf calculation.  The result deliberately stays in the mixed owner forced by the plus
construction. -/
noncomputable def pointwiseSourceHomSheafificationMixedAssembly
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hHomSheaves : pointwiseSourceHomSheavesObligation (J := J) X) :
    SourceHomSheafificationMixedAssembly (J := J) X :=
  SourceHomSheafificationMixedAssembly.ofCartesianFrontier
    (J := J) (pointwiseSourceCartesianFrontier (J := J) X) (by
      simpa [pointwiseSourceFibredCategory, pointwiseSourceProjectionFiberedFrontier,
        pointwiseSourceCartesianFrontier] using hHomSheaves)

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
