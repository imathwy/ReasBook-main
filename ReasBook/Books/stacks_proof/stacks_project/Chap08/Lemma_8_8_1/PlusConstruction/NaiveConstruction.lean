import StacksProject_2024.Chap08.Lemma_8_8_1.CartesianComposition
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.StageInterfaces
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage2HomSheaf
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3LocalEssentialSurjectivity
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.Frontier

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

namespace DescentCompletionObject

namespace Stage3Frontier

/-- Helper for Chap08 Lemma 8 8 1: the source stage 3.7 old-object functor, expressed at the
heterogeneous based-functor level.  This is the faithful owner frontier: the target projection
has the mixed owner recorded by `stackOwner`, so it is not yet a same-owner morphism
`X ⟶ S.stack`. -/
noncomputable def oldObjectToProjectionBasedFunctor
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : Stage3Frontier (J := J) X) :
    letI := category (J := J) S.homSheaves
    BasedCategory.ofFunctor X.p ⥤ᵇ
      BasedCategory.ofFunctor (projectionFunctor (J := J) S.homSheaves) := by
  letI := category (J := J) S.homSheaves
  exact oldObjectBasedFunctor (J := J) X S.homSheaves

/-- Helper for Chap08 Lemma 8 8 1: the old-object functor preserves strongly cartesian arrows,
so it is the correct morphism-level data for the descent-completion stage before any owner
resizing/downsize theorem is applied. -/
theorem oldObjectToProjectionBasedFunctor_preservesStronglyCartesian
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : Stage3Frontier (J := J) X) :
    letI := category (J := J) S.homSheaves
    (oldObjectToProjectionBasedFunctor (J := J) S).PreservesStronglyCartesian := by
  letI := category (J := J) S.homSheaves
  simpa [oldObjectToProjectionBasedFunctor] using
    oldObjectBasedFunctor_preservesStronglyCartesian (J := J) X S.homSheaves

/-- Helper for Chap08 Lemma 8 8 1: the source-faithful third stage after stages 3.12 and 3.13
have been supplied.  The structure deliberately keeps the old-object comparison as a
heterogeneous based functor, because the completed stack lives in the mixed owner `stackOwner`.
-/
structure MixedAssembly (J : GrothendieckTopology C)
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- The Hom-sheaf input used to define composition in the descent-completion category. -/
  homSheaves :
    DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X
  /-- The source stage 3.7 old-object comparison into the completed projection. -/
  toProjectionBasedFunctor :
    letI := category (J := J) (X := X) homSheaves
    BasedCategory.ofFunctor X.p ⥤ᵇ
      BasedCategory.ofFunctor (projectionFunctor (J := J) homSheaves)
  /-- The completed descent-data stack, in the mixed owner forced by the construction. -/
  stack : stackOwner.{u, v, uX, vX} (J := J)
  /-- The old-object comparison preserves cartesian arrows. -/
  preservesCartesian :
    letI := category (J := J) (X := X) homSheaves
    toProjectionBasedFunctor.PreservesStronglyCartesian
  /-- Source stage 3.9: every completed object is locally isomorphic to an old object, stated at
  the heterogeneous based-functor frontier forced by the mixed target owner. -/
  locallyEssentiallySurjective :
    letI := category (J := J) (X := X) homSheaves
    Stage3LocalEssentialSurjectivity.BasedFunctorLocallyEssentiallySurjectiveOnObjects
      (J := J) toProjectionBasedFunctor
      (projectionFunctor_isFibered (J := J) homSheaves)
  /-- Source stage 3.12 for the completed projection. -/
  projectionHomSheaves :
    projectionFunctorHomPresheavesAreSheaves (J := J) homSheaves
  /-- Source stage 3.13 for the completed projection. -/
  projectionDescentEffective :
    projectionFunctorCoverwiseDescentEffective (J := J) homSheaves

/-- Helper for Chap08 Lemma 8 8 1: assemble the completed third stage into the mixed-owner
frontier that Lean can currently express without pretending the owner gap is solved. -/
noncomputable def mixedAssembly
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : Stage3Frontier (J := J) X) :
    MixedAssembly J X where
  homSheaves := S.homSheaves
  stack := S.stack
  toProjectionBasedFunctor := oldObjectToProjectionBasedFunctor (J := J) S
  preservesCartesian :=
    oldObjectToProjectionBasedFunctor_preservesStronglyCartesian (J := J) S
  locallyEssentiallySurjective := by
    simpa [oldObjectToProjectionBasedFunctor] using
      Stage3LocalEssentialSurjectivity.oldObjectBasedFunctor_locallyEssentiallySurjectiveOnObjects
        (J := J) S.homSheaves
  projectionHomSheaves := S.projectionHomSheaves
  projectionDescentEffective := S.projectionDescentEffective

/-- The stack recorded by `mixedAssembly` is definitionally the completed projection stack. -/
@[simp]
theorem mixedAssembly_stack
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : Stage3Frontier (J := J) X) :
    (mixedAssembly (J := J) S).stack = S.stack :=
  rfl

/-- The comparison recorded by `mixedAssembly` is the old-object based functor. -/
@[simp]
theorem mixedAssembly_toProjectionBasedFunctor
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : Stage3Frontier (J := J) X) :
    letI := category (J := J) S.homSheaves
    (mixedAssembly (J := J) S).toProjectionBasedFunctor =
      oldObjectToProjectionBasedFunctor (J := J) S := by
  rfl

end Stage3Frontier
end DescentCompletionObject

/-- Source-faithful mixed-owner version of the naive plus-plus construction.

The first stage is the local-equality quotient.  The second stage is the locally-defined-Hom
construction in its natural mixed owner.  The third stage is the descent-object completion, also
kept at the mixed-owner frontier.  This structure intentionally does not assert a same-owner
`NaiveStackificationConstruction`; that is the separate universe/owner bridge. -/
structure SourceNaivePlusPlusMixedConstruction
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- Stage 1: quotient morphisms by local equality. -/
  separated : SeparatedQuotientStage (J := J) X
  /-- Stage 2: locally-defined morphisms, after the cartesian and Hom-sheaf calculations. -/
  homSheafification :
    LocallyDefinedHomTotal.SourceHomSheafificationMixedAssembly (J := J) separated.quotient
  /-- Stage 3: descent-data objects over the mixed-owner stage-2 target. -/
  descentCompletion :
    DescentCompletionObject.Stage3Frontier (J := J) homSheafification.sheafified

namespace SourceNaivePlusPlusMixedConstruction

/-- The mixed-owner stage-2 target. -/
noncomputable def stage2Target
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : SourceNaivePlusPlusMixedConstruction (J := J) X) :
    LocallyDefinedHomTotal.sourceStage2Owner S.separated.quotient :=
  S.homSheafification.sheafified

/-- The mixed-owner third-stage assembly attached to the source construction frontier. -/
noncomputable def stage3MixedAssembly
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (S : SourceNaivePlusPlusMixedConstruction (J := J) X) :
    DescentCompletionObject.Stage3Frontier.MixedAssembly J S.stage2Target :=
  DescentCompletionObject.Stage3Frontier.mixedAssembly (J := J) S.descentCompletion

/-- Assemble the mixed-owner naive construction using the concrete local-equality quotient and
the completed pointwise stage-2 cartesian calculation.  The remaining arguments are precisely
source stage 2.8 and source stages 3.12/3.13. -/
noncomputable def ofPointwiseStage2
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hHomSheaves :
      LocallyDefinedHomTotal.pointwiseSourceHomSheavesObligation
        (J := J) (separatedQuotientStage (J := J) X).quotient)
    (Hstage3 :
      DescentCompletionObject.Stage3Frontier (J := J)
        (LocallyDefinedHomTotal.pointwiseSourceHomSheafificationMixedAssembly
          (J := J) (separatedQuotientStage (J := J) X).quotient hHomSheaves).sheafified) :
    SourceNaivePlusPlusMixedConstruction (J := J) X where
  separated := separatedQuotientStage (J := J) X
  homSheafification :=
    LocallyDefinedHomTotal.pointwiseSourceHomSheafificationMixedAssembly
      (J := J) (separatedQuotientStage (J := J) X).quotient hHomSheaves
  descentCompletion := Hstage3

/-- Assemble the mixed-owner naive construction from the pointwise stage-2 calculation and the
source-order stage-3 frontiers.

This is the direct Lean counterpart of the draft's flow:

* 2.8 supplies Hom sheaves for locally-defined morphisms;
* the descent-completion composition input supplies Hom sheaves for the pre-completion category;
* 3.12 supplies Hom sheaves for the completed projection;
* 3.13 supplies descent effectivity via the total-cover construction. -/
noncomputable def ofPointwiseStage2AndTotalCoverFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    (hHomSheaves :
      LocallyDefinedHomTotal.pointwiseSourceHomSheavesObligation
        (J := J) (separatedQuotientStage (J := J) X).quotient)
    (hStage3Hom :
      DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J)
        (LocallyDefinedHomTotal.pointwiseSourceHomSheafificationMixedAssembly
          (J := J) (separatedQuotientStage (J := J) X).quotient hHomSheaves).sheafified)
    (hProjectionHom :
      DescentCompletionObject.projectionFunctorHomPresheavesAreSheaves (J := J) hStage3Hom)
    (Htotal :
      DescentCompletionObject.ProjectionFunctorCoverwiseDescentEffectiveFrontier
        (J := J) hStage3Hom) :
    SourceNaivePlusPlusMixedConstruction (J := J) X :=
  ofPointwiseStage2 (J := J) X hHomSheaves
    (DescentCompletionObject.Stage3Frontier.ofTotalCoverFrontier
      (J := J) hStage3Hom hProjectionHom Htotal)

end SourceNaivePlusPlusMixedConstruction

/-- The mixed-owner naive plus-plus frontier for a Cat-valued co-Grothendieck model.  This is the
source-faithful replacement target for the current same-owner existence placeholder. -/
abbrev CatValuedSourceNaivePlusPlusMixedConstruction
    (F : Cᵒᵖ ⥤ Cat.{vX, uX}) :=
  SourceNaivePlusPlusMixedConstruction (J := J) (catValuedCoGrothendieckModel F)

end FibredCategoryMor

end CategoryTheory
