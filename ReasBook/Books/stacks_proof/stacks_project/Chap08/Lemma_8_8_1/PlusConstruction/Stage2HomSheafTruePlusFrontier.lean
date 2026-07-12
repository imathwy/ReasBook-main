import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage2HomSheafModel

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

/-- The pre-stage-2 fibre object underlying a stage-2 fibre object.

Objects of the locally-defined-Hom stage are unchanged; this forgets the stage-2 total wrapper
and keeps only the original fibre object over the same base. -/
noncomputable abbrev sourceStage2UnderlyingFiberObject
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U) :
    X.p.Fiber U :=
  Functor.Fiber.mk (p := X.p) (a := x.1.obj) x.2

/-- The original Hom presheaf, saturated to the concrete plus universe, whose plus construction
is the source-text stage-2 Hom sheaf.

For `x y` in the locally-defined-Hom fibre over `U`, this is the Hom presheaf of their underlying
pre-stage-2 objects on the slice over `U`. -/
noncomputable abbrev sourceStage2TruePlusBasePresheaf
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U) :
    (Over U)ᵒᵖ ⥤ Type (max (max u v) vX) :=
  ((canonicalFiberPseudofunctor X.p).presheafHom
    (sourceStage2UnderlyingFiberObject (J := J) X x)
    (sourceStage2UnderlyingFiberObject (J := J) X y)) ⋙
      (CategoryTheory.uliftFunctor.{max u v, vX} : Type vX ⥤
        Type (max (max u v) vX))

/-- The genuine source-text plus presheaf for stage 2.8.

Unlike `sourceStage2HomSheafModelPresheaf`, its restriction maps are literally the maps of the
plus construction on the slice site `J.over U`. -/
noncomputable abbrev sourceStage2TruePlusPresheaf
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U) :
    (Over U)ᵒᵖ ⥤ Type (max (max u v) vX) :=
  (J.over U).plusObj (sourceStage2TruePlusBasePresheaf (J := J) X x y)

set_option backward.isDefEq.respectTransparency false in
/-- If the pre-stage-2 Hom presheaf is separated, the genuine stage-2 plus presheaf is a sheaf. -/
theorem sourceStage2TruePlusPresheaf_isSheaf_of_separated
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U)
    (hsep :
      Presieve.IsSeparated (J.over U)
        ((canonicalFiberPseudofunctor X.p).presheafHom
          (sourceStage2UnderlyingFiberObject (J := J) X x)
          (sourceStage2UnderlyingFiberObject (J := J) X y))) :
    Presheaf.IsSheaf (J.over U)
      (sourceStage2TruePlusPresheaf (J := J) X x y) := by
  apply GrothendieckTopology.Plus.isSheaf_of_sep
  intro V S s t h
  apply ULift.ext
  exact Presieve.IsSeparatedFor.ext (hsep (S : Sieve V) S.condition) (by
    intro W g hg
    exact congrArg ULift.down (h ⟨W, g, hg⟩))

/-- Source stage 2.8 after the local-equality quotient: the genuine plus presheaves are sheaves.

This is the direct formal version of the draft's sentence that the second stage takes the plus of
the already separated Hom presheaves. -/
theorem sourceStage2TruePlusPresheaf_isSheaf_afterSeparatedQuotient
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y :
      (pointwiseSourceFibredCategory
        (J := J) (separatedQuotientStage (J := J) X).quotient).p.Fiber U) :
    Presheaf.IsSheaf (J.over U)
      (sourceStage2TruePlusPresheaf
        (J := J) (separatedQuotientStage (J := J) X).quotient x y) := by
  exact sourceStage2TruePlusPresheaf_isSheaf_of_separated
    (J := J) (separatedQuotientStage (J := J) X).quotient x y
    ((separatedQuotientStage (J := J) X).homPresheavesSeparated U
      (sourceStage2UnderlyingFiberObject
        (J := J) (separatedQuotientStage (J := J) X).quotient x)
      (sourceStage2UnderlyingFiberObject
        (J := J) (separatedQuotientStage (J := J) X).quotient y))

/-- The remaining comparison between the conjugated pointwise fixed-base model and the genuine
plus presheaf on the source slice.

After `sourceStage2TruePlusPresheaf_isSheaf_afterSeparatedQuotient`, this is the precise stage-2
frontier: prove that the canonical restriction maps used by
`sourceStage2HomSheafModelPresheaf` agree with the literal plus restriction maps of
`sourceStage2TruePlusPresheaf`. -/
structure SourceStage2TruePlusComparisonFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  modelIso :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      sourceStage2HomSheafModelPresheaf (J := J) X x y ≅
        sourceStage2TruePlusPresheaf (J := J) X x y

/-- Source stage 2.8 expressed with a genuinely plus-defined presheaf.

The existing `sourceStage2HomSheafModelPresheaf` is a canonical-Hom presheaf conjugated through
the objectwise plus description.  That makes the presheaf comparison easy, but makes sheafness
look circular.  This frontier separates the source-text proof into two honest steps:

* build a presheaf whose restriction maps are the actual plus restrictions and prove it is a
  sheaf by `Plus.isSheaf_of_sep`;
* compare that true-plus presheaf to the conjugated concrete model by a natural isomorphism.

No owner or universe equality is asserted here. -/
structure SourceStage2HomSheafTruePlusFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  /-- The presheaf whose values are the source-text plus sections and whose maps are the actual
  plus restrictions. -/
  plusPresheaf :
    ∀ (U : C)
      (_x _y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      (Over U)ᵒᵖ ⥤ Type (max (max u v) vX)
  /-- The true-plus presheaf is a sheaf.  This is the part expected to follow directly from
  separatedness of the post-quotient Hom presheaves. -/
  plusPresheaf_isSheaf :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      Presheaf.IsSheaf (J.over U) (plusPresheaf U x y)
  /-- Natural comparison from the current conjugated concrete model to the true-plus presheaf.
  This is the remaining restriction-map compatibility calculation. -/
  modelIso :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      sourceStage2HomSheafModelPresheaf (J := J) X x y ≅ plusPresheaf U x y

namespace SourceStage2HomSheafTruePlusFrontier

/-- A true-plus frontier gives the concrete-model sheaf frontier used by the draft-input layer. -/
theorem toModelFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceStage2HomSheafTruePlusFrontier (J := J) X) :
    SourceStage2HomSheafModelFrontier (J := J) X where
  isSheaf := by
    intro U x y
    exact (Presheaf.isSheaf_of_iso_iff (H.modelIso U x y)).2
      (H.plusPresheaf_isSheaf U x y)

/-- A true-plus frontier also gives the abstract pointwise bridge directly. -/
noncomputable def toPointwiseBridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceStage2HomSheafTruePlusFrontier (J := J) X) :
    PointwiseSourceHomSheafBridge (J := J) X :=
  H.toModelFrontier.toPointwiseBridge

end SourceStage2HomSheafTruePlusFrontier

/-- Post-quotient true-plus stage 2.8 frontier required by the plus-plus construction. -/
abbrev SourceStage2HomSheafTruePlusBridge
    (X : FibredCategoryOver.{u, v, uX, vX} C) :=
  SourceStage2HomSheafTruePlusFrontier (J := J) (separatedQuotientStage (J := J) X).quotient

/-- The post-quotient true-plus frontier supplies the concrete stage-2 model bridge. -/
theorem sourceStage2HomSheafModelBridge_of_truePlusFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceStage2HomSheafTruePlusBridge (J := J) X) :
    SourceStage2HomSheafModelBridge (J := J) X :=
  H.toModelFrontier

/-- The post-quotient true-plus frontier supplies the abstract source stage-2 bridge. -/
noncomputable def sourceStage2HomSheafBridge_of_truePlusFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceStage2HomSheafTruePlusBridge (J := J) X) :
    SourceStage2HomSheafBridge (J := J) X :=
  H.toPointwiseBridge

namespace SourceStage2TruePlusComparisonFrontier

/-- Over the separated quotient, the comparison frontier supplies the true-plus frontier. -/
noncomputable def toTruePlusBridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H :
      SourceStage2TruePlusComparisonFrontier
        (J := J) (separatedQuotientStage (J := J) X).quotient) :
    SourceStage2HomSheafTruePlusBridge (J := J) X where
  plusPresheaf := fun U x y =>
    sourceStage2TruePlusPresheaf
      (J := J) (separatedQuotientStage (J := J) X).quotient x y
  plusPresheaf_isSheaf := by
    intro U x y
    exact sourceStage2TruePlusPresheaf_isSheaf_afterSeparatedQuotient (J := J) X x y
  modelIso := H.modelIso

/-- Over the separated quotient, the comparison frontier gives the concrete stage-2 model bridge. -/
theorem toModelBridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H :
      SourceStage2TruePlusComparisonFrontier
        (J := J) (separatedQuotientStage (J := J) X).quotient) :
    SourceStage2HomSheafModelBridge (J := J) X :=
  sourceStage2HomSheafModelBridge_of_truePlusFrontier (J := J) H.toTruePlusBridge

/-- Over the separated quotient, the comparison frontier gives the abstract stage-2 bridge. -/
noncomputable def toSourceStage2Bridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H :
      SourceStage2TruePlusComparisonFrontier
        (J := J) (separatedQuotientStage (J := J) X).quotient) :
    SourceStage2HomSheafBridge (J := J) X :=
  sourceStage2HomSheafBridge_of_truePlusFrontier (J := J) H.toTruePlusBridge

end SourceStage2TruePlusComparisonFrontier

/-- Source stage 2.8 in its most direct presheaf form: the canonical Hom presheaf of the
locally-defined-Hom projection is the genuine plus presheaf of the old Hom presheaf.

This is the Lean-facing form of the source statement
`Mor_{S^2}(x, y) = Mor_S(x, y)^+`.  It keeps the comparison at the canonical Hom presheaf level;
the pointwise fixed-base model is recovered from this by the already-proved
`sourceStage2HomSheafModelIso`. -/
structure SourceStage2CanonicalTruePlusComparisonFrontier
    (X : FibredCategoryOver.{u, v, uX, vX} C) where
  fiberHomTruePlusIso :
    ∀ (U : C)
      (x y : (pointwiseSourceFibredCategory (J := J) X).p.Fiber U),
      ((canonicalFiberPseudofunctor
        (pointwiseSourceFibredCategory (J := J) X).p).presheafHom x y) ≅
        sourceStage2TruePlusPresheaf (J := J) X x y

namespace SourceStage2CanonicalTruePlusComparisonFrontier

/-- The canonical-Hom comparison gives the model-to-true-plus comparison by composing with the
existing canonical-Hom-to-model isomorphism. -/
noncomputable def toTruePlusComparisonFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H : SourceStage2CanonicalTruePlusComparisonFrontier (J := J) X) :
    SourceStage2TruePlusComparisonFrontier (J := J) X where
  modelIso := fun U x y =>
    (sourceStage2HomSheafModelIso (J := J) X x y).symm ≪≫
      H.fiberHomTruePlusIso U x y

/-- A canonical-Hom comparison over the separated quotient gives the true-plus bridge directly,
with sheafness supplied by the already separated Hom presheaves. -/
noncomputable def toTruePlusBridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H :
      SourceStage2CanonicalTruePlusComparisonFrontier
        (J := J) (separatedQuotientStage (J := J) X).quotient) :
    SourceStage2HomSheafTruePlusBridge (J := J) X where
  plusPresheaf := fun U x y =>
    sourceStage2TruePlusPresheaf
      (J := J) (separatedQuotientStage (J := J) X).quotient x y
  plusPresheaf_isSheaf := by
    intro U x y
    exact sourceStage2TruePlusPresheaf_isSheaf_afterSeparatedQuotient (J := J) X x y
  modelIso := H.toTruePlusComparisonFrontier.modelIso

/-- A canonical-Hom comparison over the separated quotient gives the abstract stage-2 bridge
without routing through the fixed-base model as the sheaf model. -/
noncomputable def toPointwiseBridge
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (H :
      SourceStage2CanonicalTruePlusComparisonFrontier
        (J := J) (separatedQuotientStage (J := J) X).quotient) :
    PointwiseSourceHomSheafBridge
      (J := J) (separatedQuotientStage (J := J) X).quotient where
  sheafModel := fun U x y =>
    sourceStage2TruePlusPresheaf
      (J := J) (separatedQuotientStage (J := J) X).quotient x y
  sheafModel_isSheaf := by
    intro U x y
    exact sourceStage2TruePlusPresheaf_isSheaf_afterSeparatedQuotient (J := J) X x y
  fiberHomIso := H.fiberHomTruePlusIso

end SourceStage2CanonicalTruePlusComparisonFrontier

end LocallyDefinedHomTotal
end FibredCategoryMor

end CategoryTheory
