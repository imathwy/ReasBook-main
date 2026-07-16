import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import stacks_proof.stacks_project.Chap04.Lemma_4_22_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

/-- The Chapter 4 source notion that the left derived functor of `F` is defined at `X`, namely
that the pro-object indexed by `S / X` is essentially constant. -/
class LeftDerivedDefinedAt (F : D ⥤ D') (S : MorphismProperty D) (X : D) : Prop where
  isEssentiallyConstant :
    IsEssentiallyConstantCofilteredDiagram (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)

/-- The Chapter 4 source notion that the right derived functor of `F` is defined at `X`, namely
that the ind-object indexed by `X / S` is essentially constant. -/
class RightDerivedDefinedAt (F : D ⥤ D') (S : MorphismProperty D) (X : D) : Prop where
  isEssentiallyConstant :
    IsEssentiallyConstantFilteredDiagram (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)

/-- A right-derived definedness witness yields the canonical pointwise right-derived functor
existence instance. -/
noncomputable instance rightDerivedDefinedAt_toHasPointwiseRightDerivedFunctorAt
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [hX : RightDerivedDefinedAt F S X] :
    F.HasPointwiseRightDerivedFunctorAt S X := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  -- Proof comment: convert the Chapter 4 essential-constancy witness into the canonical colimit
  -- cocone computing the pointwise right Kan extension.
  obtain ⟨cX, _hcX⟩ :=
    essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone
      RX hX.isEssentiallyConstant
  exact ⟨show HasPointwiseLeftKanExtensionAt S.Q F (S.Q.obj X) from HasColimit.mk cX⟩

/-- A left-derived definedness witness yields the canonical pointwise left-derived functor
existence instance. -/
noncomputable instance leftDerivedDefinedAt_toHasPointwiseLeftDerivedFunctorAt
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [hX : LeftDerivedDefinedAt F S X] :
    F.HasPointwiseLeftDerivedFunctorAt S X := by
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  -- Proof comment: dually, convert the Chapter 4 essential-constancy witness into the canonical
  -- limit cone computing the pointwise left Kan extension.
  obtain ⟨cX, _hcX⟩ :=
    essentiallyConstantCofilteredDiagram_exists_essentiallyConstant_limitCone
      LX hX.isEssentiallyConstant
  exact ⟨show HasPointwiseRightKanExtensionAt S.Q F (S.Q.obj X) from HasLimit.mk cX⟩

end

end CategoryTheory
