import Mathlib.CategoryTheory.Adjunction.Limits
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_9

open CategoryTheory

universe u v w

/-- Remark 5.2.12. Because `weakHausdorffKification` is a right adjoint, mathlib infers that it
preserves `J`-shaped limits. -/
noncomputable instance instPreservesLimitsOfShapeWeakHausdorffKification
    {J : Type u} [Category.{v} J] :
    CategoryTheory.Limits.PreservesLimitsOfShape J weakHausdorffKification := by
  -- Proposition 5.2.9 supplies the right-adjoint witness needed by the generic limit-preservation
  -- instance for right adjoints.
  let _ : weakHausdorffKification.IsRightAdjoint :=
    weakHausdorffKificationAdjunction.isRightAdjoint
  -- Right adjoints preserve all limits through the generic mathlib instance.
  infer_instance
