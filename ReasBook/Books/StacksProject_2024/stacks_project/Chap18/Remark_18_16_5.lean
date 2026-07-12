import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ModuleCat

universe u

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B)

-- Proof sketch: `ModuleCat.extendScalars f` already has the canonical right adjoint
-- `ModuleCat.restrictScalars f` via `ModuleCat.extendRestrictScalarsAdj f`. If it also had a left
-- adjoint, then it would be a right adjoint and hence preserve all limits, in particular finite
-- limits. For extension of scalars, preservation of finite limits forces flatness of `f`.
/-- Remark 18.16.5: if extension of scalars along a ring map `f : A →+* B` also has a left
adjoint, equivalently if `ModuleCat.extendScalars f` is a right adjoint, then `f` is flat. This
is the module-theoretic obstruction to extending lower shriek functors for arbitrary morphisms of
ringed topoi. -/
theorem flat_of_extendScalars_isRightAdjoint
    (h : (extendScalars.{u, u, u} f).IsRightAdjoint) :
    f.Flat := by
  letI := h
  letI : PreservesFiniteLimits (extendScalars.{u, u, u} f) := by infer_instance
  have htensor : PreservesFiniteLimits
      (tensorLeft ((restrictScalars.{u, u, u} f).obj (of B B))) := by
    change PreservesFiniteLimits
      (extendScalars.{u, u, u} f ⋙ restrictScalars.{u, u, u} f)
    infer_instance
  simpa [RingHom.Flat] using
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft
      ((restrictScalars.{u, u, u} f).obj (of B B))).2 htensor

end
