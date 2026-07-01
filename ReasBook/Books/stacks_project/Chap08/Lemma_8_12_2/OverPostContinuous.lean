import Mathlib
import stacks_project.Chap07.Lemma_7_28_1

universe uC uD vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Lemma 8.12.2: theorem-local owner for the slice continuity step along `Over.post u`.
This isolates the exact source-faithful blocker from the main pullback-stack proof. -/
theorem overPost_op_comp_isSheaf_of_isContinuous_local
    [Functor.IsContinuous u J K]
    {U : C} (P : (Over (u.obj U))ᵒᵖ ⥤ Type vS)
    (hP : Presheaf.IsSheaf (K.over (u.obj U)) P) :
    Presheaf.IsSheaf (J.over U) ((Over.post u).op ⋙ P) := by
  -- Route correction: now that the Chapter 7 owner is imported stably, the local bridge is just
  -- the generic continuity-to-sheaf transport theorem applied to `Over.post u`.
  simpa using
    (Functor.op_comp_isSheaf_of_isSheaf
      (F := Over.post u) (J := J.over U) (K := K.over (u.obj U)) P hP)

end

end CategoryTheory
