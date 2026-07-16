import StacksProject_2024.stacks_project.Chap29.Definition_29_41_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: Chapter 29 already introduced the source-facing birational owner
-- `IsBirational`. A modification is the integral/proper specialization of that owner, so this
-- file keeps `IsModification` as a thin bridge rather than duplicating the birational data.

section

variable {X' X : Scheme.{u}}

private instance finiteIrreducibleComponents_of_isIntegral (X : Scheme.{u}) [IsIntegral X] :
    Finite (irreducibleComponents X) := by
  letI : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  infer_instance

/-- Definition 29.51.11: a modification is a birational proper morphism
`f : X' ⟶ X` between integral schemes. The birational part is the existing Chapter 29 owner
`IsBirational`, so the source-facing public API keeps the integrality hypotheses together with the
proper specialization of that owner. -/
@[stacks 01RN]
class IsModification (f : X' ⟶ X) : Prop extends IsProper f where
  isIntegralSource : IsIntegral X'
  isIntegralTarget : IsIntegral X
  toIsBirational :
    letI : IsIntegral X' := isIntegralSource
    letI : IsIntegral X := isIntegralTarget
    letI : Finite (irreducibleComponents X') := finiteIrreducibleComponents_of_isIntegral X'
    letI : Finite (irreducibleComponents X) := finiteIrreducibleComponents_of_isIntegral X
    IsBirational f

attribute [instance] IsModification.isIntegralSource IsModification.isIntegralTarget

instance (f : X' ⟶ X) [h : IsModification f] : IsBirational f := by
  letI : IsIntegral X' := h.isIntegralSource
  letI : IsIntegral X := h.isIntegralTarget
  letI : Finite (irreducibleComponents X') := finiteIrreducibleComponents_of_isIntegral X'
  letI : Finite (irreducibleComponents X) := finiteIrreducibleComponents_of_isIntegral X
  exact h.toIsBirational

/-- Over integral source and target schemes, `IsModification f` is exactly the birational-proper
specialization from the source definition. -/
@[stacks 01RN]
theorem isModification_iff (f : X' ⟶ X) [IsIntegral X'] [IsIntegral X] :
    IsModification f ↔ IsBirational f ∧ IsProper f := by
  constructor
  · intro h
    exact ⟨inferInstance, h.toIsProper⟩
  · rintro ⟨hBirational, hProper⟩
    exact
      { isIntegralSource := inferInstance
        isIntegralTarget := inferInstance
        toIsBirational := hBirational
        toIsProper := hProper }

end

end AlgebraicGeometry
