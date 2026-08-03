module

public import Mathlib.Order.RelClasses

public section

universe u

/-- The relation `r a b ∨ a = b` is the canonical reflexive closure `Relation.ReflGen r`. -/
theorem relOrEq_iff_reflGen {α : Type u} (r : α → α → Prop) (a b : α) :
    r a b ∨ a = b ↔ Relation.ReflGen r a b := by
  simp [Relation.reflGen_iff, eq_comm, or_comm]

/-- Exercise 11.2 (1): the reflexive closure of a strict partial order is a partial order. -/
instance IsStrictOrder.relOrEq {α : Sort u} (r : α → α → Prop) [IsStrictOrder α r] :
    IsPartialOrder α (fun a b ↦ r a b ∨ a = b) := by
  -- Reflexivity is supplied by the equality branch of the closure.
  refine { refl := fun a ↦ Or.inr rfl, trans := ?_, antisymm := ?_ }
  · -- Compose strict comparisons, eliminating equality branches by substitution.
    intro a b c hab hbc
    rcases hab with hab | hab
    · rcases hbc with hbc | hbc
      · exact Or.inl (trans_of r hab hbc)
      · subst c
        exact Or.inl hab
    · subst b
      exact hbc
  · -- Opposing strict comparisons contradict asymmetry; equality branches settle the goal.
    intro a b hab hba
    rcases hab with hab | hab
    · rcases hba with hba | hba
      · exact (asymm_of r hab hba).elim
      · exact hba.symm
    · exact hab

/-- Exercise 11.2 (2): removing equality from a partial order gives a strict partial order. -/
instance IsPartialOrder.relAndNe {α : Sort u} (r : α → α → Prop) [IsPartialOrder α r] :
    IsStrictOrder α (fun a b ↦ r a b ∧ a ≠ b) := by
  -- The inequality component immediately excludes self-related elements.
  refine { irrefl := fun a haa ↦ haa.2 rfl, trans := ?_ }
  -- Transitivity of the order component combines with antisymmetry to preserve inequality.
  intro a b c hab hbc
  refine ⟨trans_of r hab.1 hbc.1, ?_⟩
  intro hac
  subst c
  exact hab.2 (antisymm_of r hab.1 hbc.1)
