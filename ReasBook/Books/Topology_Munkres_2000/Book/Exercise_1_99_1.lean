module

public import Mathlib.Data.Set.CoeSort
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.RelClasses

public section

universe u v

/-- Exercise 1.99.1: General principle of recursive definition on a well-ordered
type. A rule assigning an element of `C` to every map from a strict section
`Set.Iio α` determines a unique function on the whole type. -/
theorem existsUniqueRecursiveDefinition
    {J : Type u} [Preorder J] [WellFoundedLT J] {C : Type v}
    (ρ : {α : J} → (Set.Iio α → C) → C) :
    ∃! h : J → C, ∀ α : J, h α = ρ (fun β : Set.Iio α ↦ h β) := by
  let step (α : J) (previous : ∀ β : J, β < α → C) : C :=
    ρ (fun β ↦ previous β β.property)
  let h := WellFoundedLT.fix step
  have h_eq (α : J) : h α = ρ (fun β : Set.Iio α ↦ h β) := by
    dsimp only [h]
    rw [WellFoundedLT.fix_eq]
  refine ⟨h, h_eq, fun g g_eq ↦ ?_⟩
  funext α
  induction α using WellFoundedLT.induction with
  | _ α ih =>
      rw [g_eq, h_eq]
      congr
      funext β
      exact ih β β.property

end
