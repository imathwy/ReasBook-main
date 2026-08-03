module

public import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Basic

public section

universe u

/-- Exercise 9.6 (1): No type with a proposed membership relation can contain
an element representing every subset of itself. -/
theorem noUniversalSet {α : Type u} (mem : α → α → Prop) :
    ¬ ∃ represent : Set α → α, ∀ A x, mem x (represent A) ↔ x ∈ A := by
  rintro ⟨represent, hrepresent⟩
  apply Function.cantor_injective represent
  intro A B hab
  ext x
  rw [← hrepresent A x, ← hrepresent B x, hab]

/-- Exercise 9.6 (2): No element of a type can represent exactly the elements
that are not related to themselves by a proposed membership relation. -/
theorem noRussellSet {α : Type u} (mem : α → α → Prop) :
    ¬ ∃ b : α, ∀ x : α, mem x b ↔ ¬ mem x x := by
  rintro ⟨b, hb⟩
  exact iff_not_self (hb b)
