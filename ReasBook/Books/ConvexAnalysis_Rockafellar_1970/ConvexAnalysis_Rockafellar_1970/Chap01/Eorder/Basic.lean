/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Ze Yuan
-/
module

public import Mathlib.Order.WithBotTop
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-! # The additive structure on `WithBotTop α` -/

@[expose] public section

variable {α : Type*}

namespace WithBotTop

section Add

variable [Add α] {a b : α} {x y : WithBotTop α}

@[simp, norm_cast]
theorem coe_add : (a + b : α) = (a : WithBotTop α) + b := rfl

@[simp]
theorem add_bot (x : WithBotTop α) : x + ⊥ = ⊥ :=
  WithBot.add_bot x

@[simp]
theorem bot_add (x : WithBotTop α) : ⊥ + x = ⊥ :=
  WithBot.bot_add x

@[simp]
theorem top_add_top : (⊤ : WithBotTop α) + ⊤ = ⊤ :=
  rfl

@[simp]
theorem top_add_of_ne_bot (hx : x ≠ ⊥) : (⊤ : WithBotTop α) + x = ⊤ := by
  cases x using WithBotTop.rec
  · contradiction
  · rfl
  · rfl

@[simp]
theorem add_top_of_ne_bot (hx : x ≠ ⊥) : x + (⊤ : WithBotTop α) = ⊤ := by
  cases x using WithBotTop.rec
  · contradiction
  · rfl
  · rfl

@[simp]
theorem top_add_coe (a : α) : (⊤ : WithBotTop α) + a = ⊤ :=
  top_add_of_ne_bot (x := (a : WithBotTop α)) coe_ne_bot

@[simp]
theorem coe_add_top (a : α) : (a : WithBotTop α) + ⊤ = ⊤ :=
  add_top_of_ne_bot (x := (a : WithBotTop α)) coe_ne_bot

@[simp]
theorem top_add_bot : (⊤ : WithBotTop α) + ⊥ = ⊥ :=
  add_bot _

@[simp]
theorem bot_add_top : (⊥ : WithBotTop α) + ⊤ = ⊥ :=
  bot_add _

theorem top_add_iff_ne_bot {x : WithBotTop α} : (⊤ : WithBotTop α) + x = ⊤ ↔ x ≠ ⊥ := by
  constructor
  · intro hx
    rintro rfl
    rw [top_add_bot] at hx
    exact bot_ne_top hx
  · exact top_add_of_ne_bot

theorem add_top_iff_ne_bot {x : WithBotTop α} : x + (⊤ : WithBotTop α) = ⊤ ↔ x ≠ ⊥ := by
  constructor
  · intro hx
    rintro rfl
    rw [bot_add_top] at hx
    exact bot_ne_top hx
  · exact add_top_of_ne_bot

@[simp]
theorem add_eq_bot_iff : x + y = (⊥ : WithBotTop α) ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot

theorem add_ne_bot_iff : x + y ≠ (⊥ : WithBotTop α) ↔ x ≠ ⊥ ∧ y ≠ ⊥ :=
  WithBot.add_ne_bot

theorem add_ne_top (hx : x ≠ ⊥) (hx' : x ≠ ⊤) (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ (⊤ : WithBotTop α) := by
  lift x to α using ⟨hx, hx'⟩
  lift y to α using ⟨hy, hy'⟩
  rw [← coe_add]
  exact coe_ne_top

theorem add_ne_top_iff_ne_top₂ (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ (⊤ : WithBotTop α) ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  constructor
  · intro h
    constructor
    · intro hx'
      exact h (hx' ▸ top_add_of_ne_bot hy)
    · intro hy'
      exact h (hy' ▸ add_top_of_ne_bot hx)
  · rintro ⟨hx', hy'⟩
    exact add_ne_top hx hx' hy hy'

theorem add_ne_top_iff_ne_top_left (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ (⊤ : WithBotTop α) ↔ x ≠ ⊤ := by
  cases x using WithBotTop.rec <;> simp [add_ne_top_iff_ne_top₂, hy, hy']

theorem add_ne_top_iff_ne_top_right (hx : x ≠ ⊥) (hx' : x ≠ ⊤) :
    x + y ≠ (⊤ : WithBotTop α) ↔ y ≠ ⊤ := by
  cases y using WithBotTop.rec <;> simp [add_ne_top_iff_ne_top₂, hx, hx']

theorem add_ne_top_iff_of_ne_bot_of_ne_top (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ (⊤ : WithBotTop α) ↔ x ≠ ⊤ :=
  add_ne_top_iff_ne_top_left hy hy'

end Add

section AddLT

variable [Add α] [LT α] {x y : WithBotTop α}

@[simp] theorem bot_lt_add_iff : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [WithBot.bot_lt_iff_ne_bot]

end AddLT

section AddMonoid

variable [AddMonoid α] {a : α}

@[simp, norm_cast]
theorem coe_nsmul (a : α) (n : ℕ) :
    ((n • a : α) : WithBotTop α) = n • (a : WithBotTop α) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [succ_nsmul, ih, coe_add]

end AddMonoid

end WithBotTop
