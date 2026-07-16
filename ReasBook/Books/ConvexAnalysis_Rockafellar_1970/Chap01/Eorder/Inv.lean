import ConvexAnalysis_Rockafellar_1970.Chap01.Eorder.MulZero
import Mathlib.Algebra.Order.Field.Basic

/-!
Primitive inversion and division on `WithBotTop α`.

This file is intentionally kept on the primitive `inv/div` layer for the new canonical
multiplication on `WithBotTop α`. It does not attempt to rebuild the full higher algebraic hierarchy
yet.
-/

universe u

namespace WithBotTop

section Inv

variable {α : Type u} [Inv α] [Zero α]

/-- Canonical inversion on `WithBotTop α`: both boundary points invert to `0`, while coercions use
the inverse on `α`. -/
protected def inv : WithBotTop α → WithBotTop α
  | ⊥ => 0
  | ⊤ => 0
  | (a : α) => (a⁻¹ : α)

instance instInv : Inv (WithBotTop α) := ⟨WithBotTop.inv⟩

@[simp] theorem inv_bot : (⊥ : WithBotTop α)⁻¹ = 0 :=
  rfl

@[simp] theorem inv_top : (⊤ : WithBotTop α)⁻¹ = 0 :=
  rfl

@[simp] theorem coe_inv (a : α) : ((a⁻¹ : α) : WithBotTop α) = (a : WithBotTop α)⁻¹ :=
  rfl

end Inv

section GroupWithZero

variable {α : Type u} [GroupWithZero α]

@[simp] theorem inv_zero : (0 : WithBotTop α)⁻¹ = 0 := by
  change (((0 : α)⁻¹ : α) : WithBotTop α) = (0 : WithBotTop α)
  rw [_root_.inv_zero]
  rfl

@[simp] theorem inv_one : (1 : WithBotTop α)⁻¹ = 1 := by
  change (((1 : α)⁻¹ : α) : WithBotTop α) = (1 : WithBotTop α)
  rw [_root_.inv_one]
  rfl

theorem inv_inv {x : WithBotTop α} (hx_top : x ≠ ⊤) (hx_bot : x ≠ ⊥) : x⁻¹⁻¹ = x := by
  cases x using WithBotTop.rec with
  | bot => contradiction
  | top => contradiction
  | coe a =>
      change ((((a⁻¹)⁻¹ : α) : α) : WithBotTop α) = (a : WithBotTop α)
      rw [_root_.inv_inv]

end GroupWithZero

section OrderedInv

variable {α : Type u} [Preorder α] [GroupWithZero α]

theorem bot_lt_inv (x : WithBotTop α) : (⊥ : WithBotTop α) < x⁻¹ := by
  cases x using WithBotTop.rec with
  | bot =>
      simpa only [WithBotTop.inv_bot] using (WithBotTop.bot_lt_zero (α := α))
  | top =>
      simpa only [WithBotTop.inv_top] using (WithBotTop.bot_lt_zero (α := α))
  | coe a =>
      change (⊥ : WithBotTop α) < ((a⁻¹ : α) : WithBotTop α)
      exact WithBot.bot_lt_coe _

theorem inv_lt_top (x : WithBotTop α) : x⁻¹ < (⊤ : WithBotTop α) := by
  cases x using WithBotTop.rec with
  | bot =>
      simpa [WithBotTop.inv_bot] using (WithBotTop.zero_lt_top (α := α))
  | top =>
      simpa [WithBotTop.inv_top] using (WithBotTop.zero_lt_top (α := α))
  | coe a =>
      simpa [WithBotTop.coe_inv] using
        (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top (a⁻¹ : α)))

end OrderedInv

section OrderedCommGroupWithZero

variable {α : Type u} [LinearOrderedCommGroupWithZero α]

theorem inv_nonneg_of_nonneg {a : WithBotTop α} (h : (0 : WithBotTop α) ≤ a) :
    (0 : WithBotTop α) ≤ a⁻¹ := by
  cases a using WithBotTop.rec with
  | bot => simp [WithBotTop.inv_bot]
  | top => simp [WithBotTop.inv_top]
  | coe a =>
      change ((0 : α) : WithBotTop α) ≤ ((a⁻¹ : α) : WithBotTop α)
      exact (WithBotTop.coe_nonneg).2 <| _root_.inv_nonneg_of_nonneg ((WithBotTop.coe_nonneg).mp h)

theorem inv_nonpos_of_nonpos {a : WithBotTop α} (h : a ≤ (0 : WithBotTop α)) :
    a⁻¹ ≤ (0 : WithBotTop α) := by
  cases a using WithBotTop.rec with
  | bot => simp [WithBotTop.inv_bot]
  | top => simp [WithBotTop.inv_top]
  | coe a =>
      change ((a⁻¹ : α) : WithBotTop α) ≤ ((0 : α) : WithBotTop α)
      exact (WithBotTop.coe_nonpos).2 <| (_root_.inv_nonpos).2 ((WithBotTop.coe_nonpos).mp h)

theorem inv_pos_of_pos_ne_top {a : WithBotTop α} (h : (0 : WithBotTop α) < a) (h_top : a ≠ ⊤) :
    (0 : WithBotTop α) < a⁻¹ := by
  cases a using WithBotTop.rec with
  | bot => exact (not_lt_bot h).elim
  | top => exact (h_top rfl).elim
  | coe a =>
      change ((0 : α) : WithBotTop α) < ((a⁻¹ : α) : WithBotTop α)
      exact (WithBotTop.coe_pos).2 <| _root_.inv_pos_of_pos ((WithBotTop.coe_pos).mp h)

theorem inv_neg_of_neg_ne_bot {a : WithBotTop α} (h : a < (0 : WithBotTop α)) (h_bot : a ≠ ⊥) :
    a⁻¹ < (0 : WithBotTop α) := by
  cases a using WithBotTop.rec with
  | bot => exact (h_bot rfl).elim
  | top => exact (not_top_lt h).elim
  | coe a =>
      change ((a⁻¹ : α) : WithBotTop α) < ((0 : α) : WithBotTop α)
      exact (WithBotTop.coe_neg').2 <| (_root_.inv_lt_zero).2 ((WithBotTop.coe_neg').mp h)

theorem inv_strictAntiOn : StrictAntiOn (fun (x : WithBotTop α) => x⁻¹) (Set.Ioi (0 : WithBotTop α)) := by
  intro a ha b hb hab
  have ha' : (0 : WithBotTop α) < a := by simpa only [Set.mem_Ioi] using ha
  have hb' : (0 : WithBotTop α) < b := by simpa only [Set.mem_Ioi] using hb
  cases a using WithBotTop.rec with
  | bot => exact (not_lt_bot ha').elim
  | top => exact (not_top_lt hab).elim
  | coe a =>
      match b with
      | ⊥ => exact (not_lt_bot hb').elim
      | ⊤ => simpa [WithBotTop.inv_top] using
          inv_pos_of_pos_ne_top ha' (WithBotTop.coe_ne_top _)
      | (b : α) =>
          change (((b⁻¹ : α) : WithBotTop α) < ((a⁻¹ : α) : WithBotTop α))
          exact (WithBotTop.coe_lt_coe).2 <|
            _root_.inv_strictAnti₀ ((WithBotTop.coe_pos).1 ha') ((WithBotTop.coe_lt_coe).1 hab)

end OrderedCommGroupWithZero

section Div

variable {α : Type u} [LT α] [DecidableLT α] [Std.Irrefl (α := α) (· < ·)] [MulZeroClass α]
variable [Inv α]

/-- Canonical division on `WithBotTop α`, defined by multiplication with the canonical inverse. -/
protected def div (a b : WithBotTop α) : WithBotTop α :=
  a * b⁻¹

instance instDiv : Div (WithBotTop α) := ⟨WithBotTop.div⟩

omit [Std.Irrefl (α := α) (· < ·)] in
@[simp] theorem div_eq_mul_inv (a b : WithBotTop α) : a / b = a * b⁻¹ :=
  rfl

@[simp] theorem div_top (a : WithBotTop α) : a / ⊤ = 0 := by
  rw [div_eq_mul_inv, inv_top, mul_zero]

@[simp] theorem div_bot (a : WithBotTop α) : a / ⊥ = 0 := by
  rw [div_eq_mul_inv, inv_bot, mul_zero]

@[simp] theorem zero_div (a : WithBotTop α) : 0 / a = 0 := by
  rw [div_eq_mul_inv, zero_mul]

end Div

section DivZero

variable {α : Type u} [LT α] [DecidableLT α] [Std.Irrefl (α := α) (· < ·)]
variable [GroupWithZero α]

omit [Std.Irrefl (α := α) (· < ·)] in
@[simp] theorem coe_div (a b : α) :
    ((a / b : α) : WithBotTop α) = (a : WithBotTop α) / (b : WithBotTop α) := by
  rw [_root_.div_eq_mul_inv, WithBotTop.div_eq_mul_inv, WithBotTop.coe_mul, WithBotTop.coe_inv]

@[simp] theorem div_zero (a : WithBotTop α) : a / 0 = 0 := by
  rw [div_eq_mul_inv, inv_zero, mul_zero]

end DivZero

end WithBotTop
