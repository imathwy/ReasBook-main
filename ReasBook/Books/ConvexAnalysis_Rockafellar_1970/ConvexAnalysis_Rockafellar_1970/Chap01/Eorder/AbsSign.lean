import Mathlib.Algebra.Order.WithBotTop.Operations
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Sign.Basic

/-!
Canonical absolute-value and sign owner layer for `WithBotTop α`.

This file is the generic `WithBotTop` replacement for the `abs/sign` part of
`Mathlib.Data.EReal.Inv`.

Unlike `EReal.abs`, whose codomain is the positive cone `ℝ≥0∞`, the generic owner here keeps the
codomain on the same surface `WithBotTop α`. This keeps the chapter-facing API canonical on the
`WithBotTop` layer while still isolating the finite `abs/sign` behavior.
-/

universe u

namespace WithBotTop

open SignType (sign)

section AbsCore

variable {α : Type u} [Lattice α] [AddGroup α]

/-- Absolute value on `WithBotTop α`: both boundary points map to `⊤`, and finite values use the
ambient absolute value on `α`. -/
protected def abs : WithBotTop α → WithBotTop α
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (a : α) => (|a| : α)

@[simp] theorem abs_top : WithBotTop.abs (⊤ : WithBotTop α) = ⊤ :=
  rfl

@[simp] theorem abs_bot : WithBotTop.abs (⊥ : WithBotTop α) = ⊤ :=
  rfl

@[simp] theorem coe_abs (a : α) : WithBotTop.abs (a : WithBotTop α) = (|a| : α) :=
  rfl

end AbsCore

section AbsLemmas

variable {α : Type u} [LinearOrder α] [AddGroup α] [AddLeftMono α]

@[simp] theorem abs_zero : WithBotTop.abs (0 : WithBotTop α) = 0 := by
  rw [show (0 : WithBotTop α) = ((0 : α) : WithBotTop α) by rfl, coe_abs, _root_.abs_zero]

@[simp] theorem abs_eq_zero_iff {x : WithBotTop α} : WithBotTop.abs x = 0 ↔ x = 0 := by
  cases x using WithBotTop.rec with
  | bot =>
      constructor
      · intro h
        exact False.elim (WithBotTop.top_ne_zero h)
      · intro h
        cases WithBotTop.bot_ne_coe h
  | top =>
      simp [WithBotTop.abs]
  | coe a =>
      rcases le_total a 0 with ha | ha
      · simp [WithBotTop.coe_abs, abs_of_nonpos ha]
      · rw [WithBotTop.coe_abs, abs_of_nonneg ha]

omit [AddLeftMono α] in
@[simp] theorem abs_neg : ∀ x : WithBotTop α, WithBotTop.abs (-x) = WithBotTop.abs x
  | ⊥ => rfl
  | ⊤ => rfl
  | (a : α) => by
      change WithBotTop.abs (((-a : α) : α) : WithBotTop α) = WithBotTop.abs (a : α)
      rw [WithBotTop.coe_abs, WithBotTop.coe_abs, _root_.abs_neg]

end AbsLemmas

section Sign

variable {α : Type u} [Zero α] [Preorder α] [DecidableLT α]

/-- Sign on `WithBotTop α`: `⊤` has positive sign, `⊥` has negative sign, and finite values use the
ambient sign on `α`. -/
protected def sign : WithBotTop α → SignType
  | ⊥ => -1
  | ⊤ => 1
  | (a : α) => sign a

theorem sign_top : WithBotTop.sign (⊤ : WithBotTop α) = 1 :=
  rfl

theorem sign_bot : WithBotTop.sign (⊥ : WithBotTop α) = -1 :=
  rfl

@[simp] theorem sign_coe (a : α) : WithBotTop.sign (a : WithBotTop α) = sign a :=
  rfl

end Sign

section SignNeg

variable {α : Type u} [AddGroup α] [Preorder α] [DecidableLT α] [AddLeftStrictMono α]

@[simp] theorem sign_neg : ∀ x : WithBotTop α, WithBotTop.sign (-x) = -WithBotTop.sign x
  | ⊥ => rfl
  | ⊤ => rfl
  | (a : α) => by
      simpa [WithBotTop.sign] using (Left.sign_neg a)

end SignNeg

section SignZero

variable {α : Type u} [LinearOrder α] [AddGroup α] [DecidableLT α]

@[simp] theorem sign_eq_zero_iff {x : WithBotTop α} :
    WithBotTop.sign x = 0 ↔ x = 0 := by
  sorry

end SignZero

section SignBoundaryIff

variable {α : Type u} [LinearOrder α] [AddGroup α] [DecidableLT α]

@[simp] theorem sign_eq_one_iff {x : WithBotTop α} :
    WithBotTop.sign x = 1 ↔ 0 < x ∨ x = ⊤ := by
  sorry

@[simp] theorem sign_eq_neg_one_iff {x : WithBotTop α} :
    WithBotTop.sign x = -1 ↔ x < 0 ∨ x = ⊥ := by
  sorry

@[simp] theorem sign_nonneg_iff {x : WithBotTop α} :
    0 ≤ WithBotTop.sign x ↔ 0 ≤ x := by
  sorry

@[simp] theorem sign_nonpos_iff {x : WithBotTop α} :
    WithBotTop.sign x ≤ 0 ↔ x ≤ 0 := by
  sorry

theorem sign_eq_sign_or_eq_neg {x y : WithBotTop α}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    WithBotTop.sign x = WithBotTop.sign y ∨ WithBotTop.sign x = -WithBotTop.sign y := by
  sorry

end SignBoundaryIff

section SignCoe

variable {α : Type u} [Ring α]

@[simp] theorem coe_sign (s : SignType) :
    ((((s : α) : α) : WithBotTop α)) = s := by
  sorry

end SignCoe

section AbsSignMul

variable {α : Type u} [LinearOrder α] [Ring α] [IsStrictOrderedRing α] [DecidableLT α]

omit [DecidableLT α] in
theorem abs_coe_lt_top (a : α) : WithBotTop.abs (a : WithBotTop α) < ⊤ := by
  sorry

theorem abs_mul (x y : WithBotTop α) :
    WithBotTop.abs (x * y) = WithBotTop.abs x * WithBotTop.abs y := by
  sorry

@[simp] theorem sign_mul (x y : WithBotTop α) :
    WithBotTop.sign (x * y) = WithBotTop.sign x * WithBotTop.sign y := by
  sorry

@[simp] theorem sign_mul_abs (x : WithBotTop α) :
    ((WithBotTop.sign x : α) : WithBotTop α) * WithBotTop.abs x = x := by
  sorry

@[simp] theorem abs_mul_sign (x : WithBotTop α) :
    WithBotTop.abs x * ((WithBotTop.sign x : α) : WithBotTop α) = x := by
  sorry

theorem sign_mul_self (x : WithBotTop α) :
    (((WithBotTop.sign x : α) : α) : WithBotTop α) * x = WithBotTop.abs x := by
  sorry

theorem self_mul_sign (x : WithBotTop α) :
    x * (((WithBotTop.sign x : α) : α) : WithBotTop α) = WithBotTop.abs x := by
  sorry

theorem sign_eq_and_abs_eq_iff_eq {x y : WithBotTop α} :
    WithBotTop.abs x = WithBotTop.abs y ∧ WithBotTop.sign x = WithBotTop.sign y ↔ x = y := by
  sorry

end AbsSignMul

section OrderFacing

variable {α : Type u} [LinearOrder α] [Ring α] [IsStrictOrderedRing α] [DecidableLT α]

theorem le_iff_sign {x y : WithBotTop α} :
    x ≤ y ↔
      WithBotTop.sign x < WithBotTop.sign y ∨
        WithBotTop.sign x = SignType.neg ∧
            WithBotTop.sign y = SignType.neg ∧
            WithBotTop.abs y ≤ WithBotTop.abs x ∨
          WithBotTop.sign x = SignType.zero ∧
            WithBotTop.sign y = SignType.zero ∨
            WithBotTop.sign x = SignType.pos ∧
              WithBotTop.sign y = SignType.pos ∧
              WithBotTop.abs x ≤ WithBotTop.abs y := by
  sorry

theorem lt_iff_sign {x y : WithBotTop α} :
    x < y ↔
      WithBotTop.sign x < WithBotTop.sign y ∨
        WithBotTop.sign x = SignType.neg ∧
            WithBotTop.sign y = SignType.neg ∧
            WithBotTop.abs y < WithBotTop.abs x ∨
          WithBotTop.sign x = SignType.pos ∧
            WithBotTop.sign y = SignType.pos ∧
            WithBotTop.abs x < WithBotTop.abs y := by
  sorry

end OrderFacing

section AbsSignInvDiv

variable {α : Type u} [LinearOrder α] [Field α] [IsStrictOrderedRing α] [DecidableLT α]

omit [DecidableLT α] in
theorem abs_inv (x : WithBotTop α) :
    WithBotTop.abs x⁻¹ = (WithBotTop.abs x)⁻¹ := by
  sorry

@[simp] theorem sign_inv (x : WithBotTop α) :
    WithBotTop.sign x⁻¹ = WithBotTop.sign x := by
  sorry

theorem sign_mul_inv_abs (x : WithBotTop α) :
    (((WithBotTop.sign x : α) : α) : WithBotTop α) * (WithBotTop.abs x)⁻¹ = x⁻¹ := by
  sorry

theorem abs_div (x y : WithBotTop α) :
    WithBotTop.abs (x / y) = WithBotTop.abs x / WithBotTop.abs y := by
  sorry

@[simp] theorem sign_div (x y : WithBotTop α) :
    WithBotTop.sign (x / y) = WithBotTop.sign x / WithBotTop.sign y := by
  sorry

end AbsSignInvDiv

end WithBotTop
