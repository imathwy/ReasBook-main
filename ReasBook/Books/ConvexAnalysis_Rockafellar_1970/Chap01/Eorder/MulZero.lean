/-
Copyright (c) 2024 Lacitpille. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacitpille
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Sign.Basic
import ConvexAnalysis_Rockafellar_1970.Chap01.Mathlib_Order_Interval_Set_WithBotTop

/-!
Canonical multiplication on `WithBotTop α`.

The multiplication on `WithBotTop α` is sign-sensitive at the boundary:

- `⊤ * ⊤ = ⊤`
- `⊤ * ⊥ = ⊥`
- `⊥ * ⊤ = ⊥`
- `⊥ * ⊥ = ⊤`

Finite values multiply as usual, and the sign of a finite value determines its product with `⊤`
or `⊥`.
-/

universe u

namespace WithBotTop

section Sign

variable {α : Type u} [LT α] [DecidableLT α] [Zero α]

/-- The sign of a finite element relative to `0`, encoded as `SignType`. -/
def sign0 (a : α) : SignType :=
  if a < 0 then .neg else if 0 < a then .pos else .zero

@[simp] theorem sign0_neg {a : α} (ha : a < 0) : sign0 a = .neg := by
  simp [WithBotTop.sign0, ha]

@[simp] theorem sign0_zero [Std.Irrefl (α := α) (· < ·)] : sign0 (0 : α) = .zero := by
  simp [WithBotTop.sign0, irrefl]

@[simp] theorem sign0_eq_zero [Std.Irrefl (α := α) (· < ·)] {a : α} (ha : a = 0) :
    sign0 a = .zero := by
  subst a
  exact sign0_zero (α := α)

@[simp] theorem sign0_pos [IsStrictOrder α (· < ·)] {a : α} (ha : 0 < a) :
    sign0 a = .pos := by
  have h : ¬ a < 0 := by
    intro h'
    exact (irrefl a) (_root_.trans h' ha)
  simp [WithBotTop.sign0, h, ha]

end Sign

section Mul

variable {α : Type u} [LT α] [DecidableLT α] [Zero α] [Mul α]

/-- Canonical multiplication on `WithBotTop α`: finite values multiply as usual, while the sign of
finite values controls multiplication by `⊤` and `⊥`. -/
protected def mul : WithBotTop α → WithBotTop α → WithBotTop α
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | (a : α), (b : α) => ((a * b : α) : WithBotTop α)
  | (a : α), ⊤ =>
      match sign0 a with
      | .neg => ⊥
      | .zero => 0
      | .pos => ⊤
  | ⊤, (a : α) =>
      match sign0 a with
      | .neg => ⊥
      | .zero => 0
      | .pos => ⊤
  | (a : α), ⊥ =>
      match sign0 a with
      | .neg => ⊤
      | .zero => 0
      | .pos => ⊥
  | ⊥, (a : α) =>
      match sign0 a with
      | .neg => ⊤
      | .zero => 0
      | .pos => ⊥

instance instMul : Mul (WithBotTop α) := ⟨WithBotTop.mul⟩

instance instSMul : SMul α (WithBotTop α) := ⟨fun a x => (a : WithBotTop α) * x⟩

@[simp] theorem smul_def (a : α) (x : WithBotTop α) :
    a • x = (a : WithBotTop α) * x :=
  rfl

section One

variable [One α]

instance instOne : One (WithBotTop α) := ⟨((1 : α) : WithBotTop α)⟩

end One

@[simp] theorem coe_mul (a b : α) :
    ((a * b : α) : WithBotTop α) = (a : WithBotTop α) * (b : WithBotTop α) :=
  rfl

@[simp] theorem coe_smul (a b : α) :
    a • (b : WithBotTop α) = ((a * b : α) : WithBotTop α) := by
  rfl

@[simp] theorem top_mul_top :
    (⊤ : WithBotTop α) * (⊤ : WithBotTop α) = ⊤ :=
  rfl

@[simp] theorem top_mul_bot :
    (⊤ : WithBotTop α) * (⊥ : WithBotTop α) = ⊥ :=
  rfl

@[simp] theorem bot_mul_top :
    (⊥ : WithBotTop α) * (⊤ : WithBotTop α) = ⊥ :=
  rfl

@[simp] theorem bot_mul_bot :
    (⊥ : WithBotTop α) * (⊥ : WithBotTop α) = ⊤ :=
  rfl

@[simp] theorem top_mul_coe_of_pos [IsStrictOrder α (· < ·)] {a : α} (ha : 0 < a) :
    (⊤ : WithBotTop α) * (a : WithBotTop α) = ⊤ := by
  change
      (match sign0 a with
      | .neg => (⊥ : WithBotTop α)
      | .zero => 0
      | .pos => ⊤) = ⊤
  rw [WithBotTop.sign0_pos ha]

@[simp] theorem top_mul_coe_of_neg {a : α} (ha : a < 0) :
    (⊤ : WithBotTop α) * (a : WithBotTop α) = ⊥ := by
  change
      (match sign0 a with
      | .neg => (⊥ : WithBotTop α)
      | .zero => 0
      | .pos => ⊤) = ⊥
  rw [WithBotTop.sign0_neg ha]

@[simp] theorem top_mul_coe_of_zero [Std.Irrefl (α := α) (· < ·)] :
    (⊤ : WithBotTop α) * ((0 : α) : WithBotTop α) = 0 := by
  change
      (match sign0 (0 : α) with
      | .neg => (⊥ : WithBotTop α)
      | .zero => 0
      | .pos => ⊤) = 0
  rw [WithBotTop.sign0_zero (α := α)]

@[simp] theorem bot_mul_coe_of_pos [IsStrictOrder α (· < ·)] {a : α} (ha : 0 < a) :
    (⊥ : WithBotTop α) * (a : WithBotTop α) = ⊥ := by
  change
      (match sign0 a with
      | .neg => (⊤ : WithBotTop α)
      | .zero => 0
      | .pos => ⊥) = ⊥
  rw [WithBotTop.sign0_pos ha]

@[simp] theorem bot_mul_coe_of_neg {a : α} (ha : a < 0) :
    (⊥ : WithBotTop α) * (a : WithBotTop α) = ⊤ := by
  change
      (match sign0 a with
      | .neg => (⊤ : WithBotTop α)
      | .zero => 0
      | .pos => ⊥) = ⊤
  rw [WithBotTop.sign0_neg ha]

@[simp] theorem bot_mul_coe_of_zero [Std.Irrefl (α := α) (· < ·)] :
    (⊥ : WithBotTop α) * ((0 : α) : WithBotTop α) = 0 := by
  change
      (match sign0 (0 : α) with
      | .neg => (⊤ : WithBotTop α)
      | .zero => 0
      | .pos => ⊥) = 0
  rw [WithBotTop.sign0_zero (α := α)]

@[simp] theorem coe_mul_top_of_pos [IsStrictOrder α (· < ·)] {a : α} (ha : 0 < a) :
    (a : WithBotTop α) * (⊤ : WithBotTop α) = ⊤ := by
  change
      (match sign0 a with
      | .neg => (⊥ : WithBotTop α)
      | .zero => 0
      | .pos => ⊤) = ⊤
  rw [WithBotTop.sign0_pos ha]

@[simp] theorem coe_mul_top_of_neg {a : α} (ha : a < 0) :
    (a : WithBotTop α) * (⊤ : WithBotTop α) = ⊥ := by
  change
      (match sign0 a with
      | .neg => (⊥ : WithBotTop α)
      | .zero => 0
      | .pos => ⊤) = ⊥
  rw [WithBotTop.sign0_neg ha]

@[simp] theorem coe_mul_top_of_zero [Std.Irrefl (α := α) (· < ·)] :
    ((0 : α) : WithBotTop α) * (⊤ : WithBotTop α) = 0 := by
  change
      (match sign0 (0 : α) with
      | .neg => (⊥ : WithBotTop α)
      | .zero => 0
      | .pos => ⊤) = 0
  rw [WithBotTop.sign0_zero (α := α)]

@[simp] theorem coe_mul_bot_of_pos [IsStrictOrder α (· < ·)] {a : α} (ha : 0 < a) :
    (a : WithBotTop α) * (⊥ : WithBotTop α) = ⊥ := by
  change
      (match sign0 a with
      | .neg => (⊤ : WithBotTop α)
      | .zero => 0
      | .pos => ⊥) = ⊥
  rw [WithBotTop.sign0_pos ha]

@[simp] theorem coe_mul_bot_of_neg {a : α} (ha : a < 0) :
    (a : WithBotTop α) * (⊥ : WithBotTop α) = ⊤ := by
  change
      (match sign0 a with
      | .neg => (⊤ : WithBotTop α)
      | .zero => 0
      | .pos => ⊥) = ⊤
  rw [WithBotTop.sign0_neg ha]

@[simp] theorem coe_mul_bot_of_zero [Std.Irrefl (α := α) (· < ·)] :
    ((0 : α) : WithBotTop α) * (⊥ : WithBotTop α) = 0 := by
  change
      (match sign0 (0 : α) with
      | .neg => (⊤ : WithBotTop α)
      | .zero => 0
      | .pos => ⊥) = 0
  rw [WithBotTop.sign0_zero (α := α)]

end Mul

section Induction

variable {α : Type u} [LinearOrder α] [Zero α]

/-- Induct on two `WithBotTop α`s by performing case splits on the sign of one whenever the other
is infinite. -/
@[elab_as_elim]
theorem induction₂ {P : WithBotTop α → WithBotTop α → Prop}
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : α, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : α, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : ∀ x : α, 0 < x → P x ⊤) (pos_bot : ∀ x : α, 0 < x → P x ⊥)
    (zero_top : P 0 ⊤) (coe_coe : ∀ x y : α, P x y) (zero_bot : P 0 ⊥)
    (neg_top : ∀ x : α, x < 0 → P x ⊤) (neg_bot : ∀ x : α, x < 0 → P x ⊥)
    (bot_top : P ⊥ ⊤) (bot_pos : ∀ x : α, 0 < x → P ⊥ x) (bot_zero : P ⊥ 0)
    (bot_neg : ∀ x : α, x < 0 → P ⊥ x) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : α) => by
      rcases lt_trichotomy y 0 with (hy | rfl | hy)
      exacts [bot_neg y hy, bot_zero, bot_pos y hy]
  | ⊥, ⊤ => bot_top
  | (x : α), ⊥ => by
      rcases lt_trichotomy x 0 with (hx | rfl | hx)
      exacts [neg_bot x hx, zero_bot, pos_bot x hx]
  | (x : α), (y : α) => coe_coe _ _
  | (x : α), ⊤ => by
      rcases lt_trichotomy x 0 with (hx | rfl | hx)
      exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : α) => by
      rcases lt_trichotomy y 0 with (hy | rfl | hy)
      exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `WithBotTop α`s by performing case splits on the sign of one whenever the other
is infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
theorem induction₂_symm {P : WithBotTop α → WithBotTop α → Prop}
    (symm : ∀ {x y}, P x y → P y x) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : α, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : α, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_bot : ∀ x : α, 0 < x → P x ⊥) (coe_coe : ∀ x y : α, P x y) (zero_bot : P 0 ⊥)
    (neg_bot : ∀ x : α, x < 0 → P x ⊥) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
  @induction₂ α _ _ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot
    (symm top_bot) (fun _ h => symm <| pos_bot _ h) (symm zero_bot)
    (fun _ h => symm <| neg_bot _ h) bot_bot

end Induction

section ZeroOrder

variable {α : Type u} [Preorder α] [Zero α] {a : α}

@[simp] theorem coe_nonneg : (0 : WithBotTop α) ≤ a ↔ 0 ≤ a :=
  coe_le_coe

@[simp] theorem coe_nonpos : (a : WithBotTop α) ≤ 0 ↔ a ≤ 0 :=
  coe_le_coe

@[simp] theorem coe_pos : (0 : WithBotTop α) < a ↔ 0 < a :=
  coe_lt_coe

@[simp] theorem coe_neg' : (a : WithBotTop α) < 0 ↔ a < 0 :=
  coe_lt_coe

theorem bot_lt_zero : (⊥ : WithBotTop α) < 0 :=
  WithBot.bot_lt_coe _

theorem zero_lt_top : (0 : WithBotTop α) < ⊤ :=
  WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)

omit [Preorder α] in
@[simp] theorem bot_ne_zero : (⊥ : WithBotTop α) ≠ 0 :=
  WithBot.bot_ne_coe

omit [Preorder α] in
@[simp] theorem zero_ne_bot : (0 : WithBotTop α) ≠ (⊥ : WithBotTop α) :=
  WithBot.coe_ne_bot

omit [Preorder α] in
@[simp] theorem top_ne_zero : (⊤ : WithBotTop α) ≠ 0 :=
  fun h => WithTop.top_ne_coe (WithBot.coe_injective h)

omit [Preorder α] in
@[simp] theorem zero_ne_top : (0 : WithBotTop α) ≠ (⊤ : WithBotTop α) :=
  fun h => WithTop.coe_ne_top (WithBot.coe_injective h)

end ZeroOrder

section MulOrder

variable {α : Type u} [LinearOrder α] [DecidableLT α] [Zero α] [Mul α]

theorem mul_top_of_pos {x : WithBotTop α} (h : (0 : WithBotTop α) < x) :
    x * (⊤ : WithBotTop α) = ⊤ := by
  cases x using WithBotTop.rec with
  | bot =>
      exact (not_lt_of_ge bot_le h).elim
  | top =>
      rfl
  | coe a =>
      exact WithBotTop.coe_mul_top_of_pos (coe_lt_coe.mp h)

theorem mul_top_of_neg {x : WithBotTop α} (h : x < (0 : WithBotTop α)) :
    x * (⊤ : WithBotTop α) = ⊥ := by
  cases x using WithBotTop.rec with
  | bot =>
      rfl
  | top =>
      exact (not_lt_of_ge le_top h).elim
  | coe a =>
      exact WithBotTop.coe_mul_top_of_neg (coe_lt_coe.mp h)

theorem top_mul_of_pos {x : WithBotTop α} (h : (0 : WithBotTop α) < x) :
    (⊤ : WithBotTop α) * x = ⊤ := by
  cases x using WithBotTop.rec with
  | bot =>
      exact (not_lt_of_ge bot_le h).elim
  | top =>
      rfl
  | coe a =>
      exact WithBotTop.top_mul_coe_of_pos (coe_lt_coe.mp h)

theorem top_mul_of_neg {x : WithBotTop α} (h : x < (0 : WithBotTop α)) :
    (⊤ : WithBotTop α) * x = ⊥ := by
  cases x using WithBotTop.rec with
  | bot =>
      rfl
  | top =>
      exact (not_lt_of_ge le_top h).elim
  | coe a =>
      exact WithBotTop.top_mul_coe_of_neg (coe_lt_coe.mp h)

theorem mul_bot_of_pos {x : WithBotTop α} (h : (0 : WithBotTop α) < x) :
    x * (⊥ : WithBotTop α) = ⊥ := by
  cases x using WithBotTop.rec with
  | bot =>
      exact (not_lt_of_ge bot_le h).elim
  | top =>
      rfl
  | coe a =>
      exact WithBotTop.coe_mul_bot_of_pos (coe_lt_coe.mp h)

theorem mul_bot_of_neg {x : WithBotTop α} (h : x < (0 : WithBotTop α)) :
    x * (⊥ : WithBotTop α) = ⊤ := by
  cases x using WithBotTop.rec with
  | bot =>
      rfl
  | top =>
      exact (not_lt_of_ge le_top h).elim
  | coe a =>
      exact WithBotTop.coe_mul_bot_of_neg (coe_lt_coe.mp h)

theorem bot_mul_of_pos {x : WithBotTop α} (h : (0 : WithBotTop α) < x) :
    (⊥ : WithBotTop α) * x = ⊥ := by
  cases x using WithBotTop.rec with
  | bot =>
      exact (not_lt_of_ge bot_le h).elim
  | top =>
      rfl
  | coe a =>
      exact WithBotTop.bot_mul_coe_of_pos (coe_lt_coe.mp h)

theorem bot_mul_of_neg {x : WithBotTop α} (h : x < (0 : WithBotTop α)) :
    (⊥ : WithBotTop α) * x = ⊤ := by
  cases x using WithBotTop.rec with
  | bot =>
      rfl
  | top =>
      exact (not_lt_of_ge le_top h).elim
  | coe a =>
      exact WithBotTop.bot_mul_coe_of_neg (coe_lt_coe.mp h)

end MulOrder

section OrderedCommGroupWithZero

variable {α : Type u} [LinearOrderedCommGroupWithZero α]

theorem mul_pos {a b : WithBotTop α} (ha : (0 : WithBotTop α) < a) (hb : (0 : WithBotTop α) < b) :
    (0 : WithBotTop α) < a * b := by
  cases a using WithBotTop.rec with
  | bot =>
      exact (not_lt_of_ge bot_le ha).elim
  | top =>
      cases b using WithBotTop.rec with
      | bot =>
          exact (not_lt_of_ge bot_le hb).elim
      | top =>
          exact WithBot.toDual_lt_toDual_iff.mp ha
      | coe b =>
          rw [WithBotTop.top_mul_coe_of_pos (coe_lt_coe.mp hb)]
          exact WithBot.toDual_lt_toDual_iff.mp ha
  | coe a =>
      cases b using WithBotTop.rec with
      | bot =>
          exact (not_lt_of_ge bot_le hb).elim
      | top =>
          rw [WithBotTop.coe_mul_top_of_pos (coe_lt_coe.mp ha)]
          exact WithBot.toDual_lt_toDual_iff.mp hb
      | coe b =>
          change ((0 : α) : WithBotTop α) < (((a * b : α) : α) : WithBotTop α)
          rw [coe_lt_coe]
          exact _root_.mul_pos (coe_lt_coe.mp ha) (coe_lt_coe.mp hb)

end OrderedCommGroupWithZero

section MulZeroClass

variable {α : Type u} [LT α] [DecidableLT α] [Std.Irrefl (α := α) (· < ·)] [MulZeroClass α]

@[simp] theorem mul_zero : ∀ x : WithBotTop α, x * (0 : WithBotTop α) = 0
  | ⊥ => by
      change
          (match sign0 (0 : α) with
          | .neg => (⊤ : WithBotTop α)
          | .zero => 0
          | .pos => ⊥) = 0
      rw [WithBotTop.sign0_zero (α := α)]
  | ⊤ => by
      change
          (match sign0 (0 : α) with
          | .neg => (⊥ : WithBotTop α)
          | .zero => 0
          | .pos => ⊤) = 0
      rw [WithBotTop.sign0_zero (α := α)]
  | (a : α) => by
      change ((a * 0 : α) : WithBotTop α) = ((0 : α) : WithBotTop α)
      rw [MulZeroClass.mul_zero]

@[simp] theorem zero_mul : ∀ x : WithBotTop α, (0 : WithBotTop α) * x = 0
  | ⊥ => by
      change
          (match sign0 (0 : α) with
          | .neg => (⊤ : WithBotTop α)
          | .zero => 0
          | .pos => ⊥) = 0
      rw [WithBotTop.sign0_zero (α := α)]
  | ⊤ => by
      change
          (match sign0 (0 : α) with
          | .neg => (⊥ : WithBotTop α)
          | .zero => 0
          | .pos => ⊤) = 0
      rw [WithBotTop.sign0_zero (α := α)]
  | (a : α) => by
      change ((0 * a : α) : WithBotTop α) = ((0 : α) : WithBotTop α)
      rw [MulZeroClass.zero_mul]

instance instMulZeroClass : MulZeroClass (WithBotTop α) where
  mul := WithBotTop.mul
  zero := 0
  zero_mul := zero_mul
  mul_zero := mul_zero

end MulZeroClass

section OrderedMulZeroOneClass

variable {α : Type u} [LinearOrderedCommGroupWithZero α]

theorem one_mul : ∀ x : WithBotTop α, (1 : WithBotTop α) * x = x
  | ⊥ => WithBotTop.coe_mul_bot_of_pos zero_lt_one
  | ⊤ => WithBotTop.coe_mul_top_of_pos zero_lt_one
  | (a : α) => by
      change ((((1 : α) * a : α) : α) : WithBotTop α) = (a : WithBotTop α)
      rw [_root_.one_mul]

theorem mul_one : ∀ x : WithBotTop α, x * (1 : WithBotTop α) = x
  | ⊥ => WithBotTop.bot_mul_coe_of_pos zero_lt_one
  | ⊤ => WithBotTop.top_mul_coe_of_pos zero_lt_one
  | (a : α) => by
      change (((a * (1 : α) : α) : α) : WithBotTop α) = (a : WithBotTop α)
      rw [_root_.mul_one]

instance instMulZeroOneClass : MulZeroOneClass (WithBotTop α) where
  mul := WithBotTop.mul
  zero := 0
  one := 1
  zero_mul := zero_mul
  mul_zero := mul_zero
  one_mul := one_mul
  mul_one := mul_one

end OrderedMulZeroOneClass

section OrderedCommMonoidWithZero

variable {α : Type u} [LinearOrderedCommGroupWithZero α]

theorem mul_comm (x y : WithBotTop α) : x * y = y * x := by
  cases x using WithBotTop.rec with
  | bot =>
      cases y using WithBotTop.rec with
      | bot => rfl
      | top => rfl
      | coe a =>
          rcases lt_trichotomy a 0 with hneg | rfl | hpos
          · rw [WithBotTop.bot_mul_coe_of_neg hneg, WithBotTop.coe_mul_bot_of_neg hneg]
          · rw [WithBotTop.bot_mul_coe_of_zero (α := α), WithBotTop.coe_mul_bot_of_zero (α := α)]
          · rw [WithBotTop.bot_mul_coe_of_pos hpos, WithBotTop.coe_mul_bot_of_pos hpos]
  | top =>
      cases y using WithBotTop.rec with
      | bot => rfl
      | top => rfl
      | coe a =>
          rcases lt_trichotomy a 0 with hneg | rfl | hpos
          · rw [WithBotTop.top_mul_coe_of_neg hneg, WithBotTop.coe_mul_top_of_neg hneg]
          · rw [WithBotTop.top_mul_coe_of_zero (α := α), WithBotTop.coe_mul_top_of_zero (α := α)]
          · rw [WithBotTop.top_mul_coe_of_pos hpos, WithBotTop.coe_mul_top_of_pos hpos]
  | coe a =>
      cases y using WithBotTop.rec with
      | bot =>
          rcases lt_trichotomy a 0 with hneg | rfl | hpos
          · rw [WithBotTop.coe_mul_bot_of_neg hneg, WithBotTop.bot_mul_coe_of_neg hneg]
          · rw [WithBotTop.coe_mul_bot_of_zero (α := α), WithBotTop.bot_mul_coe_of_zero (α := α)]
          · rw [WithBotTop.coe_mul_bot_of_pos hpos, WithBotTop.bot_mul_coe_of_pos hpos]
      | top =>
          rcases lt_trichotomy a 0 with hneg | rfl | hpos
          · rw [WithBotTop.coe_mul_top_of_neg hneg, WithBotTop.top_mul_coe_of_neg hneg]
          · rw [WithBotTop.coe_mul_top_of_zero (α := α), WithBotTop.top_mul_coe_of_zero (α := α)]
          · rw [WithBotTop.coe_mul_top_of_pos hpos, WithBotTop.top_mul_coe_of_pos hpos]
      | coe b =>
          rw [← WithBotTop.coe_mul, ← WithBotTop.coe_mul, _root_.mul_comm]

instance instNoZeroDivisors : NoZeroDivisors (WithBotTop α) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    contrapose! h
    cases a using WithBotTop.rec with
    | bot =>
        cases b using WithBotTop.rec with
        | bot =>
            exact WithBotTop.top_ne_zero (α := α)
        | coe b =>
            have hb0 : b ≠ 0 := by
              intro hb0
              exact h.2 (congrArg (fun t : α => (t : WithBotTop α)) hb0)
            rcases lt_or_gt_of_ne hb0 with hb | hb
            · rw [WithBotTop.bot_mul_coe_of_neg hb]
              exact WithBotTop.top_ne_zero (α := α)
            · rw [WithBotTop.bot_mul_coe_of_pos hb]
              exact WithBotTop.bot_ne_zero (α := α)
        | top =>
            exact WithBotTop.bot_ne_zero (α := α)
    | coe a =>
        cases b using WithBotTop.rec with
        | bot =>
            have ha0 : a ≠ 0 := by
              intro ha0
              exact h.1 (congrArg (fun t : α => (t : WithBotTop α)) ha0)
            rcases lt_or_gt_of_ne ha0 with ha | ha
            · rw [WithBotTop.coe_mul_bot_of_neg ha]
              exact WithBotTop.top_ne_zero (α := α)
            · rw [WithBotTop.coe_mul_bot_of_pos ha]
              exact WithBotTop.bot_ne_zero (α := α)
        | coe b =>
            change (((a * b : α) : WithBotTop α) ≠ (0 : WithBotTop α))
            have ha0 : a ≠ 0 := by
              intro ha0
              exact h.1 (congrArg (fun t : α => (t : WithBotTop α)) ha0)
            have hb0 : b ≠ 0 := by
              intro hb0
              exact h.2 (congrArg (fun t : α => (t : WithBotTop α)) hb0)
            intro hab
            have hab' : a * b = (0 : α) := WithBotTop.coe_injective hab
            exact (mul_ne_zero ha0 hb0) hab'
        | top =>
            have ha0 : a ≠ 0 := by
              intro ha0
              exact h.1 (congrArg (fun t : α => (t : WithBotTop α)) ha0)
            rcases lt_or_gt_of_ne ha0 with ha | ha
            · rw [WithBotTop.coe_mul_top_of_neg ha]
              exact WithBotTop.bot_ne_zero (α := α)
            · rw [WithBotTop.coe_mul_top_of_pos ha]
              exact WithBotTop.top_ne_zero (α := α)
    | top =>
        cases b using WithBotTop.rec with
        | bot =>
            exact WithBotTop.bot_ne_zero (α := α)
        | coe b =>
            have hb0 : b ≠ 0 := by
              intro hb0
              exact h.2 (congrArg (fun t : α => (t : WithBotTop α)) hb0)
            rcases lt_or_gt_of_ne hb0 with hb | hb
            · rw [WithBotTop.top_mul_coe_of_neg hb]
              exact WithBotTop.bot_ne_zero (α := α)
            · rw [WithBotTop.top_mul_coe_of_pos hb]
              exact WithBotTop.top_ne_zero (α := α)
        | top =>
            exact WithBotTop.top_ne_zero (α := α)

end OrderedCommMonoidWithZero

section OrderedMulZeroClass

variable {α : Type u} [LinearOrderedCommGroupWithZero α]

theorem mul_nonneg {a b : WithBotTop α} (ha : (0 : WithBotTop α) ≤ a)
    (hb : (0 : WithBotTop α) ≤ b) : (0 : WithBotTop α) ≤ a * b := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simp
  exact le_of_lt (WithBotTop.mul_pos ha' hb')

lemma mul_le_mul_of_nonpos_right {a b c : WithBotTop α} (h : b ≤ a) (hc : c ≤ (0 : WithBotTop α)) :
    a * c ≤ b * c := by
  sorry

lemma mul_pos_iff {a b : WithBotTop α} :
    (0 : WithBotTop α) < a * b ↔
      ((0 : WithBotTop α) < a ∧ (0 : WithBotTop α) < b) ∨ (a < 0 ∧ b < 0) := by
  sorry

lemma mul_nonneg_iff {a b : WithBotTop α} :
    (0 : WithBotTop α) ≤ a * b ↔
      ((0 : WithBotTop α) ≤ a ∧ (0 : WithBotTop α) ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) := by
  sorry

lemma mul_neg_iff {a b : WithBotTop α} :
    a * b < (0 : WithBotTop α) ↔
      ((0 : WithBotTop α) < a ∧ b < 0) ∨ (a < 0 ∧ (0 : WithBotTop α) < b) := by
  sorry

lemma mul_nonpos_iff {a b : WithBotTop α} :
    a * b ≤ (0 : WithBotTop α) ↔
      ((0 : WithBotTop α) ≤ a ∧ b ≤ 0) ∨ (a ≤ 0 ∧ (0 : WithBotTop α) ≤ b) := by
  sorry

lemma mul_nonpos_of_nonneg_of_nonpos {a b : WithBotTop α} (ha : (0 : WithBotTop α) ≤ a)
    (hb : b ≤ 0) : a * b ≤ (0 : WithBotTop α) := by
  sorry

lemma mul_nonpos_of_nonpos_of_nonneg {a b : WithBotTop α} (ha : a ≤ 0)
    (hb : (0 : WithBotTop α) ≤ b) : a * b ≤ (0 : WithBotTop α) := by
  sorry

lemma mul_nonneg_of_nonpos_of_nonpos {a b : WithBotTop α} (ha : a ≤ 0)
    (hb : b ≤ 0) : (0 : WithBotTop α) ≤ a * b := by
  sorry

lemma mul_eq_top (a b : WithBotTop α) :
    a * b = ⊤ ↔
      (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ ((0 : WithBotTop α) < a ∧ b = ⊤) := by
  induction a, b using WithBotTop.induction₂_symm with
  | symm h => grind [WithBotTop.mul_comm]
  | top_top => simp [WithBotTop.zero_lt_top]
  | top_pos _ hx => simp [WithBotTop.top_mul_coe_of_pos hx, hx]
  | top_zero => simp [WithBotTop.zero_ne_top]
  | top_neg _ hx =>
      rw [WithBotTop.top_mul_coe_of_neg hx]
      constructor
      · intro h
        exact (bot_ne_top h).elim
      · rintro (h | h | h | h)
        · exact (top_ne_bot h.1).elim
        · exact (not_top_lt h.1).elim
        · have hxpos := (WithBotTop.coe_pos).1 h.2
          exact (hx.not_ge hxpos.le).elim
        · exact (WithBotTop.coe_ne_top _ h.2).elim
  | top_bot => simp
  | pos_bot _ hx => simp [hx, WithBotTop.coe_mul_bot_of_pos hx]
  | coe_coe x y => simp [WithBotTop.coe_pos, WithBotTop.coe_neg', ← coe_mul]
  | zero_bot => simp [WithBotTop.zero_ne_top]
  | neg_bot _ hx =>
      rw [WithBotTop.coe_mul_bot_of_neg hx]
      simp [hx, WithBotTop.coe_pos, WithBotTop.coe_neg']
  | bot_bot => simp

lemma mul_ne_top (a b : WithBotTop α) :
    a * b ≠ ⊤ ↔
      (a ≠ ⊥ ∨ (0 : WithBotTop α) ≤ b) ∧
        ((0 : WithBotTop α) ≤ a ∨ b ≠ ⊥) ∧
          (a ≠ ⊤ ∨ b ≤ 0) ∧
            (a ≤ 0 ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_top]
  push +distrib Not
  rfl

lemma mul_eq_bot (a b : WithBotTop α) :
    a * b = ⊥ ↔
      (a = ⊥ ∧ (0 : WithBotTop α) < b) ∨ ((0 : WithBotTop α) < a ∧ b = ⊥) ∨
        (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤) := by
  induction a, b using WithBotTop.induction₂_symm with
  | symm h => grind [WithBotTop.mul_comm]
  | top_top => simp [WithBotTop.zero_lt_top]
  | top_pos _ hx => simp [WithBotTop.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx =>
      simp [hx, WithBotTop.coe_pos, WithBotTop.coe_neg', WithBotTop.top_mul_coe_of_neg hx,
        WithBotTop.zero_lt_top]
  | top_bot => simp [WithBotTop.zero_lt_top]
  | pos_bot _ hx => simp [hx, WithBotTop.coe_mul_bot_of_pos hx]
  | coe_coe x y => simp [WithBotTop.coe_pos, WithBotTop.coe_neg', ← coe_mul]
  | zero_bot => simp
  | neg_bot _ hx =>
      rw [WithBotTop.coe_mul_bot_of_neg hx]
      constructor
      · intro h
        exact (top_ne_bot h).elim
      · rintro (h | h | h | h)
        · exact (WithBotTop.coe_ne_bot _ h.1).elim
        · have hxpos := (WithBotTop.coe_pos).1 h.1
          exact (hx.not_ge hxpos.le).elim
        · exact (WithBotTop.coe_ne_top _ h.1).elim
        · exact h.2.symm
  | bot_bot => simp

lemma mul_ne_bot (a b : WithBotTop α) :
    a * b ≠ ⊥ ↔
      (a ≠ ⊥ ∨ b ≤ 0) ∧
        (a ≤ 0 ∨ b ≠ ⊥) ∧
          (a ≠ ⊤ ∨ (0 : WithBotTop α) ≤ b) ∧
            ((0 : WithBotTop α) ≤ a ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_bot]
  push +distrib Not
  rfl

end OrderedMulZeroClass

section LinearOrderedField

variable {α : Type u} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

lemma le_mul_of_forall_lt {a b c : WithBotTop α} (h₁ : (0 : WithBotTop α) < a ∨ b ≠ ⊤)
    (h₂ : a ≠ ⊤ ∨ (0 : WithBotTop α) < b) (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') :
    c ≤ a * b := by
  sorry

lemma mul_le_of_forall_lt_of_nonneg {a b c : WithBotTop α} (ha : (0 : WithBotTop α) ≤ a)
    (hc : (0 : WithBotTop α) ≤ c)
    (h : ∀ a' ∈ Set.Ioo (0 : WithBotTop α) a, ∀ b' ∈ Set.Ioo (0 : WithBotTop α) b, a' * b' ≤ c) :
    a * b ≤ c := by
  sorry

end LinearOrderedField

end WithBotTop
