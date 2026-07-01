import Mathlib.Algebra.Order.WithBotTop.Inv
import Mathlib.Algebra.Order.WithBotTop.Add
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Order.Hom.Basic

/-!
Canonical negation and subtraction on `WithBotTop α`.

This file is the `neg/sub` owner layer in the generic `WithBotTop` hierarchy.

- The canonical additive surface lives in `EOrder.Basic` and `EOrder.Add`.
- The canonical multiplicative surface now lives in `EOrder.Mul`.
- The canonical inversion and division surface lives in `EOrder.Inv`, already phrased in terms of
  the new ordinary `*` on `WithBotTop α`.
- This file therefore contains only the operations that are genuinely new here:
  `Neg`, `Sub`, and the order-facing lemmas built from them.

In particular, there is no separate signed-multiplication API left in this layer: every downstream
statement here is meant to work over the new canonical `*`.
-/

universe u

namespace WithBotTop

section Neg

variable {α : Type u} [Neg α]

/-- Canonical negation on `WithBotTop α`: the boundary points are swapped, and coercions use the
negation on `α`. -/
protected def neg : WithBotTop α → WithBotTop α
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (a : α) => (-a : α)

instance instNeg : Neg (WithBotTop α) := ⟨WithBotTop.neg⟩

@[simp] theorem neg_top : -(⊤ : WithBotTop α) = ⊥ :=
  rfl

@[simp] theorem neg_bot : -(⊥ : WithBotTop α) = ⊤ :=
  rfl

@[simp] theorem coe_neg (a : α) : ((-a : α) : WithBotTop α) = -(a : WithBotTop α) :=
  rfl

end Neg

section NegZeroClass

variable {α : Type u} [NegZeroClass α]

@[simp] theorem neg_zero : (-(0 : WithBotTop α)) = 0 := by
  change (((-(0 : α) : α)) : WithBotTop α) = (0 : WithBotTop α)
  rw [_root_.neg_zero]
  rfl

end NegZeroClass

section InvolutiveNeg

variable {α : Type u} [InvolutiveNeg α]

instance instInvolutiveNeg : InvolutiveNeg (WithBotTop α) where
  neg_neg x := by
    cases x using WithBotTop.rec with
    | bot => rfl
    | top => rfl
    | coe a =>
        change (((-(-a) : α) : α) : WithBotTop α) = (a : WithBotTop α)
        rw [neg_neg]

@[simp] theorem neg_eq_top_iff {x : WithBotTop α} : -x = (⊤ : WithBotTop α) ↔ x = ⊥ := by
  cases x using WithBotTop.rec with
  | bot => simp
  | top =>
      constructor
      · intro h
        exact False.elim (top_ne_bot h.symm)
      · intro h
        cases h
  | coe a =>
      constructor
      · intro h
        change (((-a : α) : WithBotTop α) = ⊤) at h
        exact False.elim <| WithBotTop.top_ne_coe h.symm
      · intro h
        exact False.elim <| WithBotTop.coe_ne_bot h

@[simp] theorem neg_eq_bot_iff {x : WithBotTop α} : -x = (⊥ : WithBotTop α) ↔ x = ⊤ := by
  cases x using WithBotTop.rec with
  | bot =>
      constructor
      · intro h
        exact False.elim (top_ne_bot h)
      · intro h
        cases h
  | top => simp
  | coe a =>
      constructor
      · intro h
        change (((-a : α) : WithBotTop α) = ⊥) at h
        exact False.elim <| WithBotTop.bot_ne_coe h.symm
      · intro h
        exact False.elim <| WithBotTop.coe_ne_top h

end InvolutiveNeg

section InvNeg

variable {α : Type u} [DivisionRing α]

theorem inv_neg (a : WithBotTop α) : (WithBotTop.neg a)⁻¹ = WithBotTop.neg (a⁻¹) := by
  cases a using WithBotTop.rec with
  | bot =>
      change (0 : WithBotTop α) = WithBotTop.neg 0
      exact WithBotTop.neg_zero.symm
  | top =>
      change (0 : WithBotTop α) = WithBotTop.neg 0
      exact WithBotTop.neg_zero.symm
  | coe a =>
      change ((((-a)⁻¹ : α) : α) : WithBotTop α) = (((-(a⁻¹) : α) : α) : WithBotTop α)
      exact congrArg (fun t : α => (t : WithBotTop α)) (by simp)

end InvNeg

section AddGroup

variable {α : Type u} [AddGroup α]

@[simp] theorem neg_eq_zero_iff {x : WithBotTop α} : -x = (0 : WithBotTop α) ↔ x = 0 := by
  cases x using WithBotTop.rec with
  | bot =>
      constructor
      · intro h
        exact False.elim (WithBotTop.top_ne_zero h)
      · intro h
        exact False.elim (WithBotTop.bot_ne_zero h)
  | top =>
      constructor
      · intro h
        exact False.elim (WithBotTop.bot_ne_zero h)
      · intro h
        exact False.elim (WithBotTop.top_ne_zero h)
  | coe a =>
      constructor
      · intro h
        have h' : ((-a : α) : WithBotTop α) = ((0 : α) : WithBotTop α) := by
          simpa [coe_neg] using h
        have : a = 0 := _root_.neg_eq_zero.mp (WithBotTop.coe_inj.mp h')
        exact WithBotTop.coe_inj.mpr this
      · intro h
        change ((a : α) : WithBotTop α) = ((0 : α) : WithBotTop α) at h
        have ha : a = 0 := WithBotTop.coe_inj.mp h
        have : (-a : α) = 0 := _root_.neg_eq_zero.mpr ha
        exact WithBotTop.coe_inj.mpr this

end AddGroup

section OrderedNeg

variable {α : Type u} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

@[simp] theorem neg_le_neg_iff {a b : WithBotTop α} : -a ≤ -b ↔ b ≤ a := by
  cases a using WithBotTop.rec with
  | bot =>
      cases b using WithBotTop.rec with
      | bot => simp
      | top => simp
      | coe b => simp
  | top =>
      cases b using WithBotTop.rec with
      | bot => simp
      | top => simp
      | coe b => simp
  | coe a =>
      cases b using WithBotTop.rec with
      | bot => simp
      | top => simp
      | coe b =>
          rw [← WithBotTop.coe_neg, ← WithBotTop.coe_neg]
          rw [WithBotTop.coe_le_coe, WithBotTop.coe_le_coe]
          exact (_root_.neg_le_neg_iff : (-a : α) ≤ -b ↔ b ≤ a)

@[simp] theorem neg_lt_neg_iff {a b : WithBotTop α} : -a < -b ↔ b < a := by
  cases a using WithBotTop.rec with
  | bot =>
      cases b using WithBotTop.rec with
      | bot => simp
      | top => simp
      | coe b => simp
  | coe a =>
      cases b using WithBotTop.rec with
      | bot =>
          constructor
          · intro _
            change (⊥ : WithBot (WithTop α)) < (((a : α) : WithTop α) : WithBot (WithTop α))
            exact WithBot.bot_lt_coe ((a : α) : WithTop α)
          · intro _
            change
              ((((-a : α) : WithTop α) : WithBot (WithTop α)) <
                ((⊤ : WithTop α) : WithBot (WithTop α)))
            exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top (-a))
      | top => simp
      | coe b =>
          rw [← WithBotTop.coe_neg, ← WithBotTop.coe_neg]
          rw [WithBotTop.coe_lt_coe, WithBotTop.coe_lt_coe]
          exact (_root_.neg_lt_neg_iff : (-a : α) < -b ↔ b < a)
  | top =>
      cases b using WithBotTop.rec with
      | bot => simp
      | top => simp
      | coe a =>
          constructor
          · intro _
            change
              (((a : α) : WithTop α) : WithBot (WithTop α)) <
                ((⊤ : WithTop α) : WithBot (WithTop α))
            exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top a)
          · intro _
            change (⊥ : WithBot (WithTop α)) < ((((-a : α) : WithTop α) : WithBot (WithTop α)))
            exact WithBot.bot_lt_coe ((-a : α) : WithTop α)

/-- `-a ≤ b` if and only if `-b ≤ a` on `WithBotTop α`. -/
protected theorem neg_le {a b : WithBotTop α} : -a ≤ b ↔ -b ≤ a := by
  rw [← neg_le_neg_iff, neg_neg]

/-- If `-a ≤ b` then `-b ≤ a` on `WithBotTop α`. -/
protected theorem neg_le_of_neg_le {a b : WithBotTop α} (h : -a ≤ b) : -b ≤ a :=
  WithBotTop.neg_le.mp h

/-- `a ≤ -b` if and only if `b ≤ -a` on `WithBotTop α`. -/
protected theorem le_neg {a b : WithBotTop α} : a ≤ -b ↔ b ≤ -a := by
  rw [← neg_le_neg_iff, neg_neg]

/-- If `a ≤ -b` then `b ≤ -a` on `WithBotTop α`. -/
protected theorem le_neg_of_le_neg {a b : WithBotTop α} (h : a ≤ -b) : b ≤ -a :=
  WithBotTop.le_neg.mp h

/-- `-a < b` if and only if `-b < a` on `WithBotTop α`. -/
theorem neg_lt_comm {a b : WithBotTop α} : -a < b ↔ -b < a := by
  rw [← neg_lt_neg_iff, neg_neg]

/-- If `-a < b` then `-b < a` on `WithBotTop α`. -/
protected theorem neg_lt_of_neg_lt {a b : WithBotTop α} (h : -a < b) : -b < a :=
  neg_lt_comm.mp h

/-- `a < -b` if and only if `b < -a` on `WithBotTop α`. -/
theorem lt_neg_comm {a b : WithBotTop α} : a < -b ↔ b < -a := by
  rw [← neg_lt_neg_iff, neg_neg]

/-- If `a < -b` then `b < -a` on `WithBotTop α`. -/
protected theorem lt_neg_of_lt_neg {a b : WithBotTop α} (h : a < -b) : b < -a :=
  lt_neg_comm.mp h

theorem neg_strictAnti : StrictAnti (- · : WithBotTop α → WithBotTop α) := by
  intro a b hab
  exact (neg_lt_neg_iff).2 hab

lemma min_neg_neg (x y : WithBotTop α) : min (-x) (-y) = -max x y := by
  simpa using (WithBotTop.neg_strictAnti.antitone.map_max (a := x) (b := y)).symm

lemma max_neg_neg (x y : WithBotTop α) : max (-x) (-y) = -min x y := by
  simpa using (WithBotTop.neg_strictAnti.antitone.map_min (a := x) (b := y)).symm

def negOrderIso : WithBotTop α ≃o (WithBotTop α)ᵒᵈ where
  toFun := fun x => OrderDual.toDual (-x)
  invFun := fun x => -OrderDual.ofDual x
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  map_rel_iff' := by
    intro a b
    exact neg_le_neg_iff

@[simp] theorem neg_le_zero {a : WithBotTop α} :
    -a ≤ (0 : WithBotTop α) ↔ (0 : WithBotTop α) ≤ a := by
  rw [WithBotTop.neg_le, WithBotTop.neg_zero]

@[simp] theorem neg_nonneg {a : WithBotTop α} : (0 : WithBotTop α) ≤ -a ↔ a ≤ 0 := by
  rw [WithBotTop.le_neg, WithBotTop.neg_zero]

@[simp] theorem neg_lt_zero {a : WithBotTop α} :
    -a < (0 : WithBotTop α) ↔ (0 : WithBotTop α) < a := by
  rw [neg_lt_comm, WithBotTop.neg_zero]

@[simp] theorem neg_pos {a : WithBotTop α} : (0 : WithBotTop α) < -a ↔ a < 0 := by
  rw [lt_neg_comm, WithBotTop.neg_zero]

/-- Induct on two `WithBotTop α`s by performing case splits on the sign of one whenever the other
is infinite. This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for
all `x`, `y`. -/
@[elab_as_elim]
lemma induction₂_neg_left {P : WithBotTop α → WithBotTop α → Prop}
    (neg_left : ∀ {x y}, P x y → P (-x) y)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : α, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : α, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (zero_top : P 0 ⊤) (zero_bot : P 0 ⊥)
    (pos_top : ∀ x : α, 0 < x → P x ⊤) (pos_bot : ∀ x : α, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : α, P x y) : ∀ x y, P x y :=
  have hneg : ∀ y, (∀ x : α, 0 < x → P x y) → ∀ x : α, x < 0 → P x y := fun _ h x hx => by
    simpa [WithBotTop.coe_neg] using neg_left (h (-x) ((_root_.neg_pos).2 hx))
  @WithBotTop.induction₂ α _ _ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (hneg _ pos_top) (hneg _ pos_bot) (neg_left top_top)
    (fun x hx => neg_left <| top_pos x hx) (neg_left top_zero)
    (fun x hx => neg_left <| top_neg x hx) (neg_left top_bot)

/-- Induct on two `WithBotTop α`s by performing case splits on the sign of one whenever the other
is infinite. This version eliminates some cases by assuming that `P` is symmetric and `P x y`
implies `P (-x) y` for all `x`, `y`. -/
@[elab_as_elim]
lemma induction₂_symm_neg {P : WithBotTop α → WithBotTop α → Prop}
    (symm : ∀ {x y}, P x y → P y x)
    (neg_left : ∀ {x y}, P x y → P (-x) y) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : α, 0 < x → P ⊤ x) (top_zero : P ⊤ 0) (coe_coe : ∀ x y : α, P x y) :
    ∀ x y, P x y :=
  have neg_right : ∀ {x y}, P x y → P x (-y) := fun h => symm <| neg_left <| symm h
  have hneg : ∀ x, (∀ y : α, 0 < y → P x y) → ∀ y : α, y < 0 → P x y := fun _ h y hy => by
    simpa [WithBotTop.coe_neg] using neg_right (h (-y) ((_root_.neg_pos).2 hy))
  @WithBotTop.induction₂_neg_left α _ _ _ P neg_left top_top top_pos top_zero (hneg _ top_pos)
    (neg_right top_top) (symm top_zero) (symm <| neg_left top_zero)
    (fun x hx => symm <| top_pos x hx) (fun x hx => symm <| neg_left <| top_pos x hx) coe_coe

end OrderedNeg

section OrderedMul

variable {α : Type u} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

protected theorem neg_mul (x y : WithBotTop α) : -x * y = -(x * y) := by
  induction x, y using induction₂_neg_left with
  | top_zero => simp
  | zero_top => simp
  | zero_bot => simp
  | top_top | top_bot =>
      rfl
  | neg_left h =>
      rename_i x y
      change ((-(-x)) * y) = -((-x) * y)
      calc
        ((-(-x)) * y) = x * y := by simp
        _ = -(-(x * y)) := by
          symm
          exact neg_neg (x * y)
        _ = -((-x) * y) := by
          rw [h]
  | coe_coe x y =>
      change (((-x : α) * y : α) : WithBotTop α) = ((-(x * y) : α) : WithBotTop α)
      exact congrArg (fun t : α => (t : WithBotTop α)) (_root_.neg_mul x y)
  | top_pos x h =>
      rw [WithBotTop.top_mul_coe_of_pos h, WithBotTop.neg_top]
      simpa using (WithBotTop.bot_mul_coe_of_pos h)
  | pos_top x h =>
      rw [← WithBotTop.coe_neg, WithBotTop.coe_mul_top_of_pos h, WithBotTop.neg_top]
      simpa using (WithBotTop.coe_mul_top_of_neg (a := -x) (neg_neg_of_pos h))
  | top_neg x h =>
      rw [WithBotTop.top_mul_coe_of_neg h, WithBotTop.neg_bot]
      simpa using (WithBotTop.bot_mul_coe_of_neg h)
  | pos_bot x h =>
      rw [← WithBotTop.coe_neg, WithBotTop.coe_mul_bot_of_pos h, WithBotTop.neg_bot]
      simpa using (WithBotTop.coe_mul_bot_of_neg (a := -x) (neg_neg_of_pos h))

theorem mul_neg (x y : WithBotTop α) : x * -y = -(x * y) := by
  have hcomm : ∀ a b : WithBotTop α, a * b = b * a := by
    intro a b
    cases a using WithBotTop.rec with
    | bot =>
        cases b using WithBotTop.rec with
        | bot => rfl
        | top => rfl
        | coe a =>
            rcases lt_trichotomy a 0 with hneg | rfl | hpos
            · rw [WithBotTop.bot_mul_coe_of_neg hneg, WithBotTop.coe_mul_bot_of_neg hneg]
            · rw [WithBotTop.bot_mul_coe_of_zero (α := α), WithBotTop.coe_mul_bot_of_zero (α := α)]
            · rw [WithBotTop.bot_mul_coe_of_pos hpos, WithBotTop.coe_mul_bot_of_pos hpos]
    | top =>
        cases b using WithBotTop.rec with
        | bot => rfl
        | top => rfl
        | coe a =>
            rcases lt_trichotomy a 0 with hneg | rfl | hpos
            · rw [WithBotTop.top_mul_coe_of_neg hneg, WithBotTop.coe_mul_top_of_neg hneg]
            · rw [WithBotTop.top_mul_coe_of_zero (α := α), WithBotTop.coe_mul_top_of_zero (α := α)]
            · rw [WithBotTop.top_mul_coe_of_pos hpos, WithBotTop.coe_mul_top_of_pos hpos]
    | coe a =>
        cases b using WithBotTop.rec with
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
            exact congrArg (fun t : α => (t : WithBotTop α)) (_root_.mul_comm a b)
  calc
    x * -y = -y * x := hcomm _ _
    _ = -(y * x) := WithBotTop.neg_mul y x
    _ = -(x * y) := by rw [hcomm _ _]

end OrderedMul

section Sub

variable {α : Type u} [Add α] [Neg α]

/-- Canonical subtraction on `WithBotTop α`, defined by `x - y = x + (-y)`. -/
protected def sub (x y : WithBotTop α) : WithBotTop α :=
  x + (-y)

instance instSub : Sub (WithBotTop α) := ⟨WithBotTop.sub⟩

@[simp] theorem sub_eq_add_neg (x y : WithBotTop α) : x - y = x + (-y) :=
  rfl

@[simp] theorem bot_sub (x : WithBotTop α) : (⊥ : WithBotTop α) - x = ⊥ := by
  simp

@[simp] theorem sub_top (x : WithBotTop α) : x - (⊤ : WithBotTop α) = ⊥ := by
  simp

@[simp] theorem top_sub_bot : (⊤ : WithBotTop α) - (⊥ : WithBotTop α) = ⊤ := by
  simp

@[simp] theorem top_sub_coe (a : α) : (⊤ : WithBotTop α) - a = ⊤ := by
  change (⊤ : WithBotTop α) + ((-a : α) : WithBotTop α) = ⊤
  simpa using (WithBotTop.top_add_coe (-a))

@[simp] theorem coe_sub_bot (a : α) : (a : WithBotTop α) - (⊥ : WithBotTop α) = ⊤ := by
  simp

theorem sub_bot {x : WithBotTop α} (hx : x ≠ ⊥) : x - (⊥ : WithBotTop α) = ⊤ := by
  simpa [WithBotTop.sub] using (WithBotTop.add_top_of_ne_bot (x := x) hx)

theorem top_sub {x : WithBotTop α} (hx : x ≠ ⊤) : (⊤ : WithBotTop α) - x = ⊤ := by
  cases x using WithBotTop.rec with
  | bot => simp
  | top => contradiction
  | coe a =>
      change (⊤ : WithBotTop α) + ((-a : α) : WithBotTop α) = ⊤
      simpa using (WithBotTop.top_add_coe (-a))

end Sub

section SubAddGroup

variable {α : Type u} [AddGroup α]

theorem sub_self {x : WithBotTop α} (hx_top : x ≠ ⊤) (hx_bot : x ≠ ⊥) : x - x = 0 := by
  cases x using WithBotTop.rec with
  | bot => contradiction
  | top => contradiction
  | coe a =>
      change ((a : WithBotTop α) + (((-a : α) : α) : WithBotTop α)) = (0 : WithBotTop α)
      rw [← WithBotTop.coe_add]
      have hs : a + -a = (0 : α) := by
        simp
      exact congrArg (fun t : α => (t : WithBotTop α)) hs

end SubAddGroup

section NegAddGroup

variable {α : Type u} [AddCommGroup α]

lemma neg_add {x y : WithBotTop α} (h1 : x ≠ ⊥ ∨ y ≠ ⊤) (h2 : x ≠ ⊤ ∨ y ≠ ⊥) :
    -(x + y) = -x - y := by
  cases x using WithBotTop.rec with
  | bot =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe a => simp
      | top =>
          exfalso
          simp at h1
  | coe a =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe b =>
          change (((-(a + b) : α) : α) : WithBotTop α) = (((-a + -b : α) : α) : WithBotTop α)
          congr 1
          calc
            (-(a + b) : α) = -b + -a := _root_.neg_add_rev a b
            _ = -a + -b := by rw [add_comm]
      | top => simp
  | top =>
      cases y using WithBotTop.rec with
      | bot =>
          exfalso
          simp at h2
      | coe a => simp
      | top => simp

lemma neg_sub {x y : WithBotTop α} (h1 : x ≠ ⊥ ∨ y ≠ ⊥) (h2 : x ≠ ⊤ ∨ y ≠ ⊤) :
    -(x - y) = -x + y := by
  cases x using WithBotTop.rec with
  | bot =>
      cases y using WithBotTop.rec with
      | bot =>
          exfalso
          simp at h1
      | coe a => simp
      | top => simp
  | coe a =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe b =>
          change (((-(a + -b) : α) : α) : WithBotTop α) = (((-a + b : α) : α) : WithBotTop α)
          congr 1
          calc
            (-(a + -b) : α) = -(-b) + -a := _root_.neg_add_rev a (-b)
            _ = b + -a := by rw [neg_neg]
            _ = -a + b := by rw [add_comm]
      | top => simp
  | top =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe a => simp
      | top =>
          exfalso
          simp at h2

end NegAddGroup

section OrderedSubSelf

variable {α : Type u} [AddGroup α] [LinearOrder α]

theorem sub_self_le_zero {x : WithBotTop α} : x - x ≤ (0 : WithBotTop α) := by
  cases x using WithBotTop.rec with
  | bot => simp [sub_eq_add_neg, neg_bot]
  | top => simp [sub_eq_add_neg, neg_top]
  | coe a =>
      rw [sub_self (x := (a : WithBotTop α)) (WithBotTop.coe_ne_top) (WithBotTop.coe_ne_bot)]

end OrderedSubSelf

section OrderedSub

variable {α : Type u} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem sub_nonneg {x y : WithBotTop α} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
    (0 : WithBotTop α) ≤ x - y ↔ y ≤ x := by
  cases x using WithBotTop.rec with
  | bot =>
      cases y using WithBotTop.rec with
      | bot =>
          exfalso
          have : False := by simp at h_bot
          exact this
      | coe a => simp
      | top => simp
  | coe a =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe b =>
          change
            (((0 : α) : WithBotTop α) ≤ (((a + -b : α) : α) : WithBotTop α)) ↔
              ((b : α) : WithBotTop α) ≤ (a : WithBotTop α)
          rw [WithBotTop.coe_le_coe, WithBotTop.coe_le_coe]
          rw [← _root_.sub_eq_add_neg]
          exact (_root_.sub_nonneg : (0 : α) ≤ a - b ↔ b ≤ a)
      | top => simp
  | top =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe a => simp
      | top =>
          exfalso
          have : False := by simp at h_top
          exact this

theorem sub_nonpos {x y : WithBotTop α} :
    x - y ≤ (0 : WithBotTop α) ↔ x ≤ y := by
  cases x using WithBotTop.rec with
  | bot =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe a => simp
      | top => simp
  | coe a =>
      cases y using WithBotTop.rec with
      | bot =>
          constructor
          · intro h
            exact False.elim ((not_le_of_gt WithBotTop.zero_lt_top) h)
          · intro h
            exact False.elim ((not_le_of_gt (WithBotTop.bot_lt_coe (a := a))) h)
      | coe b =>
          change
            ((((a + -b : α) : α) : WithBotTop α) ≤ ((0 : α) : WithBotTop α)) ↔
              (a : WithBotTop α) ≤ (b : WithBotTop α)
          rw [WithBotTop.coe_le_coe, WithBotTop.coe_le_coe]
          rw [← _root_.sub_eq_add_neg]
          exact (_root_.sub_nonpos : a - b ≤ (0 : α) ↔ a ≤ b)
      | top => simp
  | top =>
      cases y using WithBotTop.rec with
      | bot =>
          constructor
          · intro h
            exact False.elim ((not_le_of_gt WithBotTop.zero_lt_top) h)
          · intro h
            exact False.elim <|
              (not_le_of_gt (lt_trans WithBotTop.bot_lt_zero WithBotTop.zero_lt_top)) h
      | coe a =>
          constructor
          · intro h
            exact False.elim ((not_le_of_gt WithBotTop.zero_lt_top) h)
          · intro h
            exact False.elim ((not_le_of_gt (WithBotTop.coe_lt_top (a := a))) h)
      | top => simp

theorem sub_pos {x y : WithBotTop α} :
    (0 : WithBotTop α) < x - y ↔ y < x := by
  cases x using WithBotTop.rec with
  | bot =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe a => simp
      | top => simp
  | coe a =>
      cases y using WithBotTop.rec with
      | bot =>
          constructor
          · intro _
            exact WithBotTop.bot_lt_coe (a := a)
          · intro _
            exact WithBotTop.zero_lt_top
      | coe b =>
          change
            (((0 : α) : WithBotTop α) < (((a + -b : α) : α) : WithBotTop α)) ↔
              (b : WithBotTop α) < (a : WithBotTop α)
          rw [WithBotTop.coe_lt_coe, WithBotTop.coe_lt_coe]
          rw [← _root_.sub_eq_add_neg]
          exact (_root_.sub_pos : (0 : α) < a - b ↔ b < a)
      | top => simp
  | top =>
      cases y using WithBotTop.rec with
      | bot =>
          constructor
          · intro _
            exact lt_trans WithBotTop.bot_lt_zero WithBotTop.zero_lt_top
          · intro _
            exact WithBotTop.zero_lt_top
      | coe a =>
          constructor
          · intro _
            exact WithBotTop.coe_lt_top (a := a)
          · intro _
            exact WithBotTop.zero_lt_top
      | top => simp

theorem sub_neg {x y : WithBotTop α} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
    x - y < (0 : WithBotTop α) ↔ x < y := by
  cases x using WithBotTop.rec with
  | bot =>
      cases y using WithBotTop.rec with
      | bot =>
          exfalso
          have : False := by simp at h_bot
          exact this
      | coe a =>
          constructor
          · intro _
            exact WithBotTop.bot_lt_coe (a := a)
          · intro _
            exact WithBotTop.bot_lt_zero
      | top => simp
  | coe a =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe b =>
          change
            ((((a + -b : α) : α) : WithBotTop α) < ((0 : α) : WithBotTop α)) ↔
              (a : WithBotTop α) < (b : WithBotTop α)
          rw [WithBotTop.coe_lt_coe, WithBotTop.coe_lt_coe]
          rw [← _root_.sub_eq_add_neg]
          exact (_root_.sub_neg : a - b < (0 : α) ↔ a < b)
      | top =>
          constructor
          · intro _
            exact WithBotTop.coe_lt_top (a := a)
          · intro _
            exact WithBotTop.bot_lt_zero
  | top =>
      cases y using WithBotTop.rec with
      | bot => simp
      | coe a => simp
      | top =>
          exfalso
          have : False := by simp at h_top
          exact this

theorem sub_le_sub {x y z t : WithBotTop α} (h : x ≤ y) (h' : t ≤ z) :
    x - z ≤ y - t := by
  simpa [sub_eq_add_neg] using add_le_add h (neg_le_neg_iff.2 h')

theorem sub_lt_sub_of_lt_of_le {x y z t : WithBotTop α} (h : x < y) (h' : z ≤ t)
    (hz : z ≠ ⊥) (ht : t ≠ ⊤) : x - t < y - z := by
  have hz_top : z ≠ ⊤ := by
    intro hz_top
    exact ht (top_le_iff.mp (hz_top ▸ h'))
  have ht_bot : t ≠ ⊥ := by
    intro ht_bot
    exact hz (le_bot_iff.mp (ht_bot ▸ h'))
  lift z to α using ⟨hz, hz_top⟩
  lift t to α using ⟨ht_bot, ht⟩
  have h'α : z ≤ t := WithBotTop.coe_le_coe.mp h'
  have hx : x + ((-t : α) : WithBotTop α) < y + ((-t : α) : WithBotTop α) := by
    cases x using WithBotTop.rec with
    | bot =>
        cases y using WithBotTop.rec with
        | bot => cases h
        | coe y =>
            simpa [WithBotTop.coe_add] using (WithBotTop.bot_lt_coe (a := y + -t))
        | top => simp
    | coe x =>
        cases y using WithBotTop.rec with
        | bot => cases h
        | coe y =>
            have hxy : x < y := WithBotTop.coe_lt_coe.mp h
            have hz : x + -t < y + -t := _root_.add_lt_add_left hxy (-t)
            simpa [WithBotTop.coe_add] using (WithBotTop.coe_lt_coe.mpr hz)
        | top =>
            simpa [WithBotTop.coe_add] using (WithBotTop.coe_lt_top (a := x + -t))
    | top =>
        exfalso
        exact (not_le_of_gt h) le_top
  have hy : y + ((-t : α) : WithBotTop α) ≤ y + ((-z : α) : WithBotTop α) := by
    refine add_le_add le_rfl ?_
    rw [WithBotTop.coe_le_coe]
    exact neg_le_neg h'α
  simpa [sub_eq_add_neg] using lt_of_lt_of_le hx hy

lemma le_sub_iff_add_le {a b c : WithBotTop α} (hb : b ≠ ⊥ ∨ c ≠ ⊥)
    (ht : b ≠ ⊤ ∨ c ≠ ⊤) : a ≤ c - b ↔ a + b ≤ c := by
  cases b using WithBotTop.rec with
  | bot =>
      simp only [ne_eq, not_true_eq_false, false_or] at hb
      simp [sub_bot hb]
  | coe b =>
      cases a using WithBotTop.rec with
      | bot =>
          cases c using WithBotTop.rec <;> simp [sub_eq_add_neg]
      | top =>
          cases c using WithBotTop.rec with
          | bot => simp [sub_eq_add_neg]
          | top => simp [sub_eq_add_neg]
          | coe c =>
              constructor
              · intro h'
                exact False.elim <| WithBotTop.coe_ne_top (top_le_iff.mp h')
              · intro h'
                exact False.elim ((not_le_of_gt (WithBotTop.coe_lt_top (a := c))) h')
      | coe a =>
          cases c using WithBotTop.rec with
          | bot => simp [sub_eq_add_neg]
          | top => simp [sub_eq_add_neg]
          | coe c =>
              change (((a : α) : WithBotTop α) ≤ (((c + -b : α) : α) : WithBotTop α)) ↔
                  (((a + b : α) : α) : WithBotTop α) ≤ (c : WithBotTop α)
              rw [WithBotTop.coe_le_coe, WithBotTop.coe_le_coe]
              simpa [← _root_.sub_eq_add_neg] using
                (_root_.le_sub_iff_add_le : a ≤ c - b ↔ a + b ≤ c)
  | top =>
      simp only [ne_eq, not_true_eq_false, false_or, sub_top, le_bot_iff] at ht ⊢
      refine ⟨fun h ↦ h ▸ (WithBotTop.bot_add (⊤ : WithBotTop α)).symm ▸ bot_le, fun h ↦ ?_⟩
      by_contra ha
      exact (h.trans_lt (Ne.lt_top ht)).ne (add_top_iff_ne_bot.2 ha)

lemma sub_le_iff_le_add {a b c : WithBotTop α} (h₁ : b ≠ ⊥ ∨ c ≠ ⊤)
    (h₂ : b ≠ ⊤ ∨ c ≠ ⊥) : a - b ≤ c ↔ a ≤ c + b := by
  suffices a + (-b) ≤ c ↔ a ≤ c - (-b) by simpa [sub_eq_add_neg]
  refine (le_sub_iff_add_le ?_ ?_).symm <;> simpa

protected theorem lt_sub_iff_add_lt {a b c : WithBotTop α} (h₁ : b ≠ ⊥ ∨ c ≠ ⊤)
    (h₂ : b ≠ ⊤ ∨ c ≠ ⊥) : c < a - b ↔ c + b < a :=
  lt_iff_lt_of_le_iff_le (sub_le_iff_le_add h₁ h₂)

theorem sub_le_of_le_add {a b c : WithBotTop α} (h : a ≤ b + c) : a - c ≤ b := by
  cases c using WithBotTop.rec with
  | bot =>
      rw [add_bot, le_bot_iff] at h
      simp [h]
  | top =>
      simp
  | coe c =>
      exact (sub_le_iff_le_add
        (b := ((c : α) : WithBotTop α)) (c := b) (.inl (WithBotTop.coe_ne_bot))
        (.inl (WithBotTop.coe_ne_top))).2 h

lemma add_le_of_le_sub {a b c : WithBotTop α} (h : a ≤ b - c) : a + c ≤ b := by
  rw [← neg_neg c]
  exact sub_le_of_le_add h

lemma sub_lt_iff {a b c : WithBotTop α} (h₁ : b ≠ ⊥ ∨ c ≠ ⊥) (h₂ : b ≠ ⊤ ∨ c ≠ ⊤) :
    c - b < a ↔ c < a + b :=
  lt_iff_lt_of_le_iff_le (le_sub_iff_add_le h₁ h₂)

lemma add_lt_of_lt_sub {a b c : WithBotTop α} (h : a < b - c) : a + c < b := by
  contrapose! h
  exact sub_le_of_le_add h

lemma sub_lt_of_lt_add {a b c : WithBotTop α} (h : a < b + c) : a - c < b :=
  add_lt_of_lt_sub <| by rwa [sub_eq_add_neg, neg_neg]

lemma sub_lt_of_lt_add' {a b c : WithBotTop α} (h : a < b + c) : a - b < c :=
  sub_lt_of_lt_add <| by rwa [add_comm]

end OrderedSub

section DenseOrder

variable {α : Type u} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [DenselyOrdered α]

lemma add_le_of_forall_lt {a b c : WithBotTop α}
    (h : ∀ a' < a, ∀ b' < b, a' + b' ≤ c) : a + b ≤ c := by
  sorry

lemma le_add_of_forall_gt {a b c : WithBotTop α} (h₁ : a ≠ ⊥ ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ b ≠ ⊥)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' + b') : c ≤ a + b := by
  sorry

end DenseOrder

end WithBotTop
