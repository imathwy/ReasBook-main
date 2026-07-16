import ConvexAnalysis_Rockafellar_1970.Chap01.Eorder.Inv

/-!
Higher boundary-facing division surface for `WithBotTop α`.

This file extends the primitive `inv/div` owner with the first genuinely reusable high-level
division theorems supported by the current generic multiplicative surface.
-/

universe u

namespace WithBotTop

section LinearOrderedCommGroupWithZero

variable {α : Type u} [LinearOrderedCommGroupWithZero α]

theorem top_div_of_pos_ne_top {a : WithBotTop α} (h : (0 : WithBotTop α) < a) (h_top : a ≠ ⊤) :
    (⊤ : WithBotTop α) / a = ⊤ := by
  lift a to α using ⟨ne_bot_of_gt h, h_top⟩
  rw [WithBotTop.div_eq_mul_inv]
  have ha : (0 : α) < a := WithBotTop.coe_pos.mp h
  simpa [WithBotTop.coe_inv] using
    (WithBotTop.top_mul_coe_of_pos (_root_.inv_pos_of_pos ha))

theorem top_div_of_neg_ne_bot {a : WithBotTop α} (h : a < (0 : WithBotTop α)) (h_bot : a ≠ ⊥) :
    (⊤ : WithBotTop α) / a = ⊥ := by
  lift a to α using ⟨h_bot, ne_top_of_lt h⟩
  rw [WithBotTop.div_eq_mul_inv]
  have ha : (a : α) < 0 := WithBotTop.coe_neg'.mp h
  simpa [WithBotTop.coe_inv] using
    (WithBotTop.top_mul_coe_of_neg ((_root_.inv_lt_zero).2 ha))

theorem bot_div_of_pos_ne_top {a : WithBotTop α} (h : (0 : WithBotTop α) < a) (h_top : a ≠ ⊤) :
    (⊥ : WithBotTop α) / a = ⊥ := by
  lift a to α using ⟨ne_bot_of_gt h, h_top⟩
  rw [WithBotTop.div_eq_mul_inv]
  have ha : (0 : α) < a := WithBotTop.coe_pos.mp h
  simpa [WithBotTop.coe_inv] using
    (WithBotTop.bot_mul_coe_of_pos (_root_.inv_pos_of_pos ha))

theorem bot_div_of_neg_ne_bot {a : WithBotTop α} (h : a < (0 : WithBotTop α)) (h_bot : a ≠ ⊥) :
    (⊥ : WithBotTop α) / a = ⊤ := by
  lift a to α using ⟨h_bot, ne_top_of_lt h⟩
  rw [WithBotTop.div_eq_mul_inv]
  have ha : (a : α) < 0 := WithBotTop.coe_neg'.mp h
  simpa [WithBotTop.coe_inv] using
    (WithBotTop.bot_mul_coe_of_neg ((_root_.inv_lt_zero).2 ha))

@[simp] theorem top_div_coe_of_pos {a : α} (ha : 0 < a) :
    (⊤ : WithBotTop α) / (a : WithBotTop α) = ⊤ := by
  exact top_div_of_pos_ne_top (a := (a : WithBotTop α)) (WithBotTop.coe_pos.mpr ha) (by simp)

@[simp] theorem top_div_coe_of_neg {a : α} (ha : a < 0) :
    (⊤ : WithBotTop α) / (a : WithBotTop α) = ⊥ := by
  exact top_div_of_neg_ne_bot (a := (a : WithBotTop α)) (WithBotTop.coe_neg'.mpr ha) (by simp)

@[simp] theorem bot_div_coe_of_pos {a : α} (ha : 0 < a) :
    (⊥ : WithBotTop α) / (a : WithBotTop α) = ⊥ := by
  exact bot_div_of_pos_ne_top (a := (a : WithBotTop α)) (WithBotTop.coe_pos.mpr ha) (by simp)

@[simp] theorem bot_div_coe_of_neg {a : α} (ha : a < 0) :
    (⊥ : WithBotTop α) / (a : WithBotTop α) = ⊤ := by
  exact bot_div_of_neg_ne_bot (a := (a : WithBotTop α)) (WithBotTop.coe_neg'.mpr ha) (by simp)

theorem div_nonneg {a b : WithBotTop α} (ha : (0 : WithBotTop α) ≤ a)
    (hb : (0 : WithBotTop α) ≤ b) : (0 : WithBotTop α) ≤ a / b := by
  rw [WithBotTop.div_eq_mul_inv]
  exact WithBotTop.mul_nonneg ha (WithBotTop.inv_nonneg_of_nonneg hb)

theorem div_pos {a b : WithBotTop α} (ha : (0 : WithBotTop α) < a) (hb : (0 : WithBotTop α) < b)
    (h_top : b ≠ ⊤) : (0 : WithBotTop α) < a / b := by
  rw [WithBotTop.div_eq_mul_inv]
  exact WithBotTop.mul_pos ha (WithBotTop.inv_pos_of_pos_ne_top hb h_top)

protected theorem div_eq_inv_mul (a b : WithBotTop α) : a / b = b⁻¹ * a := by
  sorry

lemma mul_inv (a b : WithBotTop α) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  sorry

lemma div_self {a : WithBotTop α} (h_bot : a ≠ ⊥) (h_top : a ≠ ⊤) (h_zero : a ≠ 0) :
    a / a = 1 := by
  sorry

lemma mul_div (a b c : WithBotTop α) : a * (b / c) = (a * b) / c := by
  sorry

lemma mul_div_right (a b c : WithBotTop α) : a / b * c = a * c / b := by
  sorry

lemma mul_div_left_comm (a b c : WithBotTop α) : a * (b / c) = b * (a / c) := by
  sorry

lemma div_div (a b c : WithBotTop α) : a / b / c = a / (b * c) := by
  sorry

lemma div_mul_div_comm (a b c d : WithBotTop α) : a / b * (c / d) = a * c / (b * d) := by
  sorry

lemma div_mul_cancel {a b : WithBotTop α} (h_bot : b ≠ ⊥) (h_top : b ≠ ⊤) (h_zero : b ≠ 0) :
    a / b * b = a := by
  sorry

lemma mul_div_cancel {a b : WithBotTop α} (h_bot : b ≠ ⊥) (h_top : b ≠ ⊤) (h_zero : b ≠ 0) :
    b * (a / b) = a := by
  sorry

lemma mul_div_mul_cancel {a b c : WithBotTop α} (h_bot : c ≠ ⊥) (h_top : c ≠ ⊤)
    (h_zero : c ≠ 0) : a * c / (b * c) = a / b := by
  sorry

lemma div_eq_iff {a b c : WithBotTop α} (h_bot : b ≠ ⊥) (h_top : b ≠ ⊤) (h_zero : b ≠ 0) :
    c / b = a ↔ c = a * b := by
  sorry

lemma monotone_div_right_of_nonneg {b : WithBotTop α} (h : (0 : WithBotTop α) ≤ b) :
    Monotone fun a => a / b := by
  sorry

lemma div_le_div_right_of_nonneg {a b c : WithBotTop α} (h : (0 : WithBotTop α) ≤ c)
    (h' : a ≤ b) : a / c ≤ b / c := by
  sorry

lemma strictMono_div_right_of_pos {b : WithBotTop α} (h : (0 : WithBotTop α) < b) (h_top : b ≠ ⊤) :
    StrictMono fun a => a / b := by
  sorry

lemma div_lt_div_right_of_pos {a b c : WithBotTop α} (h₁ : (0 : WithBotTop α) < c) (h₂ : c ≠ ⊤)
    (h₃ : a < b) : a / c < b / c := by
  sorry

lemma antitone_div_right_of_nonpos {b : WithBotTop α} (h : b ≤ (0 : WithBotTop α)) :
    Antitone fun a => a / b := by
  sorry

lemma div_le_div_right_of_nonpos {a b c : WithBotTop α} (h : c ≤ (0 : WithBotTop α))
    (h' : a ≤ b) : b / c ≤ a / c := by
  sorry

lemma strictAnti_div_right_of_neg {b : WithBotTop α} (h : b < (0 : WithBotTop α)) (h_bot : b ≠ ⊥) :
    StrictAnti fun a => a / b := by
  sorry

lemma div_lt_div_right_of_neg {a b c : WithBotTop α} (h₁ : c < (0 : WithBotTop α)) (h₂ : c ≠ ⊥)
    (h₃ : a < b) : b / c < a / c := by
  sorry

lemma le_div_iff_mul_le {a b c : WithBotTop α} (h : (0 : WithBotTop α) < b) (h_top : b ≠ ⊤) :
    a ≤ c / b ↔ a * b ≤ c := by
  sorry

lemma div_le_iff_le_mul {a b c : WithBotTop α} (h : (0 : WithBotTop α) < b) (h_top : b ≠ ⊤) :
    a / b ≤ c ↔ a ≤ b * c := by
  sorry

lemma lt_div_iff {a b c : WithBotTop α} (h : (0 : WithBotTop α) < b) (h_top : b ≠ ⊤) :
    a < c / b ↔ a * b < c := by
  sorry

lemma div_lt_iff {a b c : WithBotTop α} (h : (0 : WithBotTop α) < c) (h_top : c ≠ ⊤) :
    b / c < a ↔ b < a * c := by
  sorry

lemma div_nonpos_of_nonpos_of_nonneg {a b : WithBotTop α} (h : a ≤ (0 : WithBotTop α))
    (h' : (0 : WithBotTop α) ≤ b) : a / b ≤ 0 := by
  sorry

lemma div_nonpos_of_nonneg_of_nonpos {a b : WithBotTop α} (h : (0 : WithBotTop α) ≤ a)
    (h' : b ≤ (0 : WithBotTop α)) : a / b ≤ 0 := by
  sorry

lemma div_nonneg_of_nonpos_of_nonpos {a b : WithBotTop α} (h : a ≤ (0 : WithBotTop α))
    (h' : b ≤ (0 : WithBotTop α)) : (0 : WithBotTop α) ≤ a / b := by
  sorry

end LinearOrderedCommGroupWithZero

section LinearOrderedField

variable {α : Type u} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem natCast_div_le (m n : ℕ) :
    ((m / n : ℕ) : WithBotTop α) ≤ (m : WithBotTop α) / (n : WithBotTop α) := by
  sorry

lemma div_right_distrib_of_nonneg {a b c : WithBotTop α} (ha : (0 : WithBotTop α) ≤ a)
    (hb : (0 : WithBotTop α) ≤ b) : (a + b) / c = a / c + b / c := by
  sorry

lemma add_div_of_nonneg_right {a b c : WithBotTop α} (hc : (0 : WithBotTop α) ≤ c) :
    (a + b) / c = a / c + b / c := by
  sorry

end LinearOrderedField

end WithBotTop
