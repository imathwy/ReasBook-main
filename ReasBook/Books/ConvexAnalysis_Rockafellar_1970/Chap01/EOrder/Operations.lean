import ConvexAnalysis_Rockafellar_1970.Chap01.Eorder.Operations

/-!
Compatibility wrapper for the canonical negation and subtraction owner layer.
The implementation currently lives in `ConvexAnalysis_Rockafellar_1970.Chap01.Eorder.Operations`.
-/

universe u

namespace WithTopBot

section Neg

variable {α : Type u} [Neg α]

/-- Boundary-swapping negation on the canonical `WithTopBot` owner. -/
protected def neg : WithTopBot α → WithTopBot α
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (a : α) => (-a : α)

instance instNeg : Neg (WithTopBot α) := ⟨WithTopBot.neg⟩

@[simp] theorem neg_top : -(⊤ : WithTopBot α) = ⊥ := rfl

@[simp] theorem neg_bot : -(⊥ : WithTopBot α) = ⊤ := rfl

theorem coe_neg (a : α) : ((-a : α) : WithTopBot α) = -(a : WithTopBot α) := rfl

@[simp] theorem neg_coe_bot :
    -(((⊥ : WithBot α) : WithTop (WithBot α))) = (⊤ : WithTopBot α) := rfl

@[simp] theorem neg_coe_coe (a : α) :
    -((((a : α) : WithBot α) : WithTop (WithBot α))) = ((-a : α) : WithTopBot α) := rfl

end Neg

section InvolutiveNeg

variable {α : Type u} [InvolutiveNeg α]

instance instInvolutiveNeg : InvolutiveNeg (WithTopBot α) where
  neg_neg x := by
    induction x using WithTop.recTopCoe with
    | top => rfl
    | coe x =>
        induction x using WithBot.recBotCoe with
        | bot => rfl
        | coe a =>
            change (((-(-a) : α) : α) : WithTopBot α) = (a : WithTopBot α)
            rw [neg_neg]

end InvolutiveNeg

section OrderedNeg

variable {α : Type u} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

@[simp] theorem neg_le_neg_iff {a b : WithTopBot α} : -a ≤ -b ↔ b ≤ a := by
  induction a using WithTop.recTopCoe with
  | top =>
      induction b using WithTop.recTopCoe with
      | top => simp
      | coe b =>
          induction b using WithBot.recBotCoe with
          | bot => simp
          | coe b => simp
  | coe a =>
      induction a using WithBot.recBotCoe with
      | bot =>
          induction b using WithTop.recTopCoe with
          | top => simp
          | coe b =>
              induction b using WithBot.recBotCoe with
              | bot => simp
              | coe b => simp [neg_coe_coe]
      | coe a =>
          induction b using WithTop.recTopCoe with
          | top => simp [neg_top, neg_coe_coe]
          | coe b =>
              induction b using WithBot.recBotCoe with
              | bot => simp
              | coe b =>
                  change
                    (((-a : α) : WithBot α) : WithTop (WithBot α)) ≤
                        (((-b : α) : WithBot α) : WithTop (WithBot α)) ↔
                      (((b : α) : WithBot α) : WithTop (WithBot α)) ≤
                        (((a : α) : WithBot α) : WithTop (WithBot α))
                  rw [WithTop.coe_le_coe, WithTop.coe_le_coe,
                    WithBot.coe_le_coe, WithBot.coe_le_coe]
                  exact _root_.neg_le_neg_iff

/-- Negation identifies `WithTopBot α` with its order dual. -/
def negOrderIso : WithTopBot α ≃o (WithTopBot α)ᵒᵈ where
  toFun := fun x => OrderDual.toDual (-x)
  invFun := fun x => -OrderDual.ofDual x
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  map_rel_iff' := by
    intro a b
    exact neg_le_neg_iff

@[simp] theorem negOrderIso_apply (x : WithTopBot α) :
    negOrderIso x = OrderDual.toDual (-x) := rfl

end OrderedNeg

section Sub

variable {α : Type u} [Add α] [Neg α]

/-- Subtraction on the canonical `WithTopBot` owner, defined by addition and the
boundary-swapping negation. -/
protected def sub (x y : WithTopBot α) : WithTopBot α :=
  x + (-y)

instance instSub : Sub (WithTopBot α) := ⟨WithTopBot.sub⟩

@[simp] theorem sub_eq_add_neg (x y : WithTopBot α) : x - y = x + (-y) :=
  rfl

end Sub

section OrderedSub

variable {α : Type u} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- Subtraction by a finite extended value may be moved across an inequality. -/
theorem sub_le_iff_le_add_of_ne_top_ne_bot {a b c : WithTopBot α}
    (hb_bot : b ≠ ⊥) (hb_top : b ≠ ⊤) : a - b ≤ c ↔ a ≤ c + b := by
  induction b using WithTop.recTopCoe with
  | top => exact False.elim (hb_top rfl)
  | coe b =>
      induction b using WithBot.recBotCoe with
      | bot => exact False.elim (hb_bot rfl)
      | coe b =>
          induction a using WithTop.recTopCoe with
          | top =>
              induction c using WithTop.recTopCoe <;> simp [sub_eq_add_neg]
          | coe a =>
              induction a using WithBot.recBotCoe with
              | bot =>
                  induction c using WithTop.recTopCoe with
                  | top => simp [sub_eq_add_neg]
                  | coe c =>
                      induction c using WithBot.recBotCoe <;>
                        rw [sub_eq_add_neg, ← WithTopBot.coe_neg,
                          ← WithTop.coe_add, WithBot.bot_add] <;> simp
              | coe a =>
                  induction c using WithTop.recTopCoe with
                  | top => simp [sub_eq_add_neg]
                  | coe c =>
                      induction c using WithBot.recBotCoe with
                      | bot =>
                          rw [sub_eq_add_neg, ← WithTopBot.coe_neg,
                            ← WithTop.coe_add, ← WithTop.coe_add,
                            WithBot.bot_add, ← WithBot.coe_add]
                          constructor
                          · intro h
                            exact False.elim
                              ((not_le_of_gt (WithBot.bot_lt_coe _))
                                (WithTop.coe_le_coe.mp h))
                          · intro h
                            exact False.elim
                              ((not_le_of_gt (WithBot.bot_lt_coe _))
                                (WithTop.coe_le_coe.mp h))
                      | coe c =>
                          change
                            (((a + -b : α) : WithBot α) : WithTop (WithBot α)) ≤
                                (((c : α) : WithBot α) : WithTop (WithBot α)) ↔
                              (((a : α) : WithBot α) : WithTop (WithBot α)) ≤
                                (((c + b : α) : WithBot α) : WithTop (WithBot α))
                          rw [WithTop.coe_le_coe, WithTop.coe_le_coe,
                            WithBot.coe_le_coe, WithBot.coe_le_coe]
                          simpa [sub_eq_add_neg] using
                            (_root_.sub_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b)

end OrderedSub

end WithTopBot
