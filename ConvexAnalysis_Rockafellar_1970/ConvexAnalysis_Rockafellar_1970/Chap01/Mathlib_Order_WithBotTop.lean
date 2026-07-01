/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kevin Buzzard
-/
module

public import Mathlib.Order.WithBot

/-!
# Adding both `⊥` and `⊤` to a type

This files defines an abbreviation `WithBotTop ι` for `WithBot (WithTop ι)`.
We also introduce an abbreviation `EInt` for `WithBotTop ℤ`.
-/

@[expose] public section

variable {ι : Type*}

variable (ι) in
/-- The type obtained by adding both `⊥` and `⊤` to a type. -/
@[to_dual /-- The type obtained by adding both `⊤` and `⊥` to a type. -/]
abbrev WithBotTop := WithBot (WithTop ι)

/-- The canonical inclusion `ι → WithBotTop ι`. Registered as a coercion. -/
@[coe] def WithBotTop.coe : ι → WithBotTop ι :=
  WithBot.some ∘ WithTop.some

namespace WithBotTop

instance : Coe ι (WithBotTop ι) := ⟨WithBotTop.coe⟩

theorem coe_injective : Function.Injective (WithBotTop.coe : ι → _) := by rintro _ _ ⟨⟩; rfl

@[simp, norm_cast]
theorem coe_inj {a b : ι} : (a : WithBotTop ι) = b ↔ a = b := coe_injective.eq_iff

@[simp] lemma coe_ne_bot {a : ι} : (a : WithBotTop ι) ≠ ⊥ := by rintro ⟨⟩
@[simp] lemma bot_ne_coe {a : ι} : ⊥ ≠ (a : WithBotTop ι) := by rintro ⟨⟩
@[simp] lemma coe_ne_top {a : ι} : (a : WithBotTop ι) ≠ ⊤ := by rintro ⟨⟩
@[simp] lemma top_ne_coe {a : ι} : ⊤ ≠ (a : WithBotTop ι) := by rintro ⟨⟩
@[simp] lemma top_ne_bot : (⊤ : WithBotTop ι) ≠ ⊥ := by rintro ⟨⟩
@[simp] lemma bot_ne_top : (⊥ : WithBotTop ι) ≠ ⊤ := by rintro ⟨⟩

protected theorem «forall» {p : WithBotTop ι → Prop} :
    (∀ r, p r) ↔ p ⊥ ∧ p ⊤ ∧ ∀ r : ι, p r :=
  WithBot.forall.trans (and_congr_right fun _ => WithTop.forall)

protected theorem «exists» {p : WithBotTop ι → Prop} :
    (∃ r, p r) ↔ p ⊥ ∨ p ⊤ ∨ ∃ r : ι, p r :=
  WithBot.exists.trans (or_congr_right WithTop.exists)

section

variable {motive : (WithBotTop ι) → Sort*}
  (bot : motive ⊥) (coe : ∀ a : ι, motive a) (top : motive ⊤)

/-- A recursor for `WithBotTop` in terms of the coercion. -/
@[elab_as_elim]
protected def rec : ∀ a, motive a
  | ⊥ => bot
  | (a : ι) => coe a
  | ⊤ => top

@[simp] lemma rec_bot : WithBotTop.rec (motive := motive) bot coe top ⊥ = bot := rfl
@[simp] lemma rec_coe (a : ι) : WithBotTop.rec (motive := motive) bot coe top a = coe a := rfl
@[simp] lemma rec_top : WithBotTop.rec (motive := motive) bot coe top ⊤ = top := rfl

end

/-- The canonical unwrap function for `WithBotTop ι`. -/
def unbdryD (d : ι) (x : WithBotTop ι) : ι :=
  (x.unbotD (d : WithTop ι)).untopD d

@[simp]
theorem unbdryD_bot (d : ι) : unbdryD d (⊥ : WithBotTop ι) = d := rfl

@[simp]
theorem unbdryD_top (d : ι) : unbdryD d (⊤ : WithBotTop ι) = d := rfl

@[simp]
theorem unbdryD_coe (d a : ι) : unbdryD d (a : WithBotTop ι) = a := rfl

theorem unbdryD_eq_iff {d y : ι} {x : WithBotTop ι} :
    unbdryD d x = y ↔ x = y ∨ (x = ⊥ ∨ x = ⊤) ∧ y = d := by
  cases x using WithBotTop.rec <;> simp [eq_comm]

@[simp]
theorem unbdryD_eq_self_iff {d : ι} {x : WithBotTop ι} :
    unbdryD d x = d ↔ x = d ∨ x = ⊥ ∨ x = ⊤ := by
  simp [unbdryD_eq_iff]

def unbdry : ∀ x : WithBotTop ι, x ≠ ⊥ → x ≠ ⊤ → ι | (x : ι), _, _ => x

@[simp]
lemma coe_unbdry (x : WithBotTop ι) (h : x ≠ ⊥) (h' : x ≠ ⊤) :
    (x.unbdry h h' : WithBotTop ι) = x :=
  match x with | (x : ι) => rfl

@[simp]
lemma unbdry_coe (x : ι) (h : (x : WithBotTop ι) ≠ ⊥ := coe_ne_bot)
    (h' : (x : WithBotTop ι) ≠ ⊤ := coe_ne_top) : (x : WithBotTop ι).unbdry h h' = x :=
  rfl

theorem unbdry_eq_iff {a : WithBotTop ι} {b : ι} (h : a ≠ ⊥) (h' : a ≠ ⊤) :
    a.unbdry h h' = b ↔ a = b := by
  match a with | (a : ι) => simp

theorem eq_unbdry_iff {a : ι} {b : WithBotTop ι} (h : b ≠ ⊥) (h' : b ≠ ⊤) :
    a = b.unbdry h h' ↔ a = b := by
  match b with | (a : ι) => simp

theorem unbdry_inj {a b : WithBotTop ι} (ha : a ≠ ⊥) (hb : b ≠ ⊥) (ha' : a ≠ ⊤) (hb' : b ≠ ⊤) :
    a.unbdry ha ha' = b.unbdry hb hb' ↔ a = b := by
  rw [unbdry_eq_iff, coe_unbdry]

noncomputable abbrev unbdryA [Nonempty ι] : WithBotTop ι → ι := unbdryD (Classical.arbitrary ι)

lemma unbdryA_eq_unbdry [Nonempty ι] {a : WithBotTop ι} (ha : a ≠ ⊥) (ha' : a ≠ ⊤) :
    unbdryA a = unbdry a ha ha' := by
  match a with | (a : ι) => simp

instance canLift : CanLift (WithBotTop ι) ι (↑) fun r => r ≠ ⊥ ∧ r ≠ ⊤ where
  prf | (a : ι), _ => ⟨a, rfl⟩

/-- The equivalence between the non-boundary elements of `WithBotTop α` and `α`. -/
@[simp]
def _root_.Equiv.withBotTopSubtypeNe : {y : WithBotTop ι // y ≠ ⊥ ∧ y ≠ ⊤} ≃ ι where
  toFun := fun ⟨x,h⟩ => (unbdry x h.1 h.2)
  invFun x := ⟨x, ⟨coe_ne_bot, coe_ne_top⟩⟩
  left_inv x := by simp
  right_inv x := by simp

section LE

variable [LE ι]

@[simp]
lemma coe_le_coe {a b : ι} :
    (a : WithBotTop ι) ≤ b ↔ a ≤ b := by
  rw [← WithTop.coe_le_coe (α := ι)]
  exact WithBot.coe_le_coe

@[simp]
lemma bot_le_coe {a : ι} : (⊥ : WithBotTop ι) ≤ a :=
  WithBot.bot_le_coe _

@[simp]
lemma coe_le_top {a : ι} : (a : WithBotTop ι) ≤ ⊤ :=
  WithBot.coe_le_coe.2 <| WithTop.coe_le_top _

@[simp]
lemma not_coe_le_bot {a : ι} : ¬(a : WithBotTop ι) ≤ ⊥ :=
  WithBot.not_coe_le_bot (a : WithTop ι)

@[simp]
lemma not_top_le_coe {a : ι} : ¬(⊤ : WithBotTop ι) ≤ a :=
  fun h ↦ WithTop.not_top_le_coe a (WithBot.coe_le_coe.mp h)

lemma le_def {x y : WithBotTop ι} :
    x ≤ y ↔ x = ⊥ ∨ y = ⊤ ∨ ∃ a b : ι, a ≤ b ∧ x = a ∧ y = b := by
  cases x using WithBotTop.rec <;> cases y using WithBotTop.rec <;> simp

@[simp]
protected theorem le_bot_iff : ∀ {x : WithBotTop ι}, x ≤ ⊥ ↔ x = ⊥ := by
  intro x; cases x using WithBotTop.rec <;> simp

@[simp]
protected theorem top_le_iff : ∀ {x : WithBotTop ι}, ⊤ ≤ x ↔ x = ⊤ := by
  intro x; cases x using WithBotTop.rec <;> simp

end LE

section LT

variable [LT ι]

@[simp]
lemma coe_lt_coe {a b : ι} :
    (a : WithBotTop ι) < b ↔ a < b := by
  rw [← WithTop.coe_lt_coe (α := ι)]
  exact WithBot.coe_lt_coe

@[simp]
lemma bot_lt_coe {a : ι} : (⊥ : WithBotTop ι) < a :=
  WithBot.bot_lt_coe _

@[simp]
lemma coe_lt_top {a : ι} : (a : WithBotTop ι) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

end LT

section Preorder

variable [Preorder ι]

@[simp]
theorem coe_strictMono : StrictMono (WithBotTop.coe : ι → _) :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

lemma coe_monotone :
    Monotone (WithBotTop.coe : ι → _) :=
  fun _ _ _ ↦ by simpa

theorem eq_top_iff_forall_gt [Nonempty ι] {x : WithBotTop ι} :
    x = ⊤ ↔ ∀ y : ι, y < x := by
  cases x using WithBotTop.rec <;> simp; simpa using ⟨_, lt_irrefl _⟩

theorem eq_bot_iff_forall_lt [Nonempty ι] {x : WithBotTop ι} :
    x = ⊥ ↔ ∀ y : ι, x < y := by
  cases x using WithBotTop.rec <;> simp; simpa using ⟨_, lt_irrefl _⟩

end Preorder

end WithBotTop

/-- The type of extended integers `[-∞, ∞]`, constructed as `WithBot (WithTop ℤ)`. -/
abbrev EInt := WithBotTop ℤ
