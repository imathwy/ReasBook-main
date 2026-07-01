import Mathlib.Algebra.Order.WithBotTop.Add
import Mathlib.Algebra.Order.WithBotTop.MulZero
import Mathlib.Algebra.BigOperators.WithTop

/-!
Finite-sum theorem layer for `WithBotTop α`.

This file is intentionally a statement-only staging layer. It collects the finite-sum API that is
natural for the chapter-facing `WithBotTop α` surface without mixing it into the primitive owner
files.
-/

universe u

open Finset

namespace WithBotTop

section AddCommMonoid

variable {ι : Type*} {α : Type u} [AddCommMonoid α]

@[simp] theorem coe_sum (s : Finset ι) (f : ι → α) :
    ((∑ i ∈ s, f i : α) : WithBotTop α) = ∑ i ∈ s, (f i : WithBotTop α) := by
  sorry

@[simp] theorem sum_eq_bot_iff {s : Finset ι} {f : ι → WithBotTop α} :
    (∑ i ∈ s, f i) = (⊥ : WithBotTop α) ↔ ∃ i ∈ s, f i = ⊥ := by
  sorry

theorem sum_ne_bot_iff {s : Finset ι} {f : ι → WithBotTop α} :
    (∑ i ∈ s, f i) ≠ (⊥ : WithBotTop α) ↔ ∀ i ∈ s, f i ≠ ⊥ := by
  sorry

theorem sum_eq_bot_of_exists_eq_bot {s : Finset ι} {f : ι → WithBotTop α}
    (hbot : ∃ i ∈ s, f i = ⊥) :
    (∑ i ∈ s, f i) = (⊥ : WithBotTop α) := by
  sorry

theorem sum_eq_bot_of_mem {s : Finset ι} {f : ι → WithBotTop α} {i : ι}
    (hi : i ∈ s) (hbot : f i = ⊥) :
    (∑ j ∈ s, f j) = (⊥ : WithBotTop α) := by
  sorry

theorem sum_ne_bot_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    (hbot : ∀ i ∈ s, f i ≠ ⊥) :
    (∑ i ∈ s, f i) ≠ (⊥ : WithBotTop α) := by
  sorry

@[simp] theorem sum_eq_top_iff_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    (hbot : ∀ i ∈ s, f i ≠ ⊥) :
    (∑ i ∈ s, f i) = (⊤ : WithBotTop α) ↔ ∃ i ∈ s, f i = ⊤ := by
  sorry

theorem sum_ne_top_iff_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    (hbot : ∀ i ∈ s, f i ≠ ⊥) :
    (∑ i ∈ s, f i) ≠ (⊤ : WithBotTop α) ↔ ∀ i ∈ s, f i ≠ ⊤ := by
  sorry

@[simp] theorem sum_eq_top_iff {s : Finset ι} {f : ι → WithBotTop α} :
    (∑ i ∈ s, f i) = (⊤ : WithBotTop α) ↔
      (∃ i ∈ s, f i = ⊤) ∧ ∀ i ∈ s, f i ≠ ⊥ := by
  sorry

theorem sum_eq_top_of_exists_eq_top_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    (htop : ∃ i ∈ s, f i = ⊤) (hbot : ∀ i ∈ s, f i ≠ ⊥) :
    (∑ i ∈ s, f i) = (⊤ : WithBotTop α) := by
  sorry

theorem sum_eq_top_of_mem_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α} {i : ι}
    (hi : i ∈ s) (htop : f i = ⊤) (hbot : ∀ j ∈ s, f j ≠ ⊥) :
    (∑ j ∈ s, f j) = (⊤ : WithBotTop α) := by
  sorry

theorem sum_ne_top_of_forall_ne_top_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    (htop : ∀ i ∈ s, f i ≠ ⊤) (hbot : ∀ i ∈ s, f i ≠ ⊥) :
    (∑ i ∈ s, f i) ≠ (⊤ : WithBotTop α) := by
  sorry

theorem ne_top_of_mem_of_sum_ne_top_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    {i : ι} (hi : i ∈ s) (hsum : (∑ j ∈ s, f j) ≠ (⊤ : WithBotTop α))
    (hbot : ∀ j ∈ s, f j ≠ ⊥) :
    f i ≠ ⊤ := by
  sorry

section DecidableEq

variable [DecidableEq ι]

theorem sum_eq_bot_iff_exists_eq_bot_insert {s : Finset ι} {f : ι → WithBotTop α} {i : ι}
    (hi : i ∉ s) :
    (∑ j ∈ insert i s, f j) = (⊥ : WithBotTop α) ↔
      f i = ⊥ ∨ ∃ j ∈ s, f j = ⊥ := by
  sorry

theorem sum_eq_top_iff_of_ne_bot_insert {s : Finset ι} {f : ι → WithBotTop α} {i : ι}
    (hi : i ∉ s) (hbot : ∀ j ∈ insert i s, f j ≠ ⊥) :
    (∑ j ∈ insert i s, f j) = (⊤ : WithBotTop α) ↔
      f i = ⊤ ∨ ∃ j ∈ s, f j = ⊤ := by
  sorry

theorem sum_ne_bot_iff_forall_ne_bot_insert {s : Finset ι} {f : ι → WithBotTop α} {i : ι}
    (hi : i ∉ s) :
    (∑ j ∈ insert i s, f j) ≠ (⊥ : WithBotTop α) ↔
      f i ≠ ⊥ ∧ ∀ j ∈ s, f j ≠ ⊥ := by
  sorry

theorem sum_ne_top_iff_of_forall_ne_bot_insert {s : Finset ι} {f : ι → WithBotTop α} {i : ι}
    (hi : i ∉ s) (hbot : ∀ j ∈ insert i s, f j ≠ ⊥) :
    (∑ j ∈ insert i s, f j) ≠ (⊤ : WithBotTop α) ↔
      f i ≠ ⊤ ∧ ∀ j ∈ s, f j ≠ ⊤ := by
  sorry

theorem sum_eq_bot_iff_exists_eq_bot_erase {s : Finset ι} {f : ι → WithBotTop α} {i : ι} :
    (∑ j ∈ s.erase i, f j) = (⊥ : WithBotTop α) ↔
      ∃ j ∈ s.erase i, f j = ⊥ := by
  sorry

theorem sum_eq_top_iff_of_forall_ne_bot_erase {s : Finset ι} {f : ι → WithBotTop α} {i : ι}
    (hbot : ∀ j ∈ s.erase i, f j ≠ ⊥) :
    (∑ j ∈ s.erase i, f j) = (⊤ : WithBotTop α) ↔
      ∃ j ∈ s.erase i, f j = ⊤ := by
  sorry

end DecidableEq

theorem sum_eq_bot_iff_exists_eq_bot_disjUnion {s t : Finset ι} {f : ι → WithBotTop α}
    (hst : Disjoint s t) :
    (∑ i ∈ s.disjUnion t hst, f i) = (⊥ : WithBotTop α) ↔
      (∃ i ∈ s, f i = ⊥) ∨ ∃ i ∈ t, f i = ⊥ := by
  sorry

theorem sum_eq_top_iff_of_forall_ne_bot_disjUnion {s t : Finset ι} {f : ι → WithBotTop α}
    (hst : Disjoint s t) (hbot : ∀ i ∈ s.disjUnion t hst, f i ≠ ⊥) :
    (∑ i ∈ s.disjUnion t hst, f i) = (⊤ : WithBotTop α) ↔
      (∃ i ∈ s, f i = ⊤) ∨ ∃ i ∈ t, f i = ⊤ := by
  sorry

theorem sum_ne_top_iff_of_forall_ne_bot_disjUnion {s t : Finset ι} {f : ι → WithBotTop α}
    (hst : Disjoint s t) (hbot : ∀ i ∈ s.disjUnion t hst, f i ≠ ⊥) :
    (∑ i ∈ s.disjUnion t hst, f i) ≠ (⊤ : WithBotTop α) ↔
      (∀ i ∈ s, f i ≠ ⊤) ∧ ∀ i ∈ t, f i ≠ ⊤ := by
  sorry

end AddCommMonoid

section OrderedAddCommMonoid

variable {ι : Type*} {α : Type u} [AddCommMonoid α] [LT α]

@[simp] theorem bot_lt_sum_iff {s : Finset ι} {f : ι → WithBotTop α} :
    (⊥ : WithBotTop α) < ∑ i ∈ s, f i ↔ ∀ i ∈ s, (⊥ : WithBotTop α) < f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih]

theorem bot_lt_sum {s : Finset ι} {f : ι → WithBotTop α}
    (h : ∀ i ∈ s, (⊥ : WithBotTop α) < f i) :
    (⊥ : WithBotTop α) < ∑ i ∈ s, f i := by
  sorry

@[simp] theorem sum_lt_top_iff_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    (hbot : ∀ i ∈ s, f i ≠ ⊥) :
    (∑ i ∈ s, f i) < (⊤ : WithBotTop α) ↔ ∀ i ∈ s, f i < ⊤ := by
  sorry

theorem sum_lt_top_of_forall_lt_top_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    (htop : ∀ i ∈ s, f i < ⊤) (hbot : ∀ i ∈ s, f i ≠ ⊥) :
    (∑ i ∈ s, f i) < (⊤ : WithBotTop α) := by
  sorry

theorem lt_top_of_mem_of_sum_lt_top_of_forall_ne_bot {s : Finset ι} {f : ι → WithBotTop α}
    {i : ι} (hi : i ∈ s) (hsum : (∑ j ∈ s, f j) < (⊤ : WithBotTop α))
    (hbot : ∀ j ∈ s, f j ≠ ⊥) :
    f i < ⊤ := by
  sorry

theorem bot_lt_sum_of_mem_of_forall_bot_lt {s : Finset ι} {f : ι → WithBotTop α} {i : ι}
    (hi : i ∈ s) (h : ∀ j ∈ s, (⊥ : WithBotTop α) < f j) :
    (⊥ : WithBotTop α) < ∑ j ∈ s, f j := by
  sorry

end OrderedAddCommMonoid

section Coe

variable {ι : Type*} {α : Type u} [AddCommMonoid α]

@[simp] theorem sum_coe (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) = ((∑ i ∈ s, f i : α) : WithBotTop α) := by
  sorry

@[simp] theorem sum_coe_eq_coe_iff (s : Finset ι) (f : ι → α) {a : α} :
    (∑ i ∈ s, (f i : WithBotTop α)) = (a : WithBotTop α) ↔ (∑ i ∈ s, f i : α) = a := by
  sorry

theorem sum_coe_ne_coe_iff (s : Finset ι) (f : ι → α) {a : α} :
    (∑ i ∈ s, (f i : WithBotTop α)) ≠ (a : WithBotTop α) ↔ (∑ i ∈ s, f i : α) ≠ a := by
  sorry

@[simp] theorem sum_coe_eq_zero_iff [Zero α] (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) = (0 : WithBotTop α) ↔ (∑ i ∈ s, f i : α) = 0 := by
  sorry

@[simp] theorem sum_coe_eq_one_iff [One α] (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) = (1 : WithBotTop α) ↔ (∑ i ∈ s, f i : α) = 1 := by
  sorry

@[simp] theorem sum_coe_eq_bot_iff (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) = (⊥ : WithBotTop α) ↔ False := by
  sorry

theorem sum_coe_ne_bot (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) ≠ (⊥ : WithBotTop α) := by
  sorry

@[simp] theorem sum_coe_eq_top_iff (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) = (⊤ : WithBotTop α) ↔ False := by
  sorry

theorem sum_coe_ne_top (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) ≠ (⊤ : WithBotTop α) := by
  sorry

end Coe

section OrderedCoe

variable {ι : Type*} {α : Type u} [AddCommMonoid α] [LT α]

@[simp] theorem bot_lt_sum_coe (s : Finset ι) (f : ι → α) :
    (⊥ : WithBotTop α) < ∑ i ∈ s, (f i : WithBotTop α) := by
  sorry

@[simp] theorem sum_coe_lt_top (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) < (⊤ : WithBotTop α) := by
  sorry

end OrderedCoe

section Distrib

variable {ι : Type*} {α : Type u}
variable [LT α] [DecidableLT α] [Zero α] [AddCommMonoid α] [Mul α]

theorem coe_mul_sum [LeftDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (a : WithBotTop α) * (∑ i ∈ s, (f i : WithBotTop α)) =
      ∑ i ∈ s, ((a * f i : α) : WithBotTop α) := by
  sorry

@[simp] theorem coe_mul_sum_eq_coe [LeftDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (a : WithBotTop α) * (∑ i ∈ s, (f i : WithBotTop α)) =
      (((a * ∑ i ∈ s, f i) : α) : WithBotTop α) := by
  sorry

@[simp] theorem coe_mul_sum_eq_coe_iff [LeftDistribClass α] (a : α) (s : Finset ι)
    (f : ι → α) {b : α} :
    (a : WithBotTop α) * (∑ i ∈ s, (f i : WithBotTop α)) = (b : WithBotTop α) ↔
      (a * ∑ i ∈ s, f i : α) = b := by
  sorry

@[simp] theorem coe_mul_sum_eq_zero_iff [LeftDistribClass α] (a : α) (s : Finset ι)
    (f : ι → α) :
    (a : WithBotTop α) * (∑ i ∈ s, (f i : WithBotTop α)) = (0 : WithBotTop α) ↔
      (a * ∑ i ∈ s, f i : α) = 0 := by
  sorry

@[simp] theorem coe_mul_sum_eq_one_iff [LeftDistribClass α] [One α] (a : α) (s : Finset ι)
    (f : ι → α) :
    (a : WithBotTop α) * (∑ i ∈ s, (f i : WithBotTop α)) = (1 : WithBotTop α) ↔
      (a * ∑ i ∈ s, f i : α) = 1 := by
  sorry

theorem coe_mul_sum_ne_bot [LeftDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (a : WithBotTop α) * (∑ i ∈ s, (f i : WithBotTop α)) ≠ (⊥ : WithBotTop α) := by
  sorry

theorem coe_mul_sum_ne_top [LeftDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (a : WithBotTop α) * (∑ i ∈ s, (f i : WithBotTop α)) ≠ (⊤ : WithBotTop α) := by
  sorry

@[simp] theorem coe_mul_sum_lt_top [LeftDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (a : WithBotTop α) * (∑ i ∈ s, (f i : WithBotTop α)) < (⊤ : WithBotTop α) := by
  sorry

theorem sum_mul_coe [RightDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) * (a : WithBotTop α) =
      ∑ i ∈ s, ((f i * a : α) : WithBotTop α) := by
  sorry

@[simp] theorem sum_mul_coe_eq_coe [RightDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) * (a : WithBotTop α) =
      ((∑ i ∈ s, f i * a : α) : WithBotTop α) := by
  sorry

@[simp] theorem sum_mul_coe_eq_coe_iff [RightDistribClass α] (a : α) (s : Finset ι)
    (f : ι → α) {b : α} :
    (∑ i ∈ s, (f i : WithBotTop α)) * (a : WithBotTop α) = (b : WithBotTop α) ↔
      (∑ i ∈ s, f i * a : α) = b := by
  sorry

@[simp] theorem sum_mul_coe_eq_zero_iff [RightDistribClass α] (a : α) (s : Finset ι)
    (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) * (a : WithBotTop α) = (0 : WithBotTop α) ↔
      (∑ i ∈ s, f i * a : α) = 0 := by
  sorry

@[simp] theorem sum_mul_coe_eq_one_iff [RightDistribClass α] [One α] (a : α) (s : Finset ι)
    (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) * (a : WithBotTop α) = (1 : WithBotTop α) ↔
      (∑ i ∈ s, f i * a : α) = 1 := by
  sorry

theorem sum_mul_coe_ne_bot [RightDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) * (a : WithBotTop α) ≠ (⊥ : WithBotTop α) := by
  sorry

theorem sum_mul_coe_ne_top [RightDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) * (a : WithBotTop α) ≠ (⊤ : WithBotTop α) := by
  sorry

@[simp] theorem sum_mul_coe_lt_top [RightDistribClass α] (a : α) (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, (f i : WithBotTop α)) * (a : WithBotTop α) < (⊤ : WithBotTop α) := by
  sorry

section DecidableEq

variable [DecidableEq ι]

theorem coe_mul_sum_insert [LeftDistribClass α] (a : α) {s : Finset ι} (f : ι → α) {i : ι}
    (hi : i ∉ s) :
    (a : WithBotTop α) * (∑ j ∈ insert i s, (f j : WithBotTop α)) =
      ((a * f i : α) : WithBotTop α) + ∑ j ∈ s, ((a * f j : α) : WithBotTop α) := by
  sorry

theorem sum_mul_coe_insert [RightDistribClass α] (a : α) {s : Finset ι} (f : ι → α) {i : ι}
    (hi : i ∉ s) :
    (∑ j ∈ insert i s, (f j : WithBotTop α)) * (a : WithBotTop α) =
      ((f i * a : α) : WithBotTop α) + ∑ j ∈ s, ((f j * a : α) : WithBotTop α) := by
  sorry

theorem coe_mul_sum_erase [LeftDistribClass α] (a : α) {s : Finset ι} (f : ι → α) {i : ι} :
    (a : WithBotTop α) * (∑ j ∈ s.erase i, (f j : WithBotTop α)) =
      ∑ j ∈ s.erase i, ((a * f j : α) : WithBotTop α) := by
  sorry

theorem sum_mul_coe_erase [RightDistribClass α] (a : α) {s : Finset ι} (f : ι → α) {i : ι} :
    (∑ j ∈ s.erase i, (f j : WithBotTop α)) * (a : WithBotTop α) =
      ∑ j ∈ s.erase i, ((f j * a : α) : WithBotTop α) := by
  sorry

end DecidableEq

theorem coe_mul_sum_disjUnion [LeftDistribClass α] (a : α) {s t : Finset ι} (f : ι → α)
    (hst : Disjoint s t) :
    (a : WithBotTop α) * (∑ i ∈ s.disjUnion t hst, (f i : WithBotTop α)) =
      (∑ i ∈ s, ((a * f i : α) : WithBotTop α)) + ∑ i ∈ t, ((a * f i : α) : WithBotTop α) := by
  sorry

theorem sum_mul_coe_disjUnion [RightDistribClass α] (a : α) {s t : Finset ι} (f : ι → α)
    (hst : Disjoint s t) :
    (∑ i ∈ s.disjUnion t hst, (f i : WithBotTop α)) * (a : WithBotTop α) =
      (∑ i ∈ s, ((f i * a : α) : WithBotTop α)) + ∑ i ∈ t, ((f i * a : α) : WithBotTop α) := by
  sorry

section DecidableEq

variable [DecidableEq ι]

@[simp] theorem coe_mul_sum_insert_eq_zero_iff [LeftDistribClass α] (a : α) {s : Finset ι}
    (f : ι → α) {i : ι} :
    (a : WithBotTop α) * (∑ j ∈ insert i s, (f j : WithBotTop α)) = (0 : WithBotTop α) ↔
      (a * (∑ j ∈ insert i s, f j) : α) = 0 := by
  sorry

@[simp] theorem sum_mul_coe_insert_eq_zero_iff [RightDistribClass α] (a : α) {s : Finset ι}
    (f : ι → α) {i : ι} :
    (∑ j ∈ insert i s, (f j : WithBotTop α)) * (a : WithBotTop α) = (0 : WithBotTop α) ↔
      ((∑ j ∈ insert i s, f j) * a : α) = 0 := by
  sorry

end DecidableEq

@[simp] theorem coe_mul_sum_disjUnion_eq_zero_iff [LeftDistribClass α] (a : α) {s t : Finset ι}
    (f : ι → α) (hst : Disjoint s t) :
    (a : WithBotTop α) * (∑ i ∈ s.disjUnion t hst, (f i : WithBotTop α)) = (0 : WithBotTop α) ↔
      (a * (∑ i ∈ s.disjUnion t hst, f i) : α) = 0 := by
  sorry

@[simp] theorem sum_mul_coe_disjUnion_eq_zero_iff [RightDistribClass α] (a : α)
    {s t : Finset ι} (f : ι → α) (hst : Disjoint s t) :
    (∑ i ∈ s.disjUnion t hst, (f i : WithBotTop α)) * (a : WithBotTop α) = (0 : WithBotTop α) ↔
      ((∑ i ∈ s.disjUnion t hst, f i) * a : α) = 0 := by
  sorry

section DecidableEq

variable [DecidableEq ι]

@[simp] theorem coe_mul_sum_insert_eq_one_iff [LeftDistribClass α] [One α] (a : α)
    {s : Finset ι} (f : ι → α) {i : ι} :
    (a : WithBotTop α) * (∑ j ∈ insert i s, (f j : WithBotTop α)) = (1 : WithBotTop α) ↔
      (a * (∑ j ∈ insert i s, f j) : α) = 1 := by
  sorry

@[simp] theorem sum_mul_coe_insert_eq_one_iff [RightDistribClass α] [One α] (a : α)
    {s : Finset ι} (f : ι → α) {i : ι} :
    (∑ j ∈ insert i s, (f j : WithBotTop α)) * (a : WithBotTop α) = (1 : WithBotTop α) ↔
      ((∑ j ∈ insert i s, f j) * a : α) = 1 := by
  sorry

end DecidableEq

@[simp] theorem coe_mul_sum_disjUnion_eq_one_iff [LeftDistribClass α] [One α] (a : α)
    {s t : Finset ι} (f : ι → α) (hst : Disjoint s t) :
    (a : WithBotTop α) * (∑ i ∈ s.disjUnion t hst, (f i : WithBotTop α)) = (1 : WithBotTop α) ↔
      (a * (∑ i ∈ s.disjUnion t hst, f i) : α) = 1 := by
  sorry

@[simp] theorem sum_mul_coe_disjUnion_eq_one_iff [RightDistribClass α] [One α] (a : α)
    {s t : Finset ι} (f : ι → α) (hst : Disjoint s t) :
    (∑ i ∈ s.disjUnion t hst, (f i : WithBotTop α)) * (a : WithBotTop α) = (1 : WithBotTop α) ↔
      ((∑ i ∈ s.disjUnion t hst, f i) * a : α) = 1 := by
  sorry

end Distrib

end WithBotTop
