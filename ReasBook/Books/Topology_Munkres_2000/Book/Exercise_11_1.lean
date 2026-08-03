module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Ring

public section

namespace RationalDifferenceOrder

/-- The strict relation on `ℝ` whose positive differences are rational. -/
def lt (a b : ℝ) : Prop :=
  0 < b - a ∧ b - a ∈ Set.range (fun q : ℚ ↦ (q : ℝ))

scoped[RationalDifferenceOrder] infix:50 " ≺ " => RationalDifferenceOrder.lt

open scoped RationalDifferenceOrder

/-- The defining characterization of the positive-rational-difference order. -/
@[simp] theorem lt_iff (a b : ℝ) :
    a ≺ b ↔ 0 < b - a ∧ b - a ∈ Set.range (fun q : ℚ ↦ (q : ℝ)) := Iff.rfl

/-- The translate of the rational numbers by `a : ℝ`. -/
def translate (a : ℝ) : Set ℝ :=
  Set.range (fun q : ℚ ↦ a + (q : ℝ))

/-- Membership in a rational translate. -/
@[simp] theorem mem_translate (a x : ℝ) :
    x ∈ translate a ↔ ∃ q : ℚ, a + (q : ℝ) = x := Iff.rfl

/-- Helper for Exercise 11.1: comparison is displacement by a positive rational. -/
lemma lt_iff_exists_pos_rat (a b : ℝ) :
    a ≺ b ↔ ∃ q : ℚ, 0 < q ∧ b = a + (q : ℝ) := by
  -- Convert the range witness in the definition into an additive displacement.
  constructor
  · rintro ⟨hpos, q, hq⟩
    refine ⟨q, ?_, ?_⟩
    · rw [← hq] at hpos
      exact (Rat.cast_pos (K := ℝ)).mp hpos
    · calc
        b = a + (b - a) := by ring
        _ = a + (q : ℝ) := by rw [← hq]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, q, ?_⟩
    · simpa only [add_sub_cancel_left] using (Rat.cast_pos (K := ℝ)).mpr hq
    · simp only [add_sub_cancel_left]

/-- Helper for Exercise 11.1: positive rational difference defines a strict partial order on `ℝ`. -/
instance instIsStrictOrder : IsStrictOrder ℝ (· ≺ ·) where
  -- A positive rational displacement cannot return to its starting point.
  irrefl a := by
    rw [lt_iff_exists_pos_rat]
    rintro ⟨q, hq, ha⟩
    have hcast : (q : ℝ) = 0 := by
      apply add_left_cancel (a := a)
      simpa using ha.symm
    have hqreal : (0 : ℝ) < (q : ℝ) := (Rat.cast_pos (K := ℝ)).mpr hq
    exact (lt_irrefl 0) (hcast ▸ hqreal)
  -- Positive rational displacements compose by addition.
  trans a b c hab hbc := by
    rw [lt_iff_exists_pos_rat] at hab hbc ⊢
    rcases hab with ⟨q, hq, rfl⟩
    rcases hbc with ⟨r, hr, rfl⟩
    refine ⟨q + r, add_pos hq hr, ?_⟩
    rw [Rat.cast_add]
    ring

/-- Helper for Exercise 11.1: comparability classes are rational translates. -/
lemma comparable_or_eq_iff_mem_translate (a b : ℝ) :
    (a ≺ b ∨ a = b ∨ b ≺ a) ↔ b ∈ translate a := by
  -- Each comparison direction supplies a rational displacement from `a` to `b`.
  constructor
  · rintro (hab | hab | hba)
    · rcases (lt_iff_exists_pos_rat a b).mp hab with ⟨q, -, rfl⟩
      exact ⟨q, rfl⟩
    · subst b
      exact ⟨0, by simp⟩
    · rcases (lt_iff_exists_pos_rat b a).mp hba with ⟨q, -, hq⟩
      refine ⟨-q, ?_⟩
      change a + ((-q : ℚ) : ℝ) = b
      rw [Rat.cast_neg]
      rw [hq]
      ring
  · rintro ⟨q, hq⟩
    -- The sign of the rational displacement determines the comparison direction.
    rcases (lt_trichotomy q 0) with hneg | hzero | hpos
    · right
      right
      apply (lt_iff_exists_pos_rat b a).mpr
      refine ⟨-q, neg_pos.mpr hneg, ?_⟩
      rw [Rat.cast_neg, ← hq]
      ring
    · right
      left
      subst q
      simpa using hq
    · left
      apply (lt_iff_exists_pos_rat a b).mpr
      exact ⟨q, hpos, hq.symm⟩

/-- Helper for Exercise 11.1: points in one rational translate differ rationally. -/
lemma mem_translate_of_common_base {a x y : ℝ}
    (hx : x ∈ translate a) (hy : y ∈ translate a) : y ∈ translate x := by
  -- Subtract the two rational witnesses to change the base point from `a` to `x`.
  rcases hx with ⟨q, rfl⟩
  rcases hy with ⟨r, rfl⟩
  refine ⟨r - q, ?_⟩
  change a + (q : ℝ) + ((r - q : ℚ) : ℝ) = a + (r : ℝ)
  rw [Rat.cast_sub]
  ring

/-- Every translate of the rational numbers is a maximal simply ordered subset. -/
theorem translate_isMaxChain (a : ℝ) : IsMaxChain (· ≺ ·) (translate a) := by
  -- First, any two distinct points in the translate are comparable.
  have hchain : IsChain (· ≺ ·) (translate a) := by
    intro x hx y hy hxy
    have hyx : y ∈ translate x := mem_translate_of_common_base hx hy
    rcases (comparable_or_eq_iff_mem_translate x y).mpr hyx with hlt | heq | hgt
    · exact Or.inl hlt
    · exact (hxy heq).elim
    · exact Or.inr hgt
  refine ⟨hchain, ?_⟩
  intro s hs hsub
  apply Set.Subset.antisymm hsub
  intro x hx
  -- A larger chain contains `a`, so comparison with `a` forces every point back into its coset.
  have ha_translate : a ∈ translate a := ⟨0, by simp⟩
  have ha : a ∈ s := hsub ha_translate
  by_cases hax : a = x
  · subst x
    exact ha_translate
  · have hcomp := hs ha hx hax
    exact (comparable_or_eq_iff_mem_translate a x).mp
      (hcomp.elim Or.inl (fun h ↦ Or.inr (Or.inr h)))

/-- Exercise 11.1 (2): the maximal simply ordered subsets are exactly the translates
of the rational numbers in `ℝ`. -/
theorem isMaxChain_iff (s : Set ℝ) :
    IsMaxChain (· ≺ ·) s ↔ ∃ a : ℝ, s = translate a := by
  -- Choose a point of the maximal chain and identify the whole chain with its rational coset.
  constructor
  · intro hs
    rcases hs.nonempty_iff.mp inferInstance with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply hs.2 (translate_isMaxChain a).isChain
    intro x hx
    by_cases hax : a = x
    · subst x
      exact ⟨0, by simp⟩
    · have hcomp := hs.isChain ha hx hax
      exact (comparable_or_eq_iff_mem_translate a x).mp
        (hcomp.elim Or.inl (fun h ↦ Or.inr (Or.inr h)))
  · rintro ⟨a, rfl⟩
    exact translate_isMaxChain a

end RationalDifferenceOrder
