module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Preorder.Chain

public section

namespace HorizontalOrder

/-- The strict horizontal-line order on the real plane. -/
def lt (p q : ℝ × ℝ) : Prop :=
  p.2 = q.2 ∧ p.1 < q.1

scoped[HorizontalOrder] infix:50 " ≺ " => HorizontalOrder.lt

open scoped HorizontalOrder

/-- The coordinate characterization of the strict horizontal-line order. -/
@[simp] theorem lt_iff (p q : ℝ × ℝ) :
    p ≺ q ↔ p.2 = q.2 ∧ p.1 < q.1 := Iff.rfl

/-- The horizontal line in the real plane at height `y`. -/
def line (y : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 = y}

/-- Membership in a horizontal line is equality of second coordinates. -/
@[simp] theorem mem_line (p : ℝ × ℝ) (y : ℝ) :
    p ∈ line y ↔ p.2 = y := Iff.rfl

/-- The strict horizontal-line relation is a strict partial order. -/
instance instIsStrictOrder : IsStrictOrder (ℝ × ℝ) (· ≺ ·) where
  irrefl p hp := by
    -- A point cannot have a strictly smaller first coordinate than itself.
    exact (lt_irrefl p.1) hp.2
  trans p q r hpq hqr := by
    -- Equal heights and strict first-coordinate inequalities both compose.
    exact ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩

/-- Comparable points under the strict horizontal-line order have equal heights. -/
theorem comparable_sameHeight {p q : ℝ × ℝ} (h : p ≺ q ∨ q ≺ p) :
    p.2 = q.2 := by
  -- Either orientation of comparability records the same horizontal line.
  rcases h with hpq | hqp
  · exact hpq.1
  · exact hqp.1.symm

/-- Helper for Example 11.2: a horizontal-order chain lies in the horizontal line
through any one of its members. -/
lemma IsChain.subset_horizontalLine_of_mem {s : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hs : IsChain (· ≺ ·) s) (hp : p ∈ s) : s ⊆ line p.2 := by
  intro q hq
  -- A distinct member is comparable with the anchor and hence has the same height.
  rw [mem_line]
  by_cases hpq : p = q
  · exact congrArg Prod.snd hpq.symm
  · exact (comparable_sameHeight (hs hp hq hpq)).symm

/-- Every horizontal line is a maximal chain for the strict horizontal-line order. -/
theorem line_isMaxChain (y : ℝ) : IsMaxChain (· ≺ ·) (line y) := by
  constructor
  · intro p hp q hq hpq
    -- Distinct points on one horizontal line have distinct first coordinates.
    rw [mem_line] at hp hq
    have hfirst : p.1 ≠ q.1 := by
      intro hcoordinates
      apply hpq
      apply Prod.ext
      · exact hcoordinates
      · exact hp.trans hq.symm
    -- Linearity of the real first coordinate supplies one comparison direction.
    rcases lt_or_gt_of_ne hfirst with hlt | hgt
    · exact Or.inl ⟨hp.trans hq.symm, hlt⟩
    · exact Or.inr ⟨hq.trans hp.symm, hgt⟩
  · intro t ht hline
    -- Any containing chain includes `(0, y)`, so the chain-height invariant forces equality.
    apply Set.Subset.antisymm hline
    have hanchor : (0, y) ∈ t := hline (mem_line (0, y) y |>.mpr rfl)
    simpa using HorizontalOrder.IsChain.subset_horizontalLine_of_mem ht hanchor

/-- Helper for Example 11.2: the maximal chains for the strict horizontal-line order
are exactly horizontal lines. -/
theorem maximalChains_eq_horizontalLines (s : Set (ℝ × ℝ)) :
    IsMaxChain (· ≺ ·) s ↔ ∃ y : ℝ, s = line y := by
  constructor
  · intro hs
    -- Choose an anchor in the maximal chain and place the whole chain on its line.
    have hsNonempty : s.Nonempty := hs.nonempty_iff.mp inferInstance
    rcases hsNonempty with ⟨p, hp⟩
    refine ⟨p.2, ?_⟩
    exact hs.2 (line_isMaxChain p.2).isChain
      (HorizontalOrder.IsChain.subset_horizontalLine_of_mem hs.isChain hp)
  · rintro ⟨y, rfl⟩
    -- Every horizontal line was proved maximal above.
    exact line_isMaxChain y

end HorizontalOrder
