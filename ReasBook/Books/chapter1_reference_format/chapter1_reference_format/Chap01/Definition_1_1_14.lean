import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {S : Type u} [PartialOrder S]

/- Definition 1.1.14: for a partial order on `S`, the canonical well-order notion is
`IsWellOrder S (· < ·)`; equivalently, every nonempty subset of `S` has a least element. -/
#check IsWellOrder S (· < ·)

/-- Helper for Definition 1.1.14: in a well order, a subset element with no smaller competitor
is automatically a least element of that subset. -/
lemma isLeast_of_no_lt_in_well_order (hwo : IsWellOrder S (· < ·)) {s : Set S} {a : S}
    (ha : a ∈ s) (hminimal : ∀ x ∈ s, ¬ x < a) : IsLeast s a := by
  constructor
  · exact ha
  · intro x hx
    -- Compare `a` and `x`; if `a < x` we are done, and otherwise trichotomy forces equality.
    by_cases hax : a < x
    · exact le_of_lt hax
    · have hEq : a = x := hwo.trichotomous a x hax (hminimal x hx)
      exact hEq.le

/-- Helper for Definition 1.1.14: if every nonempty subset has a least element, then `<` is
well-founded. -/
lemma wellFounded_lt_of_nonempty_subsets_have_least
    (hleast : ∀ s : Set S, s.Nonempty → ∃ a, IsLeast s a) :
    WellFounded ((· < ·) : S → S → Prop) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro s hs
  rcases hleast s hs with ⟨a, ha⟩
  refine ⟨a, ha.1, ?_⟩
  -- A least element cannot have a strictly smaller competitor inside the same set.
  intro x hx
  exact not_lt_of_ge (ha.2 hx)

/-- Helper for Definition 1.1.14: if every nonempty subset has a least element, then `<` is
trichotomous. -/
lemma trichotomous_lt_of_nonempty_subsets_have_least
    (hleast : ∀ s : Set S, s.Nonempty → ∃ a, IsLeast s a) :
    Std.Trichotomous ((· < ·) : S → S → Prop) := by
  refine ⟨fun a b hnotab hnotba => ?_⟩
  have hs : ({a, b} : Set S).Nonempty := by
    exact ⟨a, by simp⟩
  rcases hleast ({a, b} : Set S) hs with ⟨m, hm⟩
  have hmab : m = a ∨ m = b := by
    simpa using hm.1
  rcases hmab with hmEqA | hmEqB
  · subst m
    -- If `a` is least in `{a, b}`, then `a ≤ b`; without `a < b`, equality is forced.
    have hab : a ≤ b := hm.2 (by simp)
    by_contra hEq
    exact hnotab (lt_of_le_of_ne hab hEq)
  · subst m
    -- The symmetric branch gives `b ≤ a`, and the lack of `b < a` again forces equality.
    have hba : b ≤ a := hm.2 (by simp)
    by_contra hEq
    exact hnotba (lt_of_le_of_ne hba (Ne.symm hEq))

/-- Definition 1.1.14: a partial order is a well order exactly when every nonempty subset has a
least element. -/
-- Proof sketch: use trichotomy and well-foundedness of `<` to pass from the canonical
-- `IsWellOrder` relation class to least elements of subsets, and conversely apply the least-element
-- hypothesis to suitable subsets to derive comparability and well-foundedness.
theorem isWellOrder_iff_nonempty_subsets_have_least :
    IsWellOrder S (· < ·) ↔
      ∀ s : Set S, s.Nonempty → ∃ a, IsLeast s a := by
  constructor
  · intro hwo s hs
    -- Start from a minimal element given by well-foundedness, then upgrade it to a least element.
    obtain ⟨a, ha, hminimal⟩ := hwo.wf.has_min s hs
    exact ⟨a, isLeast_of_no_lt_in_well_order hwo ha hminimal⟩
  · intro hleast
    -- Reconstruct the well-order structure by packaging well-foundedness and trichotomy of `<`.
    exact
      IsWellOrder.mk
        (toIsWellFounded := IsWellFounded.mk
          (wellFounded_lt_of_nonempty_subsets_have_least hleast))
        (toTrichotomous := trichotomous_lt_of_nonempty_subsets_have_least hleast)
