module

public import Topology_Munkres_2000.Book.Theorem_8_1.LeastUnused
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.PNat.Interval
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.WellFounded

public section

namespace Lemma8_1

universe u

/-- Helper for Lemma 8.1: a finite family in an infinite subtype omits some value. -/
theorem unusedRange_nonempty (C : Set ℕ+) (hC : C.Infinite) {ι : Type u} [Finite ι]
    (f : ι → C) : (Set.univ \ Set.range f).Nonempty := by
  -- A map from a finite type to the infinite subtype `C` cannot be surjective.
  have hnot : ¬Function.Surjective f :=
    @not_surjective_finite_infinite ι C _ hC.to_subtype f
  -- Rewrite surjectivity as full range to obtain an omitted value.
  simpa [Set.nonempty_def, Set.mem_sdiff, Function.Surjective] using hnot

/-- Helper for Lemma 8.1: restricting a function to indices below `i` has range equal to
its image of `Set.Iio i`. -/
theorem range_restrictIio {ι α : Type*} [Preorder ι] (f : ι → α) (i : ι) :
    Set.range (fun j : Set.Iio i => f j.1) = f '' Set.Iio i := by
  -- Convert witnesses between the subtype range and the set image.
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.2, rfl⟩
  · rintro ⟨j, hji, rfl⟩
    exact ⟨⟨j, hji⟩, rfl⟩

/-- Helper for Lemma 8.1: recursively choose the least value of `C` absent from all
strictly earlier values on `Set.Icc 1 n`. -/
noncomputable def recursiveLeastUnusedOnIcc (C : Set ℕ+) (hC : C.Infinite) (n : ℕ+) :
    Set.Icc 1 n → C :=
  wellFounded_lt.fix fun i previous ↦
    (wellFounded_lt.onFun (f := Subtype.val)).min
      (Set.univ \ Set.range (fun j : Set.Iio i ↦ previous j.1 j.2))
      (unusedRange_nonempty C hC fun j : Set.Iio i ↦ previous j.1 j.2)

/-- Helper for Lemma 8.1: the recursive choice is the least value not used at an earlier
index. -/
theorem recursiveLeastUnusedOnIcc_isLeastAt (C : Set ℕ+) (hC : C.Infinite) (n : ℕ+)
    (i : Set.Icc 1 n) :
    IsLeast (Set.univ \ recursiveLeastUnusedOnIcc C hC n '' Set.Iio i)
      (recursiveLeastUnusedOnIcc C hC n i) := by
  -- Unfold one recursion step and express its finite history as the earlier-value image.
  rw [recursiveLeastUnusedOnIcc, WellFounded.fix_eq]
  rw [← range_restrictIio]
  constructor
  · exact (wellFounded_lt.onFun (f := Subtype.val)).min_mem _ _
  · intro x hx
    -- Well-founded minimality in the inherited linear order gives the lower bound.
    exact le_of_not_gt ((wellFounded_lt.onFun (f := Subtype.val)).not_lt_min _ hx)

end Lemma8_1

/-- Lemma 8.1. Given an infinite set `C` of positive natural numbers and
`n : ℕ+`, there is a function on `Set.Icc 1 n` selecting at each index the
least element of `C` not used at an earlier index. -/
theorem exists_recursiveLeastUnusedOnIcc
    (C : Set ℕ+) (hC : C.Infinite) (n : ℕ+) :
    ∃ f : Set.Icc 1 n → C, f.IsLeastUnused := by
  -- Use the recursive choice and its pointwise least-unused specification.
  refine ⟨Lemma8_1.recursiveLeastUnusedOnIcc C hC n, ?_⟩
  exact Function.IsLeastUnused.of_forall
    (Lemma8_1.recursiveLeastUnusedOnIcc_isLeastAt C hC n)
