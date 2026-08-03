module

public import Topology_Munkres_2000.Book.Theorem_8_1.LeastUnused
public import Topology_Munkres_2000.Book.Theorem_8_4
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.WellFounded

public noncomputable section

/-- Helper for Example 8.1: strict lower intervals of positive natural numbers are finite. -/
instance finiteIioPNat (i : ℕ+) : Finite (Set.Iio i) := by
  -- Embed each positive integer below `i` into the finite type of naturals below `i`.
  let embedding : Set.Iio i → Fin (i : ℕ) := fun x ↦ ⟨x.1, x.2⟩
  apply Finite.of_injective embedding
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Fin.val hxy

/-- Removing the range of a function with finite domain from an infinite subtype
leaves an unused value. -/
theorem unusedRange_nonempty (C : Set ℕ+) (hC : C.Infinite)
    {ι : Type u} [Finite ι] (f : ι → C) :
    (Set.univ \ Set.range f).Nonempty := by
  obtain ⟨x, hxC, hxrange⟩ := (hC.sdiff (Set.finite_range fun i ↦ (f i : ℕ+))).nonempty
  refine ⟨⟨x, hxC⟩, by
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, Set.mem_range]
    rintro ⟨i, hi⟩
    exact hxrange ⟨i, congrArg Subtype.val hi⟩⟩

namespace LeastUnused

/-- The initial value in the least-unused recursion on an infinite set of
positive natural numbers. -/
noncomputable def initial (C : Set ℕ+) (hC : C.Infinite) : C :=
  wellFounded_lt.min Set.univ (@Set.univ_nonempty C hC.nonempty.to_subtype)

/-- The next value in the least-unused recursion is the least value outside the
range of the finite history. -/
noncomputable def next (C : Set ℕ+) (hC : C.Infinite)
    {ι : Type u} [Finite ι] (f : ι → C) : C :=
  wellFounded_lt.min (Set.univ \ Set.range f) (unusedRange_nonempty C hC f)

/-- Helper for Example 8.1: `initial C hC` is the least element of `C`. -/
lemma initial_isLeast (C : Set ℕ+) (hC : C.Infinite) :
    IsLeast Set.univ (initial C hC) := by
  -- Unfold the named minimum and use its membership and lower-bound specifications.
  constructor
  · exact wellFounded_lt.min_mem Set.univ
      (@Set.univ_nonempty C hC.nonempty.to_subtype)
  · intro x hx
    exact wellFounded_lt.min_le hx

/-- Helper for Example 8.1: `next C hC f` is the least value outside the finite range of `f`. -/
lemma next_isLeast (C : Set ℕ+) (hC : C.Infinite)
    {ι : Type u} [Finite ι] (f : ι → C) :
    IsLeast (Set.univ \ Set.range f) (next C hC f) := by
  -- Unfold the named minimum and use its membership and lower-bound specifications.
  constructor
  · exact wellFounded_lt.min_mem (Set.univ \ Set.range f)
      (unusedRange_nonempty C hC f)
  · intro x hx
    exact wellFounded_lt.min_le hx

/-- Example 8.1. The recursion formula using the least element of `C` initially and
the least value outside each finite history is exactly the least-unused property. -/
theorem recursionFormula_iff (C : Set ℕ+) (hC : C.Infinite) (h : ℕ+ → C) :
    h.IsPositiveRecursionFormula (initial C hC) (fun {_} _ f ↦ next C hC f) ↔
      h.IsLeastUnused := by
  constructor
  · intro hrec
    apply Function.IsLeastUnused.of_forall
    intro i
    -- Split an index into the initial case and the genuinely recursive case.
    rcases eq_or_lt_of_le (one_le : (1 : ℕ+) ≤ i) with hi | hi
    · subst i
      rw [hrec.eq_one]
      simpa only [Set.Iio_one_eq_empty, Set.image_empty, Set.sdiff_empty] using
        initial_isLeast C hC
    · rw [hrec.eq_of_one_lt i hi, ← Set.range_restrict]
      exact next_isLeast C hC ((Set.Iio i).restrict h)
  · intro hlu
    apply Function.IsPositiveRecursionFormula.mk
    · -- At `1`, both values are least elements of the same universal set.
      have hinitial : IsLeast (Set.univ \ h '' Set.Iio (1 : ℕ+)) (initial C hC) := by
        simpa only [Set.Iio_one_eq_empty, Set.image_empty, Set.sdiff_empty] using
          initial_isLeast C hC
      exact (hlu.at 1).unique hinitial
    · intro i hi
      -- Normalize the restricted range, then use uniqueness of the least unused value.
      have hnext : IsLeast (Set.univ \ h '' Set.Iio i)
          (next C hC ((Set.Iio i).restrict h)) := by
        rw [← Set.range_restrict]
        exact next_isLeast C hC ((Set.Iio i).restrict h)
      exact (hlu.at i).unique hnext

end LeastUnused

/- Theorem 8.3 is the specialization of the positive-integer
recursion theorem to the least element of `C` and the least element outside the
finite history's range; `LeastUnused.recursionFormula_iff` identifies the
resulting recursion formula with `Function.IsLeastUnused`. -/
#check fun (C : Set ℕ+) (hC : C.Infinite) ↦
  existsUnique_positiveRecursive C (LeastUnused.initial C hC)
    (fun {_} _ f ↦ LeastUnused.next C hC f)

end
