module

public import Topology_Munkres_2000.Book.Theorem_8_4
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Real.Basic

public section

open scoped BigOperators

/-- Exercise 8.2: `positivePartialProduct b n` is the product of the first `n`
terms of the positive-integer-indexed real sequence `b`. -/
def positivePartialProduct (b : ℕ+ → ℝ) (n : ℕ+) : ℝ :=
  ∏ k ∈ Finset.range (n : ℕ), b k.succPNat

/-- The positive partial product through the first term is that term. -/
theorem positivePartialProduct_one (b : ℕ+ → ℝ) :
    positivePartialProduct b 1 = b 1 := by
  -- The range through the first positive index contains only the zeroth natural index.
  rw [positivePartialProduct, PNat.val_ofNat, Finset.prod_range_one]
  rfl

/-- A positive partial product at a successor is the preceding product times
the newly included term. -/
theorem positivePartialProduct_succ (b : ℕ+ → ℝ) (n : ℕ+) :
    positivePartialProduct b (n + 1) = positivePartialProduct b n * b (n + 1) := by
  -- Extend the finite range by its last natural index and translate it back to `ℕ+`.
  rw [positivePartialProduct, positivePartialProduct, PNat.add_one, Nat.succPNat_coe,
    Nat.succ_eq_add_one, Finset.prod_range_succ]

/-- For an index greater than one, the positive partial product is the previous
partial product times the current term. -/
theorem positivePartialProduct_eq_prev_mul (b : ℕ+ → ℝ) (n : ℕ+) (hn : 1 < n) :
    positivePartialProduct b n = positivePartialProduct b (n - 1) * b n := by
  -- Express `n` as the successor of its positive predecessor and use the successor formula.
  simpa only [PNat.sub_add_of_lt hn] using positivePartialProduct_succ b (n - 1)

/-- The history rule used to define positive partial products by the principle
of recursive definition. -/
@[expose]
def positivePartialProductStep (b : ℕ+ → ℝ) {i : ℕ+} (hi : 1 < i)
    (f : Set.Iio i → ℝ) : ℝ :=
  f ⟨i - 1, by
    calc
      i - 1 < i - 1 + 1 := PNat.lt_succ_self _
      _ = i := PNat.sub_add_of_lt hi⟩ * b i

/-- The positive-partial-product history rule evaluates the preceding history
value and multiplies it by the current sequence term. -/
theorem positivePartialProductStep_apply (b : ℕ+ → ℝ) (i : ℕ+) (hi : 1 < i)
    (f : Set.Iio i → ℝ) :
    positivePartialProductStep b hi f =
      f ⟨i - 1, by
        calc
          i - 1 < i - 1 + 1 := PNat.lt_succ_self _
          _ = i := PNat.sub_add_of_lt hi⟩ * b i := rfl

/-- The explicit positive partial product satisfies the recursion prescribed in
Exercise 8.2. -/
theorem positivePartialProduct_isPositiveRecursionFormula (b : ℕ+ → ℝ) :
    (positivePartialProduct b).IsPositiveRecursionFormula (b 1)
      (positivePartialProductStep b) := by
  -- Supply the initial value, then identify every later value with the history rule.
  apply Function.IsPositiveRecursionFormula.mk (positivePartialProduct_one b)
  intro i hi
  rw [positivePartialProduct_eq_prev_mul b i hi]
  rfl

/-- The recursive equations for positive partial products determine a unique
positive-integer-indexed real sequence. -/
theorem existsUnique_positivePartialProduct (b : ℕ+ → ℝ) :
    ∃! h : ℕ+ → ℝ,
      h.IsPositiveRecursionFormula (b 1) (positivePartialProductStep b) := by
  -- Apply the positive-integer recursion theorem to the product history rule.
  exact existsUnique_positiveRecursive ℝ (b 1) (positivePartialProductStep b)
