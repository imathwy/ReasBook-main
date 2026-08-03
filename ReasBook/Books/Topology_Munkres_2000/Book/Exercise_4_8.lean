module

public import Topology_Munkres_2000.Book.Definition_4_5.LinearContinuum
public import Topology_Munkres_2000.Book.Definition_4_6
public import Topology_Munkres_2000.Book.Exercise_4_6.PositivePowers
import Topology_Munkres_2000.Book.Assumption_4_1
import Topology_Munkres_2000.Book.Exercise_3_13

public section

open scoped Real

/-- Part (1) of the exercise: The real numbers have the greatest lower bound property. -/
theorem realGreatestLowerBoundProperty : GreatestLowerBoundProperty ℝ := by
  -- Transfer the least-upper-bound property of `ℝ` to its order-dual completeness statement.
  exact leastUpperBoundProperty_implies_greatestLowerBoundProperty ℝ
    LinearContinuum.leastUpperBoundProperty

/-- Helper for Exercise 4.8: A nonnegative real sequence with arbitrarily small values has
infimum zero. -/
lemma sInf_range_eq_zero_of_nonneg_of_exists_lt {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ f i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ i, f i < ε) :
    sInf (Set.range f) = 0 := by
  -- Use zero as the lower bound, then test every strictly larger candidate by a small value.
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt (Set.range_nonempty f) ?_ ?_
  · intro y hy
    obtain ⟨i, rfl⟩ := hy
    exact hnonneg i
  · intro ε hε
    obtain ⟨i, hi⟩ := hsmall ε hε
    exact ⟨f i, ⟨i, rfl⟩, hi⟩

/-- The reciprocals indexed by the book's subset `ℤ₊` agree with the sequence indexed by `ℕ+`. -/
theorem image_reciprocal_positiveIntegers :
    (fun n : ℝ ↦ 1 / n) '' ℤ₊ = Set.range (fun n : ℕ+ ↦ (1 : ℝ) / (n : ℝ)) := by
  -- Replace the book's positive integers by their canonical positive-natural parametrization.
  rw [Real.positiveIntegers_eq_range_pnatCast]
  exact (Set.range_comp' (fun n : ℝ ↦ 1 / n) fun n : ℕ+ ↦ (n : ℝ)).symm

/-- Helper for Exercise 4.8: Positive-natural reciprocals become smaller than every positive
real number. -/
lemma exists_positiveReciprocal_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ+, (1 : ℝ) / (n : ℝ) < ε := by
  -- Convert the Archimedean witness `n + 1` into a positive natural index.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n.succPNat, ?_⟩
  simpa [Nat.succPNat_coe] using hn

/-- Exercise 4.8(b): The infimum of the reciprocals of the positive integers is zero. -/
theorem sInf_positiveReciprocals :
    sInf ((fun n : ℝ ↦ 1 / n) '' ℤ₊) = 0 := by
  -- Rewrite to a positive-natural range and apply the common infimum criterion.
  rw [image_reciprocal_positiveIntegers]
  refine sInf_range_eq_zero_of_nonneg_of_exists_lt _ ?_ ?_
  · intro n
    positivity
  · exact exists_positiveReciprocal_lt

/-- The positive powers with exponents in the book's subset `ℤ₊` agree with those indexed by
`ℕ+`. -/
theorem image_positivePowers (a : ℝ) :
    (fun n : ℝ ↦ a ^ n) '' ℤ₊ = Set.range (fun n : ℕ+ ↦ a ^ n) := by
  -- Parametrize the source image by `ℕ+`, then identify real and positive-natural powers.
  rw [Real.positiveIntegers_eq_range_pnatCast]
  calc
    (fun n : ℝ ↦ a ^ n) '' Set.range (fun n : ℕ+ ↦ (n : ℝ)) =
        Set.range ((fun n : ℝ ↦ a ^ n) ∘ fun n : ℕ+ ↦ (n : ℝ)) :=
      (Set.range_comp' (fun n : ℝ ↦ a ^ n) fun n : ℕ+ ↦ (n : ℝ)).symm
    _ = Set.range (fun n : ℕ+ ↦ a ^ n) := by
      congr 1
      funext n
      change a ^ ((n : ℕ) : ℝ) = a ^ n
      exact Real.rpow_pnatCast a n

/-- Helper for Exercise 4.8: Powers of a nonnegative real number below one become smaller than
every positive real number. -/
lemma exists_positivePow_lt (a ε : ℝ) (ha : 0 ≤ a) (h_lt_one : a < 1) (hε : 0 < ε) :
    ∃ n : ℕ+, a ^ n < ε := by
  -- Use convergence of the natural powers and choose a successor index for `ℕ+`.
  have hlim : Filter.Tendsto (fun n : ℕ ↦ a ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha h_lt_one
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) ε hε
  refine ⟨N.succPNat, ?_⟩
  rw [Real.positivePow_eq_pow]
  have hdist := hN (N + 1) (Nat.le_succ N)
  rw [Real.dist_eq] at hdist
  simpa [abs_of_nonneg (pow_nonneg ha (N + 1))] using hdist

/-- Exercise 4.8(c): If `0 < a < 1`, then the infimum of the positive powers of `a` is
zero. -/
theorem sInf_positivePowers (a : ℝ) (h_pos : 0 < a) (h_lt_one : a < 1) :
    sInf ((fun n : ℝ ↦ a ^ n) '' ℤ₊) = 0 := by
  -- Rewrite to the geometric sequence and apply nonnegativity plus convergence to zero.
  rw [image_positivePowers]
  refine sInf_range_eq_zero_of_nonneg_of_exists_lt _ ?_ ?_
  · intro n
    rw [Real.positivePow_eq_pow]
    exact pow_nonneg h_pos.le n
  · intro ε hε
    exact exists_positivePow_lt a ε h_pos.le h_lt_one hε
