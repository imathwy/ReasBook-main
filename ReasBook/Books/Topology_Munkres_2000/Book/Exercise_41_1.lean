module

public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sets.OpenCover

public section

open TopologicalSpace

/-- The nested family of open intervals `(-n, n)` in `ℝ`. -/
def realNestedOpenCover : ℕ → Opens ℝ :=
  fun n ↦ ⟨Set.Ioo (-(n : ℝ)) n, isOpen_Ioo⟩

/- The real line `ℝ` is paracompact. -/
#check (inferInstance : ParacompactSpace ℝ)

/-- The family `realNestedOpenCover` covers `ℝ`. -/
theorem isOpenCover_realNestedOpenCover :
    IsOpenCover realNestedOpenCover := by
  -- Every real number lies in an interval whose natural-number radius exceeds its absolute value.
  apply IsOpenCover.of_sets (fun _ ↦ isOpen_Ioo)
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact ⟨n, abs_lt.mp hn⟩

/-- Helper for Exercise 41.1: the interval `(-n, n)` contains zero exactly when `n` is positive. -/
lemma zero_mem_realNestedOpenCover_iff (n : ℕ) :
    (0 : ℝ) ∈ realNestedOpenCover n ↔ 0 < n := by
  -- Reduce interval membership to the corresponding inequalities between casts.
  simp [realNestedOpenCover]

/-- Helper for Exercise 41.1: every subfamily of the nested intervals covering `ℝ` has
arbitrarily large indices. -/
lemma exists_index_gt_of_realNestedOpenCover_subcover
    (S : Set ℕ) (hS : IsOpenCover (fun n : S ↦ realNestedOpenCover n)) (N : ℕ) :
    ∃ i : S, N < i.1 := by
  -- Cover the point `N`; the upper endpoint inequality forces the chosen index above `N`.
  obtain ⟨i, hi⟩ := hS.exists_mem (N : ℝ)
  refine ⟨i, ?_⟩
  have hiUpper : (N : ℝ) < (i.1 : ℝ) := hi.2
  exact_mod_cast hiUpper

/-- Exercise 41.1. The paracompact space `ℝ` has an open cover with no locally finite
subcollection that still covers `ℝ`. -/
theorem realNestedOpenCover_noLocallyFiniteSubcover
    (S : Set ℕ) (hS : IsOpenCover (fun n : S ↦ realNestedOpenCover n)) :
    ¬ LocallyFinite (fun n : S ↦ (realNestedOpenCover n : Set ℝ)) := by
  intro hloc
  -- Local finiteness makes the subtype indices whose intervals contain zero a finite set.
  have hpoint : {i : S | (0 : ℝ) ∈ realNestedOpenCover i}.Finite := hloc.point_finite 0
  have hvalues : ((fun i : S ↦ i.1) '' {i : S | (0 : ℝ) ∈ realNestedOpenCover i}).Finite :=
    hpoint.image fun i ↦ i.1
  obtain ⟨B, hB⟩ := hvalues.bddAbove
  -- A covering index above this bound is positive, hence its interval contains zero.
  obtain ⟨i, hi⟩ := exists_index_gt_of_realNestedOpenCover_subcover S hS B
  have hiPositive : 0 < i.1 := lt_of_le_of_lt (Nat.zero_le B) hi
  have hiZero : (0 : ℝ) ∈ realNestedOpenCover i :=
    (zero_mem_realNestedOpenCover_iff i.1).2 hiPositive
  have hiImage : i.1 ∈ (fun j : S ↦ j.1) '' {j : S | (0 : ℝ) ∈ realNestedOpenCover j} :=
    ⟨i, hiZero, rfl⟩
  -- The finite-image bound contradicts the strictly larger chosen index.
  exact (not_lt_of_ge (hB hiImage)) hi
