import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Sets.OpenCover

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

namespace TopologicalSpace.IsOpenCover

/-- Problem 1-4 (1): an open cover in which every member meets only finitely many other members is
locally finite. -/
-- Proof sketch: For any `x`, choose a cover member `U i` containing `x`. Since `U i` is open, it
-- is a neighborhood of `x`, and any `U j` meeting this neighborhood either equals `U i` or is one
-- of the finitely many other members intersecting `U i`.
theorem locallyFinite_of_finite_intersections
    {ι : Type u} {M : Type v} [TopologicalSpace M] {U : ι → Opens M} (hU : IsOpenCover U)
    (hU_finite : ∀ i, {j | j ≠ i ∧ (((U i : Set M) ∩ U j).Nonempty)}.Finite) :
    LocallyFinite (fun i ↦ (U i : Set M)) := by
  intro x
  rcases hU.exists_mem x with ⟨i, hxi⟩
  have hfinite :
      ({i} ∪ {j | j ≠ i ∧ (((U i : Set M) ∩ U j).Nonempty)} : Set ι).Finite :=
    (Set.finite_singleton i).union (hU_finite i)
  refine ⟨U i, (U i).isOpen.mem_nhds hxi, hfinite.subset ?_⟩
  intro j hj
  by_cases hji : j = i
  · exact Or.inl hji
  · exact Or.inr ⟨hji, by simpa [Set.inter_comm] using hj⟩

end TopologicalSpace.IsOpenCover

/-- An explicit open cover of `ℝ` used as the counterexample for Problem 1-4(b). -/
def problem_1_4_counterexample_cover : Option ℕ → Opens ℝ
  | none => ⊤
  | some n => ⟨Set.Ioo (n : ℝ) ((n : ℝ) + 2), isOpen_Ioo⟩

/-- Problem 1-4 (2): (b) the explicit family below is an open cover of `ℝ`. -/
-- Proof sketch: The `none` member is `univ`, so the union is all of `ℝ`; openness is immediate
-- from `isOpen_univ` for `none` and from `isOpen_Ioo` for each interval indexed by `some n`.
theorem problem_1_4_counterexample_isOpenCover :
    IsOpenCover problem_1_4_counterexample_cover := by
  simpa using
    IsOpenCover.of_sets
      (fun i ↦ (problem_1_4_counterexample_cover i).isOpen)
      (Set.iUnion_eq_univ_iff.2 fun x ↦ ⟨none, by simp [problem_1_4_counterexample_cover]⟩)

/-- Helper for Problem 1-4: if the interval indexed by `n` meets the centered neighborhood of
`x`, then `n` lies in a bounded natural interval. -/
lemma some_index_mem_Icc_of_nonempty_inter_centered_interval
    {x : ℝ} {N n : ℕ} (hN : x + 1 < (N : ℝ))
    (hmeet :
      (((problem_1_4_counterexample_cover (some n) : Set ℝ) ∩ Set.Ioo (x - 1) (x + 1)).Nonempty)) :
    n ∈ Set.Icc 0 N := by
  -- Unpack a point in the intersection and compare its coordinates with the interval endpoints.
  rcases hmeet with ⟨y, hyCover, hyCore⟩
  have hn_lt_y : (n : ℝ) < y := by
    simpa [problem_1_4_counterexample_cover] using hyCover.1
  have hy_lt_N : y < (N : ℝ) := lt_trans hyCore.2 hN
  have hn_lt_N : (n : ℝ) < (N : ℝ) := lt_trans hn_lt_y hy_lt_N
  have hn_lt_N_nat : n < N := Nat.cast_lt.mp hn_lt_N
  exact ⟨Nat.zero_le n, Nat.le_of_lt hn_lt_N_nat⟩

/-- Helper for Problem 1-4: the indices whose cover members meet the centered neighborhood of `x`
are contained in a finite bounding family consisting of `none` and bounded `some n`. -/
lemma indices_meeting_centered_interval_subset_bounding_family
    {x : ℝ} {N : ℕ} (hN : x + 1 < (N : ℝ)) :
    {i : Option ℕ |
        (((problem_1_4_counterexample_cover i : Set ℝ) ∩ Set.Ioo (x - 1) (x + 1)).Nonempty)} ⊆
      ({none} ∪ Option.some '' Set.Icc 0 N) := by
  -- Split on the `Option ℕ` index and use the bounded-index lemma in the `some` case.
  intro i hi
  cases i with
  | none =>
      exact Or.inl rfl
  | some n =>
      exact Or.inr ⟨n, some_index_mem_Icc_of_nonempty_inter_centered_interval hN hi, rfl⟩

/-- Helper for Problem 1-4: the `Option ℕ` family obtained from a bounded interval of natural
indices is finite. -/
lemma finite_option_bounding_family (N : ℕ) :
    ({none} ∪ Option.some '' Set.Icc 0 N : Set (Option ℕ)).Finite := by
  -- A singleton union the image of a finite interval is finite.
  exact (Set.finite_singleton none).union ((Set.finite_Icc 0 N).image Option.some)

/-- Problem 1-4 (3): (b) this explicit open cover of `ℝ` is locally finite. -/
-- Proof sketch: Around any point `x`, choose a sufficiently small open interval. It meets the
-- `none` member and only finitely many of the intervals `(n, n + 2)`, because only finitely many
-- natural numbers `n` can lie within bounded distance of `x`.
theorem problem_1_4_counterexample_locallyFinite :
    LocallyFinite (fun i ↦ (problem_1_4_counterexample_cover i : Set ℝ)) := by
  -- Unfold local finiteness and work at an arbitrary point `x`.
  rw [LocallyFinite]
  intro x
  let t : Set ℝ := Set.Ioo (x - 1) (x + 1)
  have hxt : x ∈ t := by
    -- The chosen interval is centered at `x`, so `x` lies strictly between its endpoints.
    simp only [t, Set.mem_Ioo]
    constructor
    · exact sub_lt_self x zero_lt_one
    · exact lt_add_of_pos_right x zero_lt_one
  have ht_mem : t ∈ nhds x := by
    -- The centered interval is an open neighborhood of `x`.
    exact isOpen_Ioo.mem_nhds hxt
  obtain ⟨N, hN⟩ := exists_nat_gt (x + 1)
  refine ⟨t, ht_mem, ?_⟩
  -- Any member meeting `t` lies in the explicit finite bounding family indexed by `N`.
  simpa [t] using
    (finite_option_bounding_family N).subset
      (indices_meeting_centered_interval_subset_bounding_family (x := x) hN)

/-- Problem 1-4 (4): (b) the distinguished member of the explicit cover meets infinitely many other
members. -/
-- Proof sketch: The `none` member is `univ`, so it intersects every nonempty interval indexed by
-- `some n`; these indices form an infinite subset of the set of members meeting `U none`.
theorem problem_1_4_counterexample_none_meets_infinitely_many_others :
    Set.Infinite
      {j : Option ℕ |
        j ≠ none ∧
          ((problem_1_4_counterexample_cover none : Set ℝ) ∩
            problem_1_4_counterexample_cover j).Nonempty} :=
  by
  have hset :
      {j : Option ℕ |
        j ≠ none ∧
          ((problem_1_4_counterexample_cover none : Set ℝ) ∩
            problem_1_4_counterexample_cover j).Nonempty} =
        Set.range (Option.some : ℕ → Option ℕ) := by
    ext j
    cases j with
    | none => simp [problem_1_4_counterexample_cover]
    | some n => simp [problem_1_4_counterexample_cover]
  rw [hset]
  exact Set.infinite_range_of_injective
    (fun m n h ↦ Option.some.inj h : Function.Injective (Option.some : ℕ → Option ℕ))

/-- Problem 1-4 (5): if every member of a locally finite family has compact closure, then each
member meets only finitely many other members. -/
-- Proof sketch: Fix `i`. Since `closure (U i)` is compact and `U` is locally finite, the mathlib
-- compactness lemma gives only finitely many `j` with `U j ∩ closure (U i)` nonempty. Any `j ≠ i`
-- with `U i ∩ U j` nonempty belongs to this finite set by monotonicity.
theorem finite_intersections_of_locallyFinite_of_compact_closure
    {ι : Type u} {M : Type v} [TopologicalSpace M] (U : ι → Set M)
    (hU_compactClosure : ∀ i, IsCompact (closure (U i))) (hU_locallyFinite : LocallyFinite U) :
    ∀ i, {j | j ≠ i ∧ (U i ∩ U j).Nonempty}.Finite := by
  intro i
  refine (hU_locallyFinite.finite_nonempty_inter_compact (hU_compactClosure i)).subset ?_
  rintro j ⟨_, x, hxUi, hxUj⟩
  exact ⟨x, hxUj, subset_closure hxUi⟩
