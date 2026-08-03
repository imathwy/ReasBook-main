module

public import Topology_Munkres_2000.Book.Definition_4_6
public import Topology_Munkres_2000.Book.Definition_13_3.RealLine
import Mathlib.Topology.Instances.Nat

public section

/-- Example 17.6 (1): The closure of the half-open interval `(0, 1]` in `ℝ` is `[0, 1]`. -/
theorem closure_unitIoc :
    closure (Set.Ioc (0 : ℝ) 1) = Set.Icc 0 1 := by
  -- The endpoints are distinct, so the standard interval-closure formula applies.
  have hzero_ne_one : (0 : ℝ) ≠ 1 := by
    norm_num
  exact closure_Ioc hzero_ne_one

/-- Helper for Example 17.6: adjoining zero to the positive reciprocal sequence gives
the range of reciprocal natural casts. -/
private lemma insert_zero_positiveReciprocals_eq_range_inv_natCast :
    insert 0 RealTopology.positiveReciprocals =
      Set.range (fun n : ℕ ↦ ((n : ℝ)⁻¹)) := by
  -- Membership on either side is split according to whether the natural index is zero.
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · subst x
      refine ⟨0, ?_⟩
      norm_num
    · obtain ⟨n, hn, rfl⟩ :=
        (RealTopology.mem_positiveReciprocals x).mp hx
      refine ⟨n, ?_⟩
      rfl
  · rintro ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst n
      left
      norm_num
    · right
      rw [RealTopology.mem_positiveReciprocals]
      refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
      rfl

/-- Helper for Example 17.6: zero is a limit point of the positive reciprocal sequence. -/
private lemma zero_mem_closure_positiveReciprocals :
    (0 : ℝ) ∈ closure RealTopology.positiveReciprocals := by
  -- Every positive-radius interval about zero contains a sufficiently small reciprocal.
  rw [Real.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨((n + 1 : ℕ) : ℝ)⁻¹, ?_, ?_⟩
  · rw [RealTopology.mem_positiveReciprocals]
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    rfl
  · have hreciprocal_pos : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by
      positivity
    rw [sub_zero, abs_of_pos hreciprocal_pos]
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using hn

/-- Helper for Example 17.6: the positive reciprocal sequence together with zero is closed. -/
private lemma isClosed_insert_zero_positiveReciprocals :
    IsClosed (insert 0 RealTopology.positiveReciprocals) := by
  -- The reciprocal natural-cast sequence converges to its already-present zero value.
  rw [insert_zero_positiveReciprocals_eq_range_inv_natCast]
  have hlimit :
      Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcompact :
      IsCompact (insert 0 (Set.range (fun n : ℕ ↦ ((n : ℝ)⁻¹)))) :=
    hlimit.isCompact_insert_range
  have hzero_mem :
      (0 : ℝ) ∈ Set.range (fun n : ℕ ↦ ((n : ℝ)⁻¹)) := by
    refine ⟨0, ?_⟩
    norm_num
  rw [Set.insert_eq_of_mem hzero_mem] at hcompact
  exact hcompact.isClosed

/-- Companion to Example 17.6 (2): The closure of the positive reciprocal sequence is the sequence
together with its limit point `0`. -/
theorem closure_positiveReciprocals :
    closure RealTopology.positiveReciprocals = insert 0 RealTopology.positiveReciprocals := by
  -- Minimality gives the closed upper bound; zero and the original set give the reverse one.
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.subset_insert 0 RealTopology.positiveReciprocals)
      isClosed_insert_zero_positiveReciprocals
  · intro x hx
    rcases hx with hx | hx
    · subst x
      exact zero_mem_closure_positiveReciprocals
    · exact subset_closure hx

/-- Companion to Example 17.6 (3): The closure of `{0} ∪ (1, 2)` is `{0} ∪ [1, 2]`. -/
theorem closure_zeroUnionIoo :
    closure (insert 0 (Set.Ioo (1 : ℝ) 2)) = insert 0 (Set.Icc 1 2) := by
  -- Closure distributes over the singleton union, and the open interval closes at both ends.
  have hone_ne_two : (1 : ℝ) ≠ 2 := by
    norm_num
  simp only [Set.insert_eq, closure_union, closure_singleton, closure_Ioo hone_ne_two]

/-- Companion to Example 17.6 (4): The closure of `ℚ`, represented as the range of the coercion
`ℚ → ℝ`, is all of `ℝ`. -/
theorem closure_ratCast :
    closure (Set.range (fun q : ℚ ↦ (q : ℝ))) = Set.univ := by
  -- Density of the rational embedding identifies the closure of its range.
  exact Rat.denseRange_cast.closure_range

/-- Helper for Example 17.6: the positive integers are the natural-cast range restricted
to real numbers at least one. -/
private lemma positiveIntegers_eq_natCastRange_inter_Ici :
    ℤ₊ = Set.range (fun n : ℕ ↦ (n : ℝ)) ∩ Set.Ici 1 := by
  -- Replace positive naturals by naturals satisfying the equivalent lower bound.
  rw [Real.positiveIntegers_eq_range_pnatCast]
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨n, ?_⟩
      rfl
    · change (1 : ℝ) ≤ (n : ℝ)
      exact_mod_cast n.property
  · rintro ⟨⟨n, rfl⟩, hn⟩
    change (1 : ℝ) ≤ (n : ℝ) at hn
    have hn_pos : 0 < n := by
      exact_mod_cast hn
    let m : ℕ+ := ⟨n, hn_pos⟩
    refine ⟨m, ?_⟩
    rfl

/-- Companion to Example 17.6 (5): The positive integers, regarded as a subset of `ℝ`,
are closed. -/
theorem closure_positiveIntegers :
    closure ℤ₊ = ℤ₊ := by
  -- The normalized set is an intersection of two closed subsets of the real line.
  rw [positiveIntegers_eq_natCastRange_inter_Ici]
  have hclosed :
      IsClosed (Set.range (fun n : ℕ ↦ (n : ℝ)) ∩ Set.Ici 1) :=
    Nat.isClosedEmbedding_coe_real.isClosed_range.inter isClosed_Ici
  exact hclosed.closure_eq

/-- Companion to Example 17.6 (6): The closure of the positive reals `Set.Ioi 0` is the set
`Set.Ici 0` of nonnegative reals, equivalently the positive reals together with `0`. -/
theorem closure_positiveReals :
    closure (Set.Ioi (0 : ℝ)) = Set.Ici 0 := by
  -- The standard closure formula for an open ray adds precisely its endpoint.
  exact closure_Ioi 0
