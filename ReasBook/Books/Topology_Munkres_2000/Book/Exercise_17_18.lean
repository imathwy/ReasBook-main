module

public import Topology_Munkres_2000.Book.Example_16_3.OrderedSquare
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Order.DenselyOrdered

public section

open scoped Topology

namespace LexUnitSquare

/-- Helper for Exercise 17.18: the point of the lexicographic square obtained by clamping two
real coordinates to the unit interval. -/
private noncomputable def clampedLexPoint (x y : ℝ) : LexUnitSquare :=
  toLex (Set.projIcc 0 1 zero_le_one x, Set.projIcc 0 1 zero_le_one y)

/-- Helper for Exercise 17.18: the first coordinate of a clamped point is unchanged when it
already lies in the unit interval. -/
@[simp] private lemma clampedLexPoint_fst {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((ofLex (clampedLexPoint x y)).1 : ℝ) = x := by
  -- The interval projection fixes an in-range coordinate.
  simp [clampedLexPoint, Set.projIcc_of_mem zero_le_one hx]

/-- Helper for Exercise 17.18: the second coordinate of a clamped point is unchanged when it
already lies in the unit interval. -/
@[simp] private lemma clampedLexPoint_snd {x y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ((ofLex (clampedLexPoint x y)).2 : ℝ) = y := by
  -- The interval projection fixes an in-range coordinate.
  simp [clampedLexPoint, Set.projIcc_of_mem zero_le_one hy]

/-- Helper for Exercise 17.18: the exposed first projection on `LexUnitSquare` agrees with the
first projection after applying `ofLex`. -/
private lemma ofLex_fst_coe (p : LexUnitSquare) :
    ((ofLex p).1 : ℝ) = (p.1 : ℝ) := by
  -- Both projections are the same carrier projection through the type synonym.
  rfl

/-- Helper for Exercise 17.18: the exposed second projection on `LexUnitSquare` agrees with the
second projection after applying `ofLex`. -/
private lemma ofLex_snd_coe (p : LexUnitSquare) :
    ((ofLex p).2 : ℝ) = (p.2 : ℝ) := by
  -- Both projections are the same carrier projection through the type synonym.
  rfl

/-- Helper for Exercise 17.18: the closure of the range of a convergent sequence in a Hausdorff
space consists of its range together with its limit. -/
private lemma closureRange_eq_insert_of_tendsto {X : Type*} [TopologicalSpace X] [T2Space X]
    {f : ℕ → X} {x : X} (hf : Filter.Tendsto f Filter.atTop (nhds x)) :
    closure (Set.range f) = insert x (Set.range f) := by
  -- Compactness makes the range together with its limit a closed upper bound.
  apply Set.Subset.antisymm
  · apply closure_minimal
    · exact Set.subset_insert x (Set.range f)
    · exact hf.isCompact_insert_range.isClosed
  -- The original range is contained in its closure, and convergence adds the limit point.
  · intro y hy
    rcases hy with hy | hy
    · rw [hy]
      exact mem_closure_of_tendsto hf (Filter.Eventually.of_forall fun n ↦ ⟨n, rfl⟩)
    · exact subset_closure hy

/-- Helper for Exercise 17.18: the open horizontal slice at height `y`. -/
private def horizontalSlice (y : ℝ) : Set LexUnitSquare :=
  {p | 0 < (p.1 : ℝ) ∧ (p.1 : ℝ) < 1 ∧ (p.2 : ℝ) = y}

/-- Helper for Exercise 17.18: the lower boundary fibers accumulated by an open horizontal
slice. -/
private def lowerHorizontalBoundary : Set LexUnitSquare :=
  {p | 0 < (p.1 : ℝ) ∧ (p.2 : ℝ) = 0}

/-- Helper for Exercise 17.18: the upper boundary fibers accumulated by an open horizontal
slice. -/
private def upperHorizontalBoundary : Set LexUnitSquare :=
  {p | (p.1 : ℝ) < 1 ∧ (p.2 : ℝ) = 1}

/-- Helper for Exercise 17.18: the canonical completion of an open horizontal slice in the
lexicographic square. -/
private def horizontalSliceCompletion (y : ℝ) : Set LexUnitSquare :=
  lowerHorizontalBoundary ∪ horizontalSlice y ∪ upperHorizontalBoundary

/-- Helper for Exercise 17.18: points below the top of the zero fiber are precisely the earlier
points of that fiber. -/
private lemma lt_clampedZeroOne_iff (p : LexUnitSquare) :
    p < clampedLexPoint 0 1 ↔ (p.1 : ℝ) = 0 ∧ (p.2 : ℝ) < 1 := by
  -- Expand lexicographic comparison and exclude a first coordinate below zero.
  rw [Prod.Lex.lt_iff]
  constructor
  · rintro (hp | hp)
    · have hnonneg : 0 ≤ ((ofLex p).1 : ℝ) := (ofLex p).1.property.1
      have hlt : ((ofLex p).1 : ℝ) < ((ofLex (clampedLexPoint 0 1)).1 : ℝ) :=
        Subtype.coe_lt_coe.mpr hp
      rw [clampedLexPoint_fst unitInterval.zero_mem] at hlt
      linarith
    · constructor
      · have heq := congrArg Subtype.val hp.1
        rw [clampedLexPoint_fst unitInterval.zero_mem, ofLex_fst_coe] at heq
        exact heq
      · have hlt : ((ofLex p).2 : ℝ) < ((ofLex (clampedLexPoint 0 1)).2 : ℝ) :=
          Subtype.coe_lt_coe.mpr hp.2
        rw [clampedLexPoint_snd unitInterval.one_mem, ofLex_snd_coe] at hlt
        exact hlt
  · intro hp
    right
    constructor
    · apply Subtype.ext
      rw [clampedLexPoint_fst unitInterval.zero_mem, ofLex_fst_coe]
      exact hp.1
    · apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_snd unitInterval.one_mem, ofLex_snd_coe]
      exact hp.2

/-- Helper for Exercise 17.18: points above the bottom of the one fiber are precisely the later
points of that fiber. -/
private lemma clampedOneZero_lt_iff (p : LexUnitSquare) :
    clampedLexPoint 1 0 < p ↔ (p.1 : ℝ) = 1 ∧ 0 < (p.2 : ℝ) := by
  -- Expand lexicographic comparison and exclude a first coordinate above one.
  rw [Prod.Lex.lt_iff]
  constructor
  · rintro (hp | hp)
    · have hupper : ((ofLex p).1 : ℝ) ≤ 1 := (ofLex p).1.property.2
      have hlt : ((ofLex (clampedLexPoint 1 0)).1 : ℝ) < ((ofLex p).1 : ℝ) :=
        Subtype.coe_lt_coe.mpr hp
      rw [clampedLexPoint_fst unitInterval.one_mem] at hlt
      linarith
    · constructor
      · have heq := congrArg Subtype.val hp.1
        rw [clampedLexPoint_fst unitInterval.one_mem, ofLex_fst_coe] at heq
        exact heq.symm
      · have hlt : ((ofLex (clampedLexPoint 1 0)).2 : ℝ) < ((ofLex p).2 : ℝ) :=
          Subtype.coe_lt_coe.mpr hp.2
        rw [clampedLexPoint_snd unitInterval.zero_mem, ofLex_snd_coe] at hlt
        exact hlt
  · intro hp
    right
    constructor
    · apply Subtype.ext
      rw [clampedLexPoint_fst unitInterval.one_mem, ofLex_fst_coe]
      exact hp.1.symm
    · apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_snd unitInterval.zero_mem, ofLex_snd_coe]
      exact hp.2

/-- Helper for Exercise 17.18: an order interval whose endpoints lie in one vertical fiber is
the corresponding coordinate interval in that fiber. -/
private lemma mem_Ioo_sameFiber_iff {x y z : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) 1) (p : LexUnitSquare) :
    p ∈ Set.Ioo (clampedLexPoint x y) (clampedLexPoint x z) ↔
      (p.1 : ℝ) = x ∧ y < (p.2 : ℝ) ∧ (p.2 : ℝ) < z := by
  -- The two lexicographic inequalities force equality of the first coordinates.
  constructor
  · intro hp
    rcases hp with ⟨hlower, hupper⟩
    rw [Prod.Lex.lt_iff] at hlower hupper
    rcases hlower with hl | hl
    · rcases hupper with hu | hu
      · have hl' : x < ((ofLex p).1 : ℝ) := by
          have h := Subtype.coe_lt_coe.mpr hl
          rwa [clampedLexPoint_fst hx] at h
        have hu' : ((ofLex p).1 : ℝ) < x := by
          have h := Subtype.coe_lt_coe.mpr hu
          rwa [clampedLexPoint_fst hx] at h
        linarith
      · have hl' : x < ((ofLex p).1 : ℝ) := by
          have h := Subtype.coe_lt_coe.mpr hl
          rwa [clampedLexPoint_fst hx] at h
        have hu' := congrArg Subtype.val hu.1
        rw [clampedLexPoint_fst hx] at hu'
        linarith
    · rcases hupper with hu | hu
      · have hl' := congrArg Subtype.val hl.1
        have hu' : ((ofLex p).1 : ℝ) < x := by
          have h := Subtype.coe_lt_coe.mpr hu
          rwa [clampedLexPoint_fst hx] at h
        rw [clampedLexPoint_fst hx] at hl'
        linarith
      · have hfirst := congrArg Subtype.val hl.1
        rw [clampedLexPoint_fst hx, ofLex_fst_coe] at hfirst
        have hl' : y < (p.2 : ℝ) := by
          have h := Subtype.coe_lt_coe.mpr hl.2
          rwa [clampedLexPoint_snd hy, ofLex_snd_coe] at h
        have hu' : (p.2 : ℝ) < z := by
          have h := Subtype.coe_lt_coe.mpr hu.2
          rwa [clampedLexPoint_snd hz, ofLex_snd_coe] at h
        exact ⟨hfirst.symm, hl', hu'⟩
  -- Coordinate equality selects the second clause of both lexicographic comparisons.
  · intro hp
    constructor
    · rw [Prod.Lex.lt_iff]
      right
      constructor
      · apply Subtype.ext
        rw [clampedLexPoint_fst hx, ofLex_fst_coe]
        exact hp.1.symm
      · apply Subtype.coe_lt_coe.mp
        rw [clampedLexPoint_snd hy, ofLex_snd_coe]
        exact hp.2.1
    · rw [Prod.Lex.lt_iff]
      right
      constructor
      · apply Subtype.ext
        rw [clampedLexPoint_fst hx, ofLex_fst_coe]
        exact hp.1
      · apply Subtype.coe_lt_coe.mp
        rw [clampedLexPoint_snd hz, ofLex_snd_coe]
        exact hp.2.2

/-- Helper for Exercise 17.18: the closed order interval from the bottom to the top of one
vertical fiber is the entire fiber. -/
private lemma mem_Icc_fullFiber_iff {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (p : LexUnitSquare) :
    p ∈ Set.Icc (clampedLexPoint x 0) (clampedLexPoint x 1) ↔ (p.1 : ℝ) = x := by
  constructor
  · intro hp
    rcases hp with ⟨hlower, hupper⟩
    rw [Prod.Lex.le_iff] at hlower hupper
    have hlower_real : x ≤ ((ofLex p).1 : ℝ) := by
      rcases hlower with hlower | hlower
      · have h := Subtype.coe_lt_coe.mpr hlower
        rw [clampedLexPoint_fst hx] at h
        exact h.le
      · have h := congrArg Subtype.val hlower.1
        rw [clampedLexPoint_fst hx] at h
        exact h.le
    have hupper_real : ((ofLex p).1 : ℝ) ≤ x := by
      rcases hupper with hupper | hupper
      · have h := Subtype.coe_lt_coe.mpr hupper
        rw [clampedLexPoint_fst hx] at h
        exact h.le
      · have h := congrArg Subtype.val hupper.1
        rw [clampedLexPoint_fst hx] at h
        exact h.le
    rw [← ofLex_fst_coe]
    exact le_antisymm hupper_real hlower_real
  · intro hp
    constructor
    · rw [Prod.Lex.le_iff]
      right
      constructor
      · apply Subtype.ext
        rw [clampedLexPoint_fst hx, ofLex_fst_coe]
        exact hp.symm
      · apply Subtype.coe_le_coe.mp
        rw [clampedLexPoint_snd unitInterval.zero_mem]
        exact (ofLex p).2.property.1
    · rw [Prod.Lex.le_iff]
      right
      constructor
      · apply Subtype.ext
        rw [clampedLexPoint_fst hx, ofLex_fst_coe]
        exact hp
      · apply Subtype.coe_le_coe.mp
        rw [clampedLexPoint_snd unitInterval.one_mem]
        exact (ofLex p).2.property.2

/-- Helper for Exercise 17.18: the canonical completion of a horizontal slice is closed in the
intrinsic order topology. -/
private lemma isClosed_horizontalSliceCompletion {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    @IsClosed LexUnitSquare (Preorder.topology LexUnitSquare) (horizontalSliceCompletion y) := by
  letI : TopologicalSpace LexUnitSquare := Preorder.topology LexUnitSquare
  letI : OrderTopology LexUnitSquare := ⟨rfl⟩
  -- A point outside the completion has an order interval or ray avoiding all three pieces.
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  have hp_not : p ∉ horizontalSliceCompletion y := hp
  have hp_first_mem : (p.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := p.1.property
  by_cases hp_first_zero : (p.1 : ℝ) = 0
  · have hp_second_ne_one : (p.2 : ℝ) ≠ 1 := by
      intro hp_second_one
      apply hp_not
      right
      have hp_first_lt_one : (p.1 : ℝ) < 1 := by linarith [hp_first_mem.2]
      exact ⟨hp_first_lt_one, hp_second_one⟩
    have hp_second_lt_one : (p.2 : ℝ) < 1 :=
      lt_of_le_of_ne p.2.property.2 hp_second_ne_one
    have hp_ray : p < clampedLexPoint 0 1 :=
      (lt_clampedZeroOne_iff p).2 ⟨hp_first_zero, hp_second_lt_one⟩
    apply Filter.mem_of_superset (Iio_mem_nhds hp_ray)
    intro q hq
    have hq_coord := (lt_clampedZeroOne_iff q).1 hq
    rw [Set.mem_compl_iff]
    intro hq_completion
    rcases hq_completion with (hq_lower | hq_slice) | hq_upper
    · linarith [hq_coord.1, hq_lower.1]
    · linarith [hq_coord.1, hq_slice.1]
    · linarith [hq_coord.2, hq_upper.2]
  by_cases hp_first_one : (p.1 : ℝ) = 1
  · have hp_second_ne_zero : (p.2 : ℝ) ≠ 0 := by
      intro hp_second_zero
      apply hp_not
      left
      left
      have hp_first_pos : 0 < (p.1 : ℝ) := by linarith [hp_first_mem.1]
      exact ⟨hp_first_pos, hp_second_zero⟩
    have hp_second_pos : 0 < (p.2 : ℝ) :=
      lt_of_le_of_ne p.2.property.1 hp_second_ne_zero.symm
    have hp_ray : clampedLexPoint 1 0 < p :=
      (clampedOneZero_lt_iff p).2 ⟨hp_first_one, hp_second_pos⟩
    apply Filter.mem_of_superset (Ioi_mem_nhds hp_ray)
    intro q hq
    have hq_coord := (clampedOneZero_lt_iff q).1 hq
    rw [Set.mem_compl_iff]
    intro hq_completion
    rcases hq_completion with (hq_lower | hq_slice) | hq_upper
    · linarith [hq_coord.2, hq_lower.2]
    · linarith [hq_coord.1, hq_slice.2.1]
    · linarith [hq_coord.1, hq_upper.1]
  · have hp_first_pos : 0 < (p.1 : ℝ) :=
      lt_of_le_of_ne hp_first_mem.1 (Ne.symm hp_first_zero)
    have hp_first_lt_one : (p.1 : ℝ) < 1 :=
      lt_of_le_of_ne hp_first_mem.2 hp_first_one
    have hp_second_ne_zero : (p.2 : ℝ) ≠ 0 := by
      intro hp_second_zero
      apply hp_not
      left
      left
      exact ⟨hp_first_pos, hp_second_zero⟩
    have hp_second_ne_one : (p.2 : ℝ) ≠ 1 := by
      intro hp_second_one
      apply hp_not
      right
      exact ⟨hp_first_lt_one, hp_second_one⟩
    have hp_second_ne_y : (p.2 : ℝ) ≠ y := by
      intro hp_second_y
      apply hp_not
      left
      right
      exact ⟨hp_first_pos, hp_first_lt_one, hp_second_y⟩
    have hp_second_pos : 0 < (p.2 : ℝ) :=
      lt_of_le_of_ne p.2.property.1 hp_second_ne_zero.symm
    have hp_second_lt_one : (p.2 : ℝ) < 1 :=
      lt_of_le_of_ne p.2.property.2 hp_second_ne_one
    rcases lt_or_gt_of_ne hp_second_ne_y with hp_below | hp_above
    · have hp_interval :
          p ∈ Set.Ioo (clampedLexPoint (p.1 : ℝ) 0) (clampedLexPoint (p.1 : ℝ) y) :=
        (mem_Ioo_sameFiber_iff hp_first_mem unitInterval.zero_mem hy p).2
          ⟨rfl, hp_second_pos, hp_below⟩
      apply Filter.mem_of_superset (Ioo_mem_nhds hp_interval.1 hp_interval.2)
      intro q hq
      have hq_coord :=
        (mem_Ioo_sameFiber_iff hp_first_mem unitInterval.zero_mem hy q).1 hq
      rw [Set.mem_compl_iff]
      intro hq_completion
      rcases hq_completion with (hq_lower | hq_slice) | hq_upper
      · linarith [hq_coord.2.1, hq_lower.2]
      · linarith [hq_coord.2.2, hq_slice.2.2]
      · linarith [hq_coord.2.2, hy.2, hq_upper.2]
    · have hp_interval :
          p ∈ Set.Ioo (clampedLexPoint (p.1 : ℝ) y) (clampedLexPoint (p.1 : ℝ) 1) :=
        (mem_Ioo_sameFiber_iff hp_first_mem hy unitInterval.one_mem p).2
          ⟨rfl, hp_above, hp_second_lt_one⟩
      apply Filter.mem_of_superset (Ioo_mem_nhds hp_interval.1 hp_interval.2)
      intro q hq
      have hq_coord :=
        (mem_Ioo_sameFiber_iff hp_first_mem hy unitInterval.one_mem q).1 hq
      rw [Set.mem_compl_iff]
      intro hq_completion
      rcases hq_completion with (hq_lower | hq_slice) | hq_upper
      · linarith [hy.1, hq_coord.2.1, hq_lower.2]
      · linarith [hq_coord.2.1, hq_slice.2.2]
      · linarith [hq_coord.2.2, hq_upper.2]

/-- Helper for Exercise 17.18: both one-sided boundary fibers of a horizontal slice belong to
its intrinsic closure. -/
private lemma horizontalSliceBoundary_subset_intrinsicClosure {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    lowerHorizontalBoundary ∪ upperHorizontalBoundary ⊆
      @closure LexUnitSquare (Preorder.topology LexUnitSquare) (horizontalSlice y) := by
  letI : TopologicalSpace LexUnitSquare := Preorder.topology LexUnitSquare
  letI : OrderTopology LexUnitSquare := ⟨rfl⟩
  intro p hp
  rw [mem_closure_iff_nhds]
  intro t ht
  rcases hp with hp_lower | hp_upper
  · have hp_first_mem : (p.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := p.1.property
    have hp_lower_bound : clampedLexPoint 0 1 < p := by
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_fst unitInterval.zero_mem, ofLex_fst_coe]
      exact hp_lower.1
    have hp_upper_bound : p < clampedLexPoint (p.1 : ℝ) 1 := by
      rw [Prod.Lex.lt_iff]
      right
      constructor
      · apply Subtype.ext
        rw [clampedLexPoint_fst hp_first_mem, ofLex_fst_coe]
      · apply Subtype.coe_lt_coe.mp
        rw [clampedLexPoint_snd unitInterval.one_mem, ofLex_snd_coe, hp_lower.2]
        norm_num
    have hp_has_lower : ∃ l, l < p := ⟨clampedLexPoint 0 1, hp_lower_bound⟩
    have hp_has_upper : ∃ u, p < u :=
      ⟨clampedLexPoint (p.1 : ℝ) 1, hp_upper_bound⟩
    rcases (mem_nhds_iff_exists_Ioo_subset' hp_has_lower hp_has_upper).1 ht with
      ⟨l, u, hp_interval, hinterval_sub⟩
    have hl_first : ((ofLex l).1 : ℝ) < (p.1 : ℝ) := by
      have hlp := hp_interval.1
      rw [Prod.Lex.lt_iff] at hlp
      rcases hlp with hlp | hlp
      · have h := Subtype.coe_lt_coe.mpr hlp
        rwa [ofLex_fst_coe] at h
      · have hnonneg : 0 ≤ ((ofLex l).2 : ℝ) := (ofLex l).2.property.1
        have h := Subtype.coe_lt_coe.mpr hlp.2
        have hp_second : ((ofLex p).2 : ℝ) = 0 := (ofLex_snd_coe p).trans hp_lower.2
        rw [hp_second] at h
        linarith
    have hlp_first : (ofLex l).1 < (ofLex p).1 := by
      apply Subtype.coe_lt_coe.mp
      rwa [ofLex_fst_coe, ofLex_fst_coe]
    obtain ⟨z, hlz, hzp⟩ := exists_between hlp_first
    let q : LexUnitSquare := clampedLexPoint (z : ℝ) y
    have hq_first_mem : (z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := z.property
    have hlq : l < q := by
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_fst hq_first_mem]
      exact Subtype.coe_lt_coe.mpr hlz
    have hqp : q < p := by
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_fst hq_first_mem, ofLex_fst_coe]
      exact Subtype.coe_lt_coe.mpr hzp
    have hqt : q ∈ t := hinterval_sub ⟨hlq, hqp.trans hp_interval.2⟩
    have hq_first_pos : 0 < (z : ℝ) := by
      have hl_nonneg : 0 ≤ ((ofLex l).1 : ℝ) := (ofLex l).1.property.1
      have hlz_real := Subtype.coe_lt_coe.mpr hlz
      linarith
    have hq_first_lt_one : (z : ℝ) < 1 := by
      have hzp_real := Subtype.coe_lt_coe.mpr hzp
      rw [ofLex_fst_coe] at hzp_real
      linarith [p.1.property.2]
    refine ⟨q, hqt, ?_⟩
    constructor
    · rw [← ofLex_fst_coe, clampedLexPoint_fst hq_first_mem]
      exact hq_first_pos
    · constructor
      · rw [← ofLex_fst_coe, clampedLexPoint_fst hq_first_mem]
        exact hq_first_lt_one
      · rw [← ofLex_snd_coe, clampedLexPoint_snd hy]
  · have hp_first_mem : (p.1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := p.1.property
    have hp_lower_bound : clampedLexPoint (p.1 : ℝ) 0 < p := by
      rw [Prod.Lex.lt_iff]
      right
      constructor
      · apply Subtype.ext
        rw [clampedLexPoint_fst hp_first_mem, ofLex_fst_coe]
      · apply Subtype.coe_lt_coe.mp
        rw [clampedLexPoint_snd unitInterval.zero_mem, ofLex_snd_coe, hp_upper.2]
        norm_num
    have hp_upper_bound : p < clampedLexPoint 1 0 := by
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_fst unitInterval.one_mem, ofLex_fst_coe]
      exact hp_upper.1
    have hp_has_lower : ∃ l, l < p :=
      ⟨clampedLexPoint (p.1 : ℝ) 0, hp_lower_bound⟩
    have hp_has_upper : ∃ u, p < u := ⟨clampedLexPoint 1 0, hp_upper_bound⟩
    rcases (mem_nhds_iff_exists_Ioo_subset' hp_has_lower hp_has_upper).1 ht with
      ⟨l, u, hp_interval, hinterval_sub⟩
    have hp_first_u : (p.1 : ℝ) < ((ofLex u).1 : ℝ) := by
      have hpu := hp_interval.2
      rw [Prod.Lex.lt_iff] at hpu
      rcases hpu with hpu | hpu
      · have h := Subtype.coe_lt_coe.mpr hpu
        rwa [ofLex_fst_coe] at h
      · have hu_upper : ((ofLex u).2 : ℝ) ≤ 1 := (ofLex u).2.property.2
        have h := Subtype.coe_lt_coe.mpr hpu.2
        rw [ofLex_snd_coe, hp_upper.2] at h
        linarith
    have hp_first_u' : (ofLex p).1 < (ofLex u).1 := by
      apply Subtype.coe_lt_coe.mp
      rwa [ofLex_fst_coe]
    obtain ⟨z, hpz, hzu⟩ := exists_between hp_first_u'
    let q : LexUnitSquare := clampedLexPoint (z : ℝ) y
    have hq_first_mem : (z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := z.property
    have hpq : p < q := by
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_fst hq_first_mem, ofLex_fst_coe]
      exact Subtype.coe_lt_coe.mpr hpz
    have hqu : q < u := by
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_fst hq_first_mem]
      exact Subtype.coe_lt_coe.mpr hzu
    have hqt : q ∈ t := hinterval_sub ⟨hp_interval.1.trans hpq, hqu⟩
    have hq_first_pos : 0 < (z : ℝ) := by
      have hpz_real := Subtype.coe_lt_coe.mpr hpz
      rw [ofLex_fst_coe] at hpz_real
      linarith [p.1.property.1]
    have hq_first_lt_one : (z : ℝ) < 1 := by
      have hu_upper : ((ofLex u).1 : ℝ) ≤ 1 := (ofLex u).1.property.2
      have hzu_real := Subtype.coe_lt_coe.mpr hzu
      linarith
    refine ⟨q, hqt, ?_⟩
    constructor
    · rw [← ofLex_fst_coe, clampedLexPoint_fst hq_first_mem]
      exact hq_first_pos
    · constructor
      · rw [← ofLex_fst_coe, clampedLexPoint_fst hq_first_mem]
        exact hq_first_lt_one
      · rw [← ofLex_snd_coe, clampedLexPoint_snd hy]

/-- Helper for Exercise 17.18: the closure of an open horizontal slice is its canonical
completion by the adjacent bottom and top boundary fibers. -/
private lemma intrinsicClosure_horizontalSlice {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    @closure LexUnitSquare (Preorder.topology LexUnitSquare) (horizontalSlice y) =
      horizontalSliceCompletion y := by
  letI : TopologicalSpace LexUnitSquare := Preorder.topology LexUnitSquare
  -- Closedness gives one inclusion, while the slice and both boundary pieces give the reverse.
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro p hp
      left
      right
      exact hp
    · exact isClosed_horizontalSliceCompletion hy
  · intro p hp
    rcases hp with (hp_lower | hp_slice) | hp_upper
    · exact horizontalSliceBoundary_subset_intrinsicClosure hy (Or.inl hp_lower)
    · exact subset_closure hp_slice
    · exact horizontalSliceBoundary_subset_intrinsicClosure hy (Or.inr hp_upper)

/-- Closure in the intrinsic order topology on the lexicographic unit square. -/
def intrinsicClosure (s : Set LexUnitSquare) : Set LexUnitSquare :=
  closure[Preorder.topology LexUnitSquare] s

/-- Points `(1 / n, 0)` of the ordered square for positive natural numbers `n`. -/
def reciprocalBottom : Set LexUnitSquare :=
  {p | ∃ n : ℕ+, (p.1 : ℝ) = 1 / (n : ℝ) ∧ (p.2 : ℝ) = 0}

/-- Points `(1 - 1 / n, 1 / 2)` of the ordered square for positive natural numbers `n`. -/
def approachingOneMidline : Set LexUnitSquare :=
  {p | ∃ n : ℕ+, (p.1 : ℝ) = 1 - 1 / (n : ℝ) ∧ (p.2 : ℝ) = 1 / 2}

/-- The bottom edge of the ordered square with both horizontal endpoints removed. -/
def openBottomEdge : Set LexUnitSquare :=
  {p | 0 < (p.1 : ℝ) ∧ (p.1 : ℝ) < 1 ∧ (p.2 : ℝ) = 0}

/-- The open horizontal line at second coordinate `1 / 2` in the ordered square. -/
def openHorizontalMidline : Set LexUnitSquare :=
  {p | 0 < (p.1 : ℝ) ∧ (p.1 : ℝ) < 1 ∧ (p.2 : ℝ) = 1 / 2}

/-- The open vertical line at first coordinate `1 / 2` in the ordered square. -/
def openVerticalMidline : Set LexUnitSquare :=
  {p | (p.1 : ℝ) = 1 / 2 ∧ 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}

/-- Exercise 17.18: The first of the five requested closure computations, for the sequence
on the bottom edge; the four remaining computations are the companion theorems below. -/
theorem closureReciprocalBottom :
    intrinsicClosure reciprocalBottom =
      reciprocalBottom ∪ {p | (p.1 : ℝ) = 0 ∧ (p.2 : ℝ) = 1} := by
  letI : TopologicalSpace LexUnitSquare := Preorder.topology LexUnitSquare
  letI : OrderTopology LexUnitSquare := ⟨rfl⟩
  let f : ℕ → LexUnitSquare := fun n ↦ clampedLexPoint (1 / ((n : ℝ) + 1)) 0
  -- Every reciprocal used by the sequence lies in the unit interval.
  have hrecip_mem (n : ℕ) : 1 / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 := by
    have hdenom : 0 ≤ (n : ℝ) + 1 := by positivity
    have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
    exact unitInterval.div_mem zero_le_one hdenom hone
  -- Reindexing positive naturals by successors identifies the source set with this range.
  have hf_range : Set.range f = reciprocalBottom := by
    ext p
    constructor
    · rintro ⟨n, rfl⟩
      have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
      let m : ℕ+ := ⟨n + 1, hnpos⟩
      refine ⟨m, ?_, ?_⟩
      · rw [← ofLex_fst_coe, clampedLexPoint_fst (hrecip_mem n)]
        simp [m]
      · rw [← ofLex_snd_coe, clampedLexPoint_snd unitInterval.zero_mem]
    · rintro ⟨m, hm₁, hm₂⟩
      have hmpos : 0 < m.val := m.property
      have hmpred : m.val - 1 + 1 = m.val := Nat.sub_add_cancel hmpos
      have hmpred_real : ((m.val - 1 : ℕ) : ℝ) + 1 = (m.val : ℝ) := by
        exact_mod_cast hmpred
      refine ⟨m.val - 1, ?_⟩
      apply ofLex.injective
      apply Prod.ext
      · apply Subtype.ext
        rw [clampedLexPoint_fst (hrecip_mem (m.val - 1)), ofLex_fst_coe, hm₁,
          hmpred_real]
      · apply Subtype.ext
        rw [clampedLexPoint_snd unitInterval.zero_mem, ofLex_snd_coe]
        exact hm₂.symm
  -- In lexicographic order the reciprocals converge to the top of the zero fiber.
  have hreal : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hf_tendsto : Filter.Tendsto f Filter.atTop (nhds (clampedLexPoint 0 1)) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have ha_first : ((ofLex a).1 : ℝ) = 0 := by
        have ha' := ha
        rw [Prod.Lex.lt_iff] at ha'
        rcases ha' with ha' | ha'
        · have ha_nonneg : 0 ≤ ((ofLex a).1 : ℝ) := (ofLex a).1.property.1
          have hlt : ((ofLex a).1 : ℝ) < ((ofLex (clampedLexPoint 0 1)).1 : ℝ) :=
            Subtype.coe_lt_coe.mpr ha'
          rw [clampedLexPoint_fst unitInterval.zero_mem] at hlt
          linarith
        · have heq := congrArg Subtype.val ha'.1
          rw [clampedLexPoint_fst unitInterval.zero_mem] at heq
          exact heq
      filter_upwards [] with n
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_fst (hrecip_mem n), ha_first]
      positivity
    · intro a ha
      have ha' : clampedLexPoint 0 1 < a := ha
      have ha_first : 0 < ((ofLex a).1 : ℝ) := by
        rw [Prod.Lex.lt_iff] at ha'
        rcases ha' with ha' | ha'
        · have hlt : ((ofLex (clampedLexPoint 0 1)).1 : ℝ) < ((ofLex a).1 : ℝ) :=
            Subtype.coe_lt_coe.mpr ha'
          rwa [clampedLexPoint_fst unitInterval.zero_mem] at hlt
        · have ha_upper : ((ofLex a).2 : ℝ) ≤ 1 := (ofLex a).2.property.2
          have hlt : ((ofLex (clampedLexPoint 0 1)).2 : ℝ) < ((ofLex a).2 : ℝ) :=
            Subtype.coe_lt_coe.mpr ha'.2
          rw [clampedLexPoint_snd unitInterval.one_mem] at hlt
          linarith
      filter_upwards [(tendsto_order.1 hreal).2 ((ofLex a).1 : ℝ) ha_first] with n hn
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rwa [clampedLexPoint_fst (hrecip_mem n)]
  -- The generic convergent-range formula now leaves only an extensional endpoint rewrite.
  rw [intrinsicClosure, ← hf_range, closureRange_eq_insert_of_tendsto hf_tendsto, hf_range]
  ext p
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (hp | hp)
    · right
      subst p
      constructor
      · rw [← ofLex_fst_coe, clampedLexPoint_fst unitInterval.zero_mem]
      · rw [← ofLex_snd_coe, clampedLexPoint_snd unitInterval.one_mem]
    · exact Or.inl hp
  · rintro (hp | hp)
    · exact Or.inr hp
    · left
      apply ofLex.injective
      apply Prod.ext
      · apply Subtype.ext
        rw [clampedLexPoint_fst unitInterval.zero_mem, ofLex_fst_coe]
        exact hp.1
      · apply Subtype.ext
        rw [clampedLexPoint_snd unitInterval.one_mem, ofLex_snd_coe]
        exact hp.2

/-- Companion for Exercise 17.18 (2): The closure of the sequence approaching the right edge. -/
theorem closureApproachingOneMidline :
    intrinsicClosure approachingOneMidline =
      approachingOneMidline ∪ {p | (p.1 : ℝ) = 1 ∧ (p.2 : ℝ) = 0} := by
  letI : TopologicalSpace LexUnitSquare := Preorder.topology LexUnitSquare
  letI : OrderTopology LexUnitSquare := ⟨rfl⟩
  let f : ℕ → LexUnitSquare := fun n ↦ clampedLexPoint (1 - 1 / ((n : ℝ) + 1)) (1 / 2)
  -- The reciprocal and translated coordinates remain in the unit interval.
  have hrecip_mem (n : ℕ) : 1 / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 := by
    have hdenom : 0 ≤ (n : ℝ) + 1 := by positivity
    have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
    exact unitInterval.div_mem zero_le_one hdenom hone
  have htranslated_mem (n : ℕ) : 1 - 1 / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · linarith [(hrecip_mem n).2]
    · linarith [(hrecip_mem n).1]
  have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  -- Successor reindexing identifies the source positive-natural set with the sequence range.
  have hf_range : Set.range f = approachingOneMidline := by
    ext p
    constructor
    · rintro ⟨n, rfl⟩
      have hnpos : 0 < n + 1 := Nat.zero_lt_succ n
      let m : ℕ+ := ⟨n + 1, hnpos⟩
      refine ⟨m, ?_, ?_⟩
      · rw [← ofLex_fst_coe, clampedLexPoint_fst (htranslated_mem n)]
        simp [m]
      · rw [← ofLex_snd_coe, clampedLexPoint_snd hhalf_mem]
    · rintro ⟨m, hm₁, hm₂⟩
      have hmpos : 0 < m.val := m.property
      have hmpred : m.val - 1 + 1 = m.val := Nat.sub_add_cancel hmpos
      have hmpred_real : ((m.val - 1 : ℕ) : ℝ) + 1 = (m.val : ℝ) := by
        exact_mod_cast hmpred
      refine ⟨m.val - 1, ?_⟩
      apply ofLex.injective
      apply Prod.ext
      · apply Subtype.ext
        rw [clampedLexPoint_fst (htranslated_mem (m.val - 1)), ofLex_fst_coe, hm₁,
          hmpred_real]
      · apply Subtype.ext
        rw [clampedLexPoint_snd hhalf_mem, ofLex_snd_coe]
        exact hm₂.symm
  -- Real convergence of the translated reciprocals gives the lexicographic endpoint limit.
  have hrecip_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htranslated_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ 1 - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hrecip_tendsto
  have hf_tendsto : Filter.Tendsto f Filter.atTop (nhds (clampedLexPoint 1 0)) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have ha' := ha
      have ha_first : ((ofLex a).1 : ℝ) < 1 := by
        rw [Prod.Lex.lt_iff] at ha'
        rcases ha' with ha' | ha'
        · have hlt : ((ofLex a).1 : ℝ) < ((ofLex (clampedLexPoint 1 0)).1 : ℝ) :=
            Subtype.coe_lt_coe.mpr ha'
          rwa [clampedLexPoint_fst unitInterval.one_mem] at hlt
        · have ha_nonneg : 0 ≤ ((ofLex a).2 : ℝ) := (ofLex a).2.property.1
          have hlt : ((ofLex a).2 : ℝ) < ((ofLex (clampedLexPoint 1 0)).2 : ℝ) :=
            Subtype.coe_lt_coe.mpr ha'.2
          rw [clampedLexPoint_snd unitInterval.zero_mem] at hlt
          linarith
      filter_upwards [(tendsto_order.1 htranslated_tendsto).1 ((ofLex a).1 : ℝ) ha_first]
        with n hn
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rwa [clampedLexPoint_fst (htranslated_mem n)]
    · intro a ha
      have ha' : clampedLexPoint 1 0 < a := ha
      have ha_first : (1 : ℝ) ≤ ((ofLex a).1 : ℝ) := by
        rw [Prod.Lex.lt_iff] at ha'
        rcases ha' with ha' | ha'
        · have hlt : ((ofLex (clampedLexPoint 1 0)).1 : ℝ) < ((ofLex a).1 : ℝ) :=
            Subtype.coe_lt_coe.mpr ha'
          rw [clampedLexPoint_fst unitInterval.one_mem] at hlt
          exact hlt.le
        · have heq := congrArg Subtype.val ha'.1
          rw [clampedLexPoint_fst unitInterval.one_mem] at heq
          exact heq.le
      filter_upwards [] with n
      rw [Prod.Lex.lt_iff]
      left
      apply Subtype.coe_lt_coe.mp
      rw [clampedLexPoint_fst (htranslated_mem n)]
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  -- Compactness closes the sequence, after which the endpoint is rewritten coordinatewise.
  rw [intrinsicClosure, ← hf_range, closureRange_eq_insert_of_tendsto hf_tendsto, hf_range]
  ext p
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (hp | hp)
    · right
      subst p
      constructor
      · rw [← ofLex_fst_coe, clampedLexPoint_fst unitInterval.one_mem]
      · rw [← ofLex_snd_coe, clampedLexPoint_snd unitInterval.zero_mem]
    · exact Or.inl hp
  · rintro (hp | hp)
    · exact Or.inr hp
    · left
      apply ofLex.injective
      apply Prod.ext
      · apply Subtype.ext
        rw [clampedLexPoint_fst unitInterval.one_mem, ofLex_fst_coe]
        exact hp.1
      · apply Subtype.ext
        rw [clampedLexPoint_snd unitInterval.zero_mem, ofLex_snd_coe]
        exact hp.2

/-- Companion for Exercise 17.18 (3): The closure of the open bottom edge. -/
theorem closureOpenBottomEdge :
    intrinsicClosure openBottomEdge =
      {p | 0 < (p.1 : ℝ) ∧ (p.2 : ℝ) = 0} ∪
        {p | (p.1 : ℝ) < 1 ∧ (p.2 : ℝ) = 1} := by
  have hedge : openBottomEdge = horizontalSlice 0 := rfl
  -- Specialize the common horizontal formula; the height-zero slice is already lower boundary.
  rw [intrinsicClosure, hedge, intrinsicClosure_horizontalSlice unitInterval.zero_mem]
  ext p
  simp only [horizontalSliceCompletion, lowerHorizontalBoundary, horizontalSlice,
    upperHorizontalBoundary, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ((hp_lower | hp_slice) | hp_upper)
    · exact Or.inl hp_lower
    · exact Or.inl ⟨hp_slice.1, hp_slice.2.2⟩
    · exact Or.inr hp_upper
  · rintro (hp_lower | hp_upper)
    · exact Or.inl (Or.inl hp_lower)
    · exact Or.inr hp_upper

/-- Companion for Exercise 17.18 (4): The closure of the open horizontal midline. -/
theorem closureOpenHorizontalMidline :
    intrinsicClosure openHorizontalMidline =
      {p | 0 < (p.1 : ℝ) ∧ (p.2 : ℝ) = 0} ∪ openHorizontalMidline ∪
        {p | (p.1 : ℝ) < 1 ∧ (p.2 : ℝ) = 1} := by
  have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  have hedge : openHorizontalMidline = horizontalSlice (1 / 2) := rfl
  -- The shared completion formula has exactly the three sets in the claimed union.
  rw [intrinsicClosure, hedge, intrinsicClosure_horizontalSlice hhalf_mem]
  rfl

/-- Companion for Exercise 17.18 (5): The closure of the open vertical midline. -/
theorem closureOpenVerticalMidline :
    intrinsicClosure openVerticalMidline = {p | (p.1 : ℝ) = 1 / 2} := by
  letI : TopologicalSpace LexUnitSquare := Preorder.topology LexUnitSquare
  letI : OrderTopology LexUnitSquare := ⟨rfl⟩
  have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  let a : LexUnitSquare := clampedLexPoint (1 / 2) 0
  let b : LexUnitSquare := clampedLexPoint (1 / 2) 1
  have hab : a ≠ b := by
    intro hab
    have hsnd := congrArg (fun p : LexUnitSquare ↦ ((ofLex p).2 : ℝ)) hab
    rw [clampedLexPoint_snd unitInterval.zero_mem,
      clampedLexPoint_snd unitInterval.one_mem] at hsnd
    norm_num at hsnd
  -- The source line is the open interval inside one fiber.
  have hopen : openVerticalMidline = Set.Ioo a b := by
    ext p
    rw [mem_Ioo_sameFiber_iff hhalf_mem unitInterval.zero_mem unitInterval.one_mem]
    rfl
  -- Its closed interval is exactly the complete vertical fiber.
  have hclosed : Set.Icc a b = {p | (p.1 : ℝ) = 1 / 2} := by
    ext p
    rw [mem_Icc_fullFiber_iff hhalf_mem]
    rfl
  rw [intrinsicClosure, hopen, closure_Ioo hab, hclosed]

end LexUnitSquare
