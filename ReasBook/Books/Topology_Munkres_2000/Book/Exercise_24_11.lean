module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.NumberTheory.Real.Irrational

public section

open Set

/-- Two closed rectangles in `ℝ × ℝ` that meet at a single corner. -/
def tangentRectangles : Set (ℝ × ℝ) :=
  (Icc (-2) 0 ×ˢ Icc (-1) 1) ∪ (Icc 0 2 ×ˢ Icc 1 3)

/-- The set `tangentRectangles` is connected. -/
theorem tangentRectangles_isConnected : IsConnected tangentRectangles := by
  -- Each rectangle is a connected product of closed intervals.
  have hleftFirst : (-2 : ℝ) ≤ 0 := by norm_num
  have hleftSecond : (-1 : ℝ) ≤ 1 := by norm_num
  have hrightFirst : (0 : ℝ) ≤ 2 := by norm_num
  have hrightSecond : (1 : ℝ) ≤ 3 := by norm_num
  have hleft : IsConnected (Icc (-2 : ℝ) 0 ×ˢ Icc (-1 : ℝ) 1) :=
    (isConnected_Icc hleftFirst).prod (isConnected_Icc hleftSecond)
  have hright : IsConnected (Icc (0 : ℝ) 2 ×ˢ Icc (1 : ℝ) 3) :=
    (isConnected_Icc hrightFirst).prod (isConnected_Icc hrightSecond)
  have hintersection :
      ((Icc (-2 : ℝ) 0 ×ˢ Icc (-1 : ℝ) 1) ∩
        (Icc (0 : ℝ) 2 ×ˢ Icc (1 : ℝ) 3)).Nonempty := by
    -- The rectangles meet at their common corner `(0, 1)`.
    refine ⟨(0, 1), ?_⟩
    norm_num
  -- A union of connected sets with nonempty intersection is connected.
  exact IsConnected.union hintersection hleft hright

/-- Helper for Exercise 24.11: an interior point of `tangentRectangles` cannot
have first coordinate zero. -/
lemma tangentRectangles_interior_fst_ne_zero {p : ℝ × ℝ}
    (hp : p ∈ interior tangentRectangles) : p.1 ≠ 0 := by
  intro hpzero
  have hleftClosed : IsClosed (Icc (-2 : ℝ) 0 ×ˢ Icc (-1 : ℝ) 1) :=
    isClosed_Icc.prod isClosed_Icc
  have hrightClosed : IsClosed (Icc (0 : ℝ) 2 ×ˢ Icc (1 : ℝ) 3) :=
    isClosed_Icc.prod isClosed_Icc
  have hleftOrInteriorRight := hleftClosed.interior_union_left hp
  have hinteriorLeftOrRight := hrightClosed.interior_union_right hp
  have hnotInteriorLeft : p ∉ interior (Icc (-2 : ℝ) 0 ×ˢ Icc (-1 : ℝ) 1) := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    simp only [mem_prod, mem_Ioo, hpzero]
    norm_num
  have hnotInteriorRight : p ∉ interior (Icc (0 : ℝ) 2 ×ˢ Icc (1 : ℝ) 3) := by
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    simp only [mem_prod, mem_Ioo, hpzero]
    norm_num
  have hpLeft : p ∈ Icc (-2 : ℝ) 0 ×ˢ Icc (-1 : ℝ) 1 :=
    hleftOrInteriorRight.resolve_right hnotInteriorRight
  have hpRight : p ∈ Icc (0 : ℝ) 2 ×ˢ Icc (1 : ℝ) 3 :=
    hinteriorLeftOrRight.resolve_left hnotInteriorLeft
  have hpsecond : p.2 = 1 := by
    rcases hpLeft with ⟨_, hpLeftSecond⟩
    rcases hpRight with ⟨_, hpRightSecond⟩
    exact le_antisymm hpLeftSecond.2 hpRightSecond.1
  have hnhds : tangentRectangles ∈ nhds p := mem_interior_iff_mem_nhds.mp hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hεhalf : 0 < ε / 2 := half_pos hε
  have hnear : (ε / 2, 1 - ε / 2) ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [hpzero, hpsecond, Real.dist_eq, max_lt_iff]
    constructor
    · rw [abs_lt]
      constructor <;> linarith
    · rw [abs_lt]
      constructor <;> linarith
  have houtside := hball hnear
  -- Moving down and right from the tangent point leaves both rectangles.
  rcases houtside with houtside | houtside
  · exact (not_le_of_gt hεhalf) houtside.1.2
  · linarith [houtside.2.1]

/-- The interior of `tangentRectangles` is not connected. -/
theorem tangentRectangles_interior_not_isConnected :
    ¬ IsConnected (interior tangentRectangles) := by
  intro hconnected
  have hleftPoint : (-1, 0) ∈ interior tangentRectangles := by
    apply subset_interior_union
    left
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    norm_num
  have hrightPoint : (1, 2) ∈ interior tangentRectangles := by
    apply subset_interior_union
    right
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    norm_num
  have hzeroInterval : (0 : ℝ) ∈ Icc ((-1, 0) : ℝ × ℝ).1 ((1, 2) : ℝ × ℝ).1 := by
    norm_num
  -- Connectedness and continuity of the first projection force an interior point
  -- on the vertical axis, contradicting the geometric exclusion lemma.
  have hzeroImage :=
    hconnected.isPreconnected.intermediate_value hleftPoint hrightPoint
      continuous_fst.continuousOn hzeroInterval
  obtain ⟨p, hpInterior, hpFirst⟩ := hzeroImage
  exact tangentRectangles_interior_fst_ne_zero hpInterior hpFirst

/-- First counterexample for Exercise 24.11: a connected set need not have connected interior. -/
theorem connectedDoesNotImplyConnectedInterior :
    ∃ A : Set (ℝ × ℝ), IsConnected A ∧ ¬ IsConnected (interior A) := by
  -- The tangent rectangles provide the required connected witness.
  exact ⟨tangentRectangles, tangentRectangles_isConnected,
    tangentRectangles_interior_not_isConnected⟩

/-- The frontier of the closed unit interval is not connected. -/
theorem unitInterval_frontier_not_isConnected :
    ¬ IsConnected (frontier (Icc (0 : ℝ) 1)) := by
  rw [frontier_Icc zero_le_one]
  intro hconnected
  have hzero : (0 : ℝ) ∈ ({0, 1} : Set ℝ) := by simp
  have hone : (1 : ℝ) ∈ ({0, 1} : Set ℝ) := by simp
  have hhalfInterval : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  -- Order-connectedness would force the midpoint into the two-point frontier.
  have hhalf := hconnected.Icc_subset hzero hone hhalfInterval
  norm_num at hhalf

/-- Second counterexample for Exercise 24.11: a connected set need not have connected frontier. -/
theorem connectedDoesNotImplyConnectedFrontier :
    ∃ A : Set ℝ, IsConnected A ∧ ¬ IsConnected (frontier A) := by
  exact ⟨Icc 0 1, isConnected_Icc zero_le_one, unitInterval_frontier_not_isConnected⟩

/-- The negative ray together with the rational points in `(0, 1]`. -/
def rayWithRationalDust : Set ℝ :=
  Iio 0 ∪ (Set.range ((↑) : ℚ → ℝ) ∩ Ioc 0 1)

/-- Helper for Exercise 24.11: the rational-dust witness has the canonical
interior `Iio 0` and closure `Iic 1`. -/
lemma rayWithRationalDust_normalForms :
    interior rayWithRationalDust = Iio 0 ∧ closure rayWithRationalDust = Iic 1 := by
  have hinterior : interior rayWithRationalDust = Iio 0 := by
    apply Subset.antisymm
    · intro x hxInterior
      have hxSet : x ∈ rayWithRationalDust := interior_subset hxInterior
      by_contra hxNotNegative
      have hxDust : x ∈ Set.range ((↑) : ℚ → ℝ) ∩ Ioc 0 1 := by
        rcases hxSet with hxNegative | hxDust
        · exact False.elim (hxNotNegative hxNegative)
        · exact hxDust
      have hnhds : rayWithRationalDust ∈ nhds x := mem_interior_iff_mem_nhds.mp hxInterior
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
      have hlower : max 0 (x - ε) < x := max_lt hxDust.2.1 (sub_lt_self x hε)
      obtain ⟨y, hyIrrational, hyLower, hyUpper⟩ := exists_irrational_btwn hlower
      have hyPositive : 0 < y := lt_of_le_of_lt (le_max_left 0 (x - ε)) hyLower
      have hyAboveBallLower : x - ε < y :=
        lt_of_le_of_lt (le_max_right 0 (x - ε)) hyLower
      have hyDistance : y ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      have hySet := hball hyDistance
      have hyDust : y ∈ Set.range ((↑) : ℚ → ℝ) ∩ Ioc 0 1 := by
        rcases hySet with hyNegative | hyDust
        · exact False.elim ((not_lt_of_ge hyPositive.le) hyNegative)
        · exact hyDust
      obtain ⟨q, hq⟩ := hyDust.1
      exact hyIrrational.ne_rat q hq.symm
    · -- The negative ray is open and is contained in the witness.
      exact interior_maximal subset_union_left isOpen_Iio
  have hclosure : closure rayWithRationalDust = Iic 1 := by
    have hhalfMem : (1 / 2 : ℝ) ∈ Ioc 0 1 := by norm_num
    have honeMem : (1 : ℝ) ∈ Ioc 0 1 := by norm_num
    have hhalfNeOne : (1 / 2 : ℝ) ≠ 1 := by norm_num
    have hnontrivial : (Ioc (0 : ℝ) 1).Nontrivial :=
      nontrivial_of_mem_mem_ne hhalfMem honeMem hhalfNeOne
    have hzeroNeOne : (0 : ℝ) ≠ 1 := by norm_num
    have hdustClosure :
        closure (Set.range ((↑) : ℚ → ℝ) ∩ Ioc 0 1) = Icc 0 1 := by
      rw [inter_comm, closure_ordConnected_inter_rat ordConnected_Ioc hnontrivial,
        closure_Ioc hzeroNeOne]
    rw [rayWithRationalDust, closure_union, closure_Iio, hdustClosure]
    ext x
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (hx | hx)
      · linarith
      · exact hx.2
    · intro hx
      by_cases hxNonpositive : x ≤ 0
      · exact Or.inl hxNonpositive
      · exact Or.inr ⟨le_of_not_ge hxNonpositive, hx⟩
  exact ⟨hinterior, hclosure⟩

/-- The interior of `rayWithRationalDust` is connected. -/
theorem rayWithRationalDust_interior_isConnected :
    IsConnected (interior rayWithRationalDust) := by
  -- Rewrite the interior to the connected negative ray.
  rw [rayWithRationalDust_normalForms.1]
  exact isConnected_Iio

/-- The frontier of `rayWithRationalDust` is connected. -/
theorem rayWithRationalDust_frontier_isConnected :
    IsConnected (frontier rayWithRationalDust) := by
  have hfrontier : frontier rayWithRationalDust = Icc 0 1 := by
    -- Compute the frontier only from the stable interior and closure normal forms.
    rw [frontier, rayWithRationalDust_normalForms.1, rayWithRationalDust_normalForms.2]
    ext x
    simp only [mem_sdiff, mem_Iic, mem_Iio, mem_Icc, not_lt, and_comm]
  rw [hfrontier]
  exact isConnected_Icc zero_le_one

/-- The set `rayWithRationalDust` is not connected. -/
theorem rayWithRationalDust_not_isConnected :
    ¬ IsConnected rayWithRationalDust := by
  intro hconnected
  have hzeroLtOne : (0 : ℝ) < 1 := by norm_num
  obtain ⟨r, hrIrrational, hrPositive, hrLessOne⟩ := exists_irrational_btwn hzeroLtOne
  have hnegativeOne : (-1 : ℝ) ∈ rayWithRationalDust := by
    left
    norm_num
  have honeRange : (1 : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := by
    refine ⟨1, ?_⟩
    norm_num
  have honeInterval : (1 : ℝ) ∈ Ioc 0 1 := by norm_num
  have hone : (1 : ℝ) ∈ rayWithRationalDust := by
    right
    exact ⟨honeRange, honeInterval⟩
  have hrInterval : r ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  -- Order-connectedness fills the interval between `-1` and `1`.
  have hrSet := hconnected.Icc_subset hnegativeOne hone hrInterval
  have hrDust : r ∈ Set.range ((↑) : ℚ → ℝ) ∩ Ioc 0 1 := by
    rcases hrSet with hrNegative | hrDust
    · exact False.elim ((not_lt_of_ge hrPositive.le) hrNegative)
    · exact hrDust
  obtain ⟨q, hq⟩ := hrDust.1
  exact hrIrrational.ne_rat q hq.symm

/-- Exercise 24.11: Connected interior and connected frontier do not imply
that the original set is connected. -/
theorem connectedInteriorAndFrontierDoNotImplyConnected :
    ∃ A : Set ℝ, IsConnected (interior A) ∧
      IsConnected (frontier A) ∧ ¬ IsConnected A := by
  -- The rational-dust set has both connected derived sets but is disconnected.
  exact ⟨rayWithRationalDust, rayWithRationalDust_interior_isConnected,
    rayWithRationalDust_frontier_isConnected, rayWithRationalDust_not_isConnected⟩
