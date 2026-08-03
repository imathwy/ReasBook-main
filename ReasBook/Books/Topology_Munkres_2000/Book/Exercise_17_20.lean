module

public import Mathlib.Topology.Closure
public import Mathlib.Topology.Instances.Irrational
public import Mathlib.Topology.Instances.Rat
public import Topology_Munkres_2000.Book.Exercise_17_20.RealPlane

public section

open Set

namespace RealPlane

/-- The open right half-plane with the horizontal axis removed. -/
def puncturedRightHalfPlane : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.2 ≠ 0}

/-- The union of the horizontal axis and the punctured open right half-plane. -/
def xAxisUnionPuncturedRightHalfPlane : Set (ℝ × ℝ) :=
  xAxis ∪ puncturedRightHalfPlane

/-- The points of the real plane whose first coordinate is rational. -/
def rationalFirstCoordinate : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.range (fun q : ℚ ↦ (q : ℝ))}

/-- The region where the difference of the coordinate squares lies in `(0, 1]`. -/
def hyperbolicBand : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ^ 2 - p.2 ^ 2 ∧ p.1 ^ 2 - p.2 ^ 2 ≤ 1}

/-- The points with nonzero first coordinate lying on or below the reciprocal graph. -/
def reciprocalLowerRegion : Set (ℝ × ℝ) :=
  {p | p.1 ≠ 0 ∧ p.2 ≤ 1 / p.1}

/-- Helper for Exercise 17.20: the horizontal axis is a product with a singleton. -/
private lemma xAxis_eq_prod :
    xAxis = Set.univ ×ˢ ({0} : Set ℝ) := by
  -- Compare the two sets through their coordinate membership conditions.
  ext p
  simp only [mem_xAxis_iff, mem_prod, mem_univ, mem_singleton_iff, true_and]

/-- Exercise 17.20 (1): The frontier of the horizontal axis is the axis itself. -/
theorem frontierXAxis :
    frontier xAxis = xAxis := by
  -- The axis is closed, and its interior is empty because the singleton factor has none.
  rw [xAxis_eq_prod]
  have hclosed : IsClosed (Set.univ ×ˢ ({0} : Set ℝ)) :=
    (isClosed_univ : IsClosed (Set.univ : Set ℝ)).prod isClosed_singleton
  have hsingleton : interior ({0} : Set ℝ) = ∅ := interior_singleton (0 : ℝ)
  rw [hclosed.frontier_eq, interior_prod_eq, interior_univ, hsingleton]
  simp only [prod_empty, sdiff_empty]

/-- Companion for Exercise 17.20 (2): The horizontal axis has empty interior. -/
theorem interiorXAxis :
    interior xAxis = ∅ := by
  -- The singleton second-coordinate factor has empty interior.
  have hsingleton : interior ({0} : Set ℝ) = ∅ := interior_singleton (0 : ℝ)
  rw [xAxis_eq_prod, interior_prod_eq, interior_univ, hsingleton, prod_empty]

/-- Helper for Exercise 17.20: the closure of the punctured right half-plane is the
closed right half-plane. -/
private lemma closurePuncturedRightHalfPlane :
    closure puncturedRightHalfPlane = {p : ℝ × ℝ | 0 ≤ p.1} := by
  -- Rewrite as a product and close each coordinate factor separately.
  have hset : puncturedRightHalfPlane = Set.Ioi 0 ×ˢ ({0}ᶜ : Set ℝ) := by
    ext p
    simp only [puncturedRightHalfPlane, mem_setOf_eq, mem_prod, mem_Ioi, mem_compl_iff,
      mem_singleton_iff]
  rw [hset, closure_prod_eq, closure_Ioi, (dense_compl_singleton (0 : ℝ)).closure_eq]
  ext p
  simp only [mem_prod, mem_Ici, mem_univ, and_true, mem_setOf_eq]

/-- Companion for Exercise 17.20 (3): The frontier of the punctured right half-plane consists of
the vertical axis and the positive part of the horizontal axis. -/
theorem frontierPuncturedRightHalfPlane :
    frontier puncturedRightHalfPlane =
      {p | p.1 = 0 ∨ (0 < p.1 ∧ p.2 = 0)} := by
  -- Subtract the open set from its computed closure.
  have hopen : IsOpen puncturedRightHalfPlane := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_compl_singleton.preimage continuous_snd)
  rw [hopen.frontier_eq, closurePuncturedRightHalfPlane]
  ext p
  simp only [mem_sdiff, mem_setOf_eq, puncturedRightHalfPlane, not_and_or, not_lt,
    Classical.not_not]
  constructor
  · intro hp
    rcases hp with ⟨hx, hnot⟩
    by_cases hzero : p.1 = 0
    · exact Or.inl hzero
    · exact Or.inr ⟨lt_of_le_of_ne hx (Ne.symm hzero), hnot.resolve_left (not_le.mpr
        (lt_of_le_of_ne hx (Ne.symm hzero)))⟩
  · intro hp
    rcases hp with hx | ⟨hx, hy⟩
    · exact ⟨hx.ge, Or.inl hx.le⟩
    · exact ⟨hx.le, Or.inr hy⟩

/-- Companion for Exercise 17.20 (4): The punctured right half-plane is open. -/
theorem interiorPuncturedRightHalfPlane :
    interior puncturedRightHalfPlane = puncturedRightHalfPlane := by
  -- Both coordinate conditions define open sets.
  exact ((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_compl_singleton.preimage continuous_snd)).interior_eq

/-- Companion for Exercise 17.20 (5): The frontier of the union consists of the vertical axis and
the negative part of the horizontal axis. -/
theorem frontierXAxisUnionPuncturedRightHalfPlane :
    frontier xAxisUnionPuncturedRightHalfPlane =
      {p | p.1 = 0 ∨ (p.1 < 0 ∧ p.2 = 0)} := by
  -- Compute the closures of the union and its complement, then intersect them.
  have haxisClosed : IsClosed xAxis := by
    rw [xAxis_eq_prod]
    exact isClosed_univ.prod isClosed_singleton
  have hclosure : closure xAxisUnionPuncturedRightHalfPlane =
      {p : ℝ × ℝ | 0 ≤ p.1 ∨ p.2 = 0} := by
    rw [xAxisUnionPuncturedRightHalfPlane, closure_union, haxisClosed.closure_eq,
      closurePuncturedRightHalfPlane]
    ext p
    simp only [mem_union, mem_xAxis_iff, mem_setOf_eq]
    exact or_comm
  have hcompl : xAxisUnionPuncturedRightHalfPlaneᶜ =
      Set.Iic 0 ×ˢ ({0}ᶜ : Set ℝ) := by
    ext p
    simp only [xAxisUnionPuncturedRightHalfPlane, mem_compl_iff, mem_union,
      mem_xAxis_iff, puncturedRightHalfPlane, mem_setOf_eq, mem_prod, mem_Iic,
      mem_compl_iff, mem_singleton_iff]
    constructor
    · intro hp
      have hy : p.2 ≠ 0 := fun hy ↦ hp (Or.inl hy)
      have hx : ¬ 0 < p.1 := fun hx ↦ hp (Or.inr ⟨hx, hy⟩)
      exact ⟨not_lt.mp hx, hy⟩
    · rintro ⟨hx, hy⟩
      intro hp
      rcases hp with hzero | ⟨hpos, _⟩
      · exact hy hzero
      · exact (not_lt_of_ge hx) hpos
  have hclosureCompl : closure xAxisUnionPuncturedRightHalfPlaneᶜ =
      {p : ℝ × ℝ | p.1 ≤ 0} := by
    rw [hcompl, closure_prod_eq, isClosed_Iic.closure_eq,
      (dense_compl_singleton (0 : ℝ)).closure_eq]
    ext p
    simp only [mem_prod, mem_Iic, mem_univ, and_true, mem_setOf_eq]
  rw [frontier_eq_closure_inter_closure, hclosure, hclosureCompl]
  ext p
  simp only [mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hx | hy, hle⟩
    · exact Or.inl (le_antisymm hle hx)
    · by_cases hzero : p.1 = 0
      · exact Or.inl hzero
      · exact Or.inr ⟨lt_of_le_of_ne hle hzero, hy⟩
  · rintro (hzero | ⟨hlt, hy⟩)
    · exact ⟨Or.inl hzero.ge, hzero.le⟩
    · exact ⟨Or.inr hy, hlt.le⟩

/-- Companion for Exercise 17.20 (6): The interior of the union is the open right half-plane. -/
theorem interiorXAxisUnionPuncturedRightHalfPlane :
    interior xAxisUnionPuncturedRightHalfPlane =
      {p | 0 < p.1} := by
  -- The complement is dense in the closed left half-plane, so its closure determines the interior.
  have hcompl : xAxisUnionPuncturedRightHalfPlaneᶜ =
      Set.Iic 0 ×ˢ ({0}ᶜ : Set ℝ) := by
    ext p
    simp only [xAxisUnionPuncturedRightHalfPlane, mem_compl_iff, mem_union,
      mem_xAxis_iff, puncturedRightHalfPlane, mem_setOf_eq, mem_prod, mem_Iic,
      mem_compl_iff, mem_singleton_iff]
    constructor
    · intro hp
      have hy : p.2 ≠ 0 := fun hy ↦ hp (Or.inl hy)
      have hx : ¬ 0 < p.1 := fun hx ↦ hp (Or.inr ⟨hx, hy⟩)
      exact ⟨not_lt.mp hx, hy⟩
    · rintro ⟨hx, hy⟩
      intro hp
      rcases hp with hzero | ⟨hpos, _⟩
      · exact hy hzero
      · exact (not_lt_of_ge hx) hpos
  rw [interior_eq_compl_closure_compl, hcompl, closure_prod_eq,
    isClosed_Iic.closure_eq, (dense_compl_singleton (0 : ℝ)).closure_eq]
  ext p
  simp only [mem_compl_iff, mem_prod, mem_Iic, mem_univ, and_true, mem_setOf_eq,
    not_le]

/-- Companion for Exercise 17.20 (7): The frontier of the points with rational first coordinate is
the entire real plane. -/
theorem frontierRationalFirstCoordinate :
    frontier rationalFirstCoordinate = Set.univ := by
  -- Rational and irrational first coordinates are both dense.
  have hdense : Dense rationalFirstCoordinate := by
    have hrange : Dense (Set.range (fun q : ℚ ↦ (q : ℝ))) := Rat.denseRange_cast
    have hpre : Dense (Prod.fst ⁻¹' Set.range (fun q : ℚ ↦ (q : ℝ))) :=
      hrange.preimage (isOpenMap_fst : IsOpenMap (Prod.fst : ℝ × ℝ → ℝ))
    have hset : rationalFirstCoordinate =
        Prod.fst ⁻¹' Set.range (fun q : ℚ ↦ (q : ℝ)) := by
      ext p
      rfl
    rw [hset]
    exact hpre
  have hdenseCompl : Dense rationalFirstCoordinateᶜ := by
    have hirr : Dense (Prod.fst ⁻¹' {x : ℝ | Irrational x}) :=
      Dense.preimage dense_irrational (isOpenMap_fst : IsOpenMap (Prod.fst : ℝ × ℝ → ℝ))
    have hset : rationalFirstCoordinateᶜ =
        Prod.fst ⁻¹' {x : ℝ | Irrational x} := by
      ext p
      simp only [rationalFirstCoordinate, mem_compl_iff, mem_setOf_eq, mem_preimage,
        Irrational]
    rw [hset]
    exact hirr
  rw [frontier_eq_closure_inter_closure, hdense.closure_eq, hdenseCompl.closure_eq]
  simp only [Set.univ_inter]

/-- Companion for Exercise 17.20 (8): The points with rational first coordinate have
empty interior. -/
theorem interiorRationalFirstCoordinate :
    interior rationalFirstCoordinate = ∅ := by
  -- Density of irrational first coordinates forces empty interior.
  rw [interior_eq_empty_iff_dense_compl]
  have hirr : Dense (Prod.fst ⁻¹' {x : ℝ | Irrational x}) :=
    Dense.preimage dense_irrational (isOpenMap_fst : IsOpenMap (Prod.fst : ℝ × ℝ → ℝ))
  have hset : rationalFirstCoordinateᶜ =
      Prod.fst ⁻¹' {x : ℝ | Irrational x} := by
    ext p
    simp only [rationalFirstCoordinate, mem_compl_iff, mem_setOf_eq, mem_preimage,
      Irrational]
  rw [hset]
  exact hirr

/-- Helper for Exercise 17.20: a point on the quadratic level one is not interior to
the half-open hyperbolic band. -/
private lemma hyperbolicLevelOne_not_mem_interior (p : ℝ × ℝ)
    (hp : p.1 ^ 2 - p.2 ^ 2 = 1) :
    p ∉ interior hyperbolicBand := by
  -- Any interior ball contains a point obtained by moving the first coordinate outward.
  intro hinterior
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hinterior
  have hxne : p.1 ≠ 0 := by
    intro hx
    rw [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at hp
    nlinarith [sq_nonneg p.2]
  rcases lt_or_gt_of_ne hxne with hx | hx
  · let q : ℝ × ℝ := (p.1 - r / 2, p.2)
    have hqball : q ∈ Metric.ball p r := by
      simp only [q, Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
        max_lt_iff]
      constructor
      · rw [show p.1 - r / 2 - p.1 = -(r / 2) by ring, abs_neg]
        rw [abs_of_pos (half_pos hr)]
        linarith
      · exact hr
    have hqmem : q ∈ hyperbolicBand := interior_subset (hball hqball)
    have hupper := hqmem.2
    simp only [q] at hupper
    nlinarith
  · let q : ℝ × ℝ := (p.1 + r / 2, p.2)
    have hqball : q ∈ Metric.ball p r := by
      simp only [q, Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
        max_lt_iff]
      constructor
      · rw [show p.1 + r / 2 - p.1 = r / 2 by ring, abs_of_pos (half_pos hr)]
        linarith
      · exact hr
    have hqmem : q ∈ hyperbolicBand := interior_subset (hball hqball)
    have hupper := hqmem.2
    simp only [q] at hupper
    nlinarith

/-- Helper for Exercise 17.20: every point on the quadratic zero level is approached
by points of the half-open hyperbolic band. -/
private lemma hyperbolicZeroLevel_mem_closure (p : ℝ × ℝ)
    (hp : p.1 ^ 2 - p.2 ^ 2 = 0) :
    p ∈ closure hyperbolicBand := by
  -- Move the first coordinate outward by a small amount controlled by the radius and slope.
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / (2 * |p.1| + 1))
  have hden : 0 < 2 * |p.1| + 1 := by positivity
  have hδ : 0 < δ := by
    exact lt_min (half_pos hε) (one_div_pos.mpr hden)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδden : δ * (2 * |p.1| + 1) ≤ 1 := by
    have hbound : δ ≤ 1 / (2 * |p.1| + 1) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hbound hden.le
    field_simp at hmul
    exact hmul
  have hδone : δ ≤ 1 := by
    nlinarith [abs_nonneg p.1]
  by_cases hx : 0 ≤ p.1
  · let q : ℝ × ℝ := (p.1 + δ, p.2)
    refine ⟨q, ?_, ?_⟩
    · constructor
      · simp only [q]
        nlinarith
      · simp only [q]
        have habs : p.1 ≤ |p.1| := le_abs_self p.1
        nlinarith
    · simp only [q, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, max_lt_iff]
      constructor
      · rw [show p.1 - (p.1 + δ) = -δ by ring, abs_neg, abs_of_pos hδ]
        exact hδε
      · exact hε
  · let q : ℝ × ℝ := (p.1 - δ, p.2)
    refine ⟨q, ?_, ?_⟩
    · constructor
      · simp only [q]
        nlinarith
      · simp only [q]
        have habs : -p.1 ≤ |p.1| := neg_le_abs p.1
        nlinarith
    · simp only [q, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, max_lt_iff]
      constructor
      · rw [show p.1 - (p.1 - δ) = δ by ring, abs_of_pos hδ]
        exact hδε
      · exact hε

/-- Helper for Exercise 17.20: strict quadratic inequalities place a point in the
interior of the hyperbolic band. -/
private lemma hyperbolicStrict_mem_interior (p : ℝ × ℝ)
    (hlower : 0 < p.1 ^ 2 - p.2 ^ 2) (hupper : p.1 ^ 2 - p.2 ^ 2 < 1) :
    p ∈ interior hyperbolicBand := by
  -- The strict band is open and is contained in the half-open band.
  let strictBand : Set (ℝ × ℝ) :=
    {q | 0 < q.1 ^ 2 - q.2 ^ 2 ∧ q.1 ^ 2 - q.2 ^ 2 < 1}
  have hcontinuous : Continuous (fun q : ℝ × ℝ ↦ q.1 ^ 2 - q.2 ^ 2) :=
    (continuous_fst.pow 2).sub (continuous_snd.pow 2)
  have hopen : IsOpen strictBand :=
    (isOpen_lt continuous_const hcontinuous).inter
      (isOpen_lt hcontinuous continuous_const)
  have hsubset : strictBand ⊆ hyperbolicBand := by
    intro q hq
    exact ⟨hq.1, hq.2.le⟩
  exact interior_maximal hsubset hopen ⟨hlower, hupper⟩

/-- Companion for Exercise 17.20 (9): The frontier of the hyperbolic band is the union of its two
level-set boundaries. -/
theorem frontierHyperbolicBand :
    frontier hyperbolicBand =
      {p | p.1 ^ 2 - p.2 ^ 2 = 0 ∨ p.1 ^ 2 - p.2 ^ 2 = 1} := by
  -- Route correction: bound the closure by a closed slab and use local interior certificates,
  -- rather than computing the entire closure by pointwise approximation.
  let closedSlab : Set (ℝ × ℝ) :=
    {p | 0 ≤ p.1 ^ 2 - p.2 ^ 2 ∧ p.1 ^ 2 - p.2 ^ 2 ≤ 1}
  have hcontinuous : Continuous (fun p : ℝ × ℝ ↦ p.1 ^ 2 - p.2 ^ 2) :=
    (continuous_fst.pow 2).sub (continuous_snd.pow 2)
  have hclosed : IsClosed closedSlab :=
    (isClosed_le continuous_const hcontinuous).inter
      (isClosed_le hcontinuous continuous_const)
  have hsubset : hyperbolicBand ⊆ closedSlab := by
    intro p hp
    exact ⟨hp.1.le, hp.2⟩
  have hclosure : closure hyperbolicBand ⊆ closedSlab := closure_minimal hsubset hclosed
  ext p
  simp only [mem_setOf_eq]
  constructor
  · intro hp
    have hpclosure : p ∈ closure hyperbolicBand := frontier_subset_closure hp
    have hpslab : p ∈ closedSlab := hclosure hpclosure
    by_cases hzero : p.1 ^ 2 - p.2 ^ 2 = 0
    · exact Or.inl hzero
    · right
      by_contra hone
      have hlower : 0 < p.1 ^ 2 - p.2 ^ 2 :=
        lt_of_le_of_ne hpslab.1 (Ne.symm hzero)
      have hupper : p.1 ^ 2 - p.2 ^ 2 < 1 := lt_of_le_of_ne hpslab.2 hone
      have hinterior := hyperbolicStrict_mem_interior p hlower hupper
      rw [frontier] at hp
      exact hp.2 hinterior
  · rintro (hzero | hone)
    · rw [frontier]
      refine ⟨hyperbolicZeroLevel_mem_closure p hzero, ?_⟩
      intro hinterior
      have hband : p ∈ hyperbolicBand := interior_subset hinterior
      nlinarith [hband.1]
    · have hband : p ∈ hyperbolicBand := by
        exact ⟨by nlinarith, hone.le⟩
      exact (mem_frontier_iff_notMem_interior hband).2
        (hyperbolicLevelOne_not_mem_interior p hone)

/-- Companion for Exercise 17.20 (10): The interior of the hyperbolic band is obtained by making
both defining inequalities strict. -/
theorem interiorHyperbolicBand :
    interior hyperbolicBand =
      {p | 0 < p.1 ^ 2 - p.2 ^ 2 ∧ p.1 ^ 2 - p.2 ^ 2 < 1} := by
  -- The strict inequalities define an open subset, and level one cannot be interior.
  let strictBand : Set (ℝ × ℝ) :=
    {p | 0 < p.1 ^ 2 - p.2 ^ 2 ∧ p.1 ^ 2 - p.2 ^ 2 < 1}
  have hcontinuous : Continuous (fun p : ℝ × ℝ ↦ p.1 ^ 2 - p.2 ^ 2) :=
    (continuous_fst.pow 2).sub (continuous_snd.pow 2)
  have hopen : IsOpen strictBand := by
    exact (isOpen_lt continuous_const hcontinuous).inter
      (isOpen_lt hcontinuous continuous_const)
  have hsubset : strictBand ⊆ hyperbolicBand := by
    intro p hp
    exact ⟨hp.1, hp.2.le⟩
  apply Set.Subset.antisymm
  · intro p hp
    have hband : p ∈ hyperbolicBand := interior_subset hp
    have hne : p.1 ^ 2 - p.2 ^ 2 ≠ 1 := by
      intro hone
      exact hyperbolicLevelOne_not_mem_interior p hone hp
    exact ⟨hband.1, lt_of_le_of_ne hband.2 hne⟩
  · exact interior_maximal hsubset hopen

/-- Helper for Exercise 17.20: a point on the reciprocal graph is not interior to the
lower reciprocal region. -/
private lemma reciprocalGraph_not_mem_interior (p : ℝ × ℝ) (_hx : p.1 ≠ 0)
    (hy : p.2 = 1 / p.1) :
    p ∉ interior reciprocalLowerRegion := by
  -- Every interior ball contains a point directly above the graph.
  intro hinterior
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hinterior
  let q : ℝ × ℝ := (p.1, p.2 + r / 2)
  have hqball : q ∈ Metric.ball p r := by
    simp only [q, Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero,
      max_lt_iff]
    constructor
    · exact hr
    · rw [show p.2 + r / 2 - p.2 = r / 2 by ring, abs_of_pos (half_pos hr)]
      linarith
  have hqmem : q ∈ reciprocalLowerRegion := interior_subset (hball hqball)
  have hqle := hqmem.2
  simp only [q] at hqle
  linarith

/-- Helper for Exercise 17.20: every point of the vertical axis is approached by
points in the reciprocal lower region. -/
private lemma verticalAxis_mem_closure_reciprocalLowerRegion (y : ℝ) :
    (0, y) ∈ closure reciprocalLowerRegion := by
  -- Approach from the positive side with a first coordinate small enough for both bounds.
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / (|y| + 1))
  have hden : 0 < |y| + 1 := by positivity
  have hδ : 0 < δ := lt_min (half_pos hε) (one_div_pos.mpr hden)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδden : δ * (|y| + 1) ≤ 1 := by
    have hbound : δ ≤ 1 / (|y| + 1) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hbound hden.le
    field_simp at hmul
    exact hmul
  refine ⟨(δ, y), ?_, ?_⟩
  · constructor
    · exact hδ.ne'
    · apply (le_div_iff₀ hδ).2
      have hyabs : y ≤ |y| := le_abs_self y
      nlinarith
  · simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, max_lt_iff]
    constructor
    · rw [zero_sub, abs_neg, abs_of_pos hδ]
      exact hδε
    · exact hε

/-- Helper for Exercise 17.20: a point strictly below the reciprocal graph is interior
to the reciprocal lower region. -/
private lemma reciprocalStrictLower_mem_interior (p : ℝ × ℝ) (hx : p.1 ≠ 0)
    (hy : p.2 < 1 / p.1) :
    p ∈ interior reciprocalLowerRegion := by
  -- Express the strict inequality as the union of its two open polynomial branches.
  let strictLower : Set (ℝ × ℝ) :=
    {q | (0 < q.1 ∧ q.1 * q.2 < 1) ∨ (q.1 < 0 ∧ 1 < q.1 * q.2)}
  have hmul : Continuous (fun q : ℝ × ℝ ↦ q.1 * q.2) :=
    continuous_fst.mul continuous_snd
  have hopen : IsOpen strictLower :=
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt hmul continuous_const)).union
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_const hmul))
  have hsubset : strictLower ⊆ reciprocalLowerRegion := by
    rintro q (⟨hqx, hqxy⟩ | ⟨hqx, hqxy⟩)
    · exact ⟨hqx.ne', (lt_div_iff₀ hqx).2 (by simpa [mul_comm] using hqxy) |>.le⟩
    · exact ⟨hqx.ne, (lt_div_iff_of_neg hqx).2 (by simpa [mul_comm] using hqxy) |>.le⟩
  apply interior_maximal hsubset hopen
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact Or.inr ⟨hneg, by simpa [mul_comm] using (lt_div_iff_of_neg hneg).1 hy⟩
  · exact Or.inl ⟨hpos, by simpa [mul_comm] using (lt_div_iff₀ hpos).1 hy⟩

/-- Helper for Exercise 17.20: a point strictly above the reciprocal graph is interior
to the complement of the reciprocal lower region. -/
private lemma reciprocalStrictUpper_mem_interior_compl (p : ℝ × ℝ) (hx : p.1 ≠ 0)
    (hy : 1 / p.1 < p.2) :
    p ∈ interior reciprocalLowerRegionᶜ := by
  -- Express the upper side as the complementary pair of open polynomial branches.
  let strictUpper : Set (ℝ × ℝ) :=
    {q | (0 < q.1 ∧ 1 < q.1 * q.2) ∨ (q.1 < 0 ∧ q.1 * q.2 < 1)}
  have hmul : Continuous (fun q : ℝ × ℝ ↦ q.1 * q.2) :=
    continuous_fst.mul continuous_snd
  have hopen : IsOpen strictUpper :=
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const hmul)).union
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt hmul continuous_const))
  have hsubset : strictUpper ⊆ reciprocalLowerRegionᶜ := by
    rintro q (⟨hqx, hqxy⟩ | ⟨hqx, hqxy⟩)
    · intro hq
      have hqle := (le_div_iff₀ hqx).1 hq.2
      nlinarith [hqxy]
    · intro hq
      have hqle := (le_div_iff_of_neg hqx).1 hq.2
      nlinarith [hqxy]
  apply interior_maximal hsubset hopen
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact Or.inr ⟨hneg, by simpa [mul_comm] using (div_lt_iff_of_neg hneg).1 hy⟩
  · exact Or.inl ⟨hpos, by simpa [mul_comm] using (div_lt_iff₀ hpos).1 hy⟩

/-- Helper for Exercise 17.20: every nonsingular point off the reciprocal graph lies
in the interior of one of its two sides. -/
private lemma reciprocalOffGraph_mem_interior_or_interior_compl (p : ℝ × ℝ)
    (hx : p.1 ≠ 0) (hy : p.2 ≠ 1 / p.1) :
    p ∈ interior reciprocalLowerRegion ∨ p ∈ interior reciprocalLowerRegionᶜ := by
  -- The strict order trichotomy selects the lower or upper open-side certificate.
  rcases lt_or_gt_of_ne hy with hlower | hupper
  · exact Or.inl (reciprocalStrictLower_mem_interior p hx hlower)
  · exact Or.inr (reciprocalStrictUpper_mem_interior_compl p hx hupper)

/-- Companion for Exercise 17.20 (11): The frontier of the reciprocal lower region is the reciprocal
graph together with the entire vertical axis. -/
theorem frontierReciprocalLowerRegion :
    frontier reciprocalLowerRegion =
      {p | p.1 = 0 ∨ (p.1 ≠ 0 ∧ p.2 = 1 / p.1)} := by
  -- Route correction: isolate the singular axis by approximation and classify every
  -- off-axis, off-graph point into one of the two open sides.
  ext p
  simp only [mem_setOf_eq]
  constructor
  · intro hp
    by_cases hx : p.1 = 0
    · exact Or.inl hx
    · right
      refine ⟨hx, ?_⟩
      by_contra hy
      rcases reciprocalOffGraph_mem_interior_or_interior_compl p hx hy with hlower | hupper
      · rw [frontier] at hp
        exact hp.2 hlower
      · have hpclosure : p ∈ closure reciprocalLowerRegion := frontier_subset_closure hp
        have hpnotclosure : p ∉ closure reciprocalLowerRegion := by
          simpa only [interior_compl, mem_compl_iff] using hupper
        exact hpnotclosure hpclosure
  · rintro (hx | ⟨hx, hy⟩)
    · rw [frontier]
      refine ⟨?_, ?_⟩
      · have hpaxis : p = (0, p.2) := by
          ext
          · exact hx
          · rfl
        rw [hpaxis]
        exact verticalAxis_mem_closure_reciprocalLowerRegion p.2
      · intro hinterior
        have hregion : p ∈ reciprocalLowerRegion := interior_subset hinterior
        exact hregion.1 hx
    · have hregion : p ∈ reciprocalLowerRegion := ⟨hx, hy.le⟩
      exact (mem_frontier_iff_notMem_interior hregion).2
        (reciprocalGraph_not_mem_interior p hx hy)

/-- Companion for Exercise 17.20: the interior of the reciprocal lower region is obtained by
making the vertical inequality strict. -/
theorem interiorReciprocalLowerRegion :
    interior reciprocalLowerRegion =
      {p | p.1 ≠ 0 ∧ p.2 < 1 / p.1} := by
  -- Normalize the strict region into two open polynomial sign branches.
  let strictRegion : Set (ℝ × ℝ) :=
    {p | (0 < p.1 ∧ p.1 * p.2 < 1) ∨ (p.1 < 0 ∧ 1 < p.1 * p.2)}
  have hopen : IsOpen strictRegion := by
    have hmul : Continuous (fun p : ℝ × ℝ ↦ p.1 * p.2) := continuous_fst.mul continuous_snd
    exact ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt hmul continuous_const)).union
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_const hmul))
  have hstrict : strictRegion = {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.2 < 1 / p.1} := by
    ext p
    simp only [strictRegion, mem_setOf_eq]
    constructor
    · rintro (⟨hx, hxy⟩ | ⟨hx, hxy⟩)
      · exact ⟨hx.ne', (lt_div_iff₀ hx).2 (by simpa [mul_comm] using hxy)⟩
      · exact ⟨hx.ne, (lt_div_iff_of_neg hx).2 (by simpa [mul_comm] using hxy)⟩
    · rintro ⟨hxne, hy⟩
      rcases lt_or_gt_of_ne hxne with hx | hx
      · exact Or.inr ⟨hx, by simpa [mul_comm] using (lt_div_iff_of_neg hx).1 hy⟩
      · exact Or.inl ⟨hx, by simpa [mul_comm] using (lt_div_iff₀ hx).1 hy⟩
  have hsubset : strictRegion ⊆ reciprocalLowerRegion := by
    rw [hstrict]
    intro p hp
    exact ⟨hp.1, hp.2.le⟩
  rw [← hstrict]
  apply Set.Subset.antisymm
  · intro p hp
    have hregion : p ∈ reciprocalLowerRegion := interior_subset hp
    have hne : p.2 ≠ 1 / p.1 := by
      intro heq
      exact reciprocalGraph_not_mem_interior p hregion.1 heq hp
    rw [hstrict]
    exact ⟨hregion.1, lt_of_le_of_ne hregion.2 hne⟩
  · exact interior_maximal hsubset hopen

end RealPlane
