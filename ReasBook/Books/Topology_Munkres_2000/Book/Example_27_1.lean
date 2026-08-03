module

public import Topology_Munkres_2000.Book.Example_24_7.SineCurve
public import Topology_Munkres_2000.Book.Example_23_5.ReciprocalGraph
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.MetricSpace.Bounded

public section

open Set

/- Example 27.1 (1): The unit sphere in `EuclideanSpace ℝ (Fin n)` is compact. -/
#check fun (n : ℕ) ↦
  (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :
    IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))

/- Example 27.1 (2): The closed unit ball in `EuclideanSpace ℝ (Fin n)` is compact. -/
#check fun (n : ℕ) ↦
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :
    IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))

namespace RealPlane

/-- The positive reciprocal graph segment with first coordinate in `(0, 1]`. -/
def reciprocalGraphSegment : Set (ℝ × ℝ) :=
  positiveReciprocalGraph ∩ (Ioc 0 1 ×ˢ univ)

/-- Membership in the positive reciprocal graph segment. -/
theorem mem_reciprocalGraphSegment_iff (p : ℝ × ℝ) :
    p ∈ reciprocalGraphSegment ↔ 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 = 1 / p.1 := by
  simp only [reciprocalGraphSegment, mem_inter_iff, mem_positiveReciprocalGraph,
    mem_prod, mem_Ioc, mem_univ, and_true]
  constructor
  · rintro ⟨⟨hpos, hrecip⟩, _, hle⟩
    exact ⟨hpos, hle, hrecip⟩
  · rintro ⟨hpos, hle, hrecip⟩
    exact ⟨⟨hpos, hrecip⟩, hpos, hle⟩

/-- Helper for Example 27.1: the reciprocal graph segment is a polynomial level set
restricted to a closed interval in the first coordinate. -/
lemma reciprocalGraphSegment_eq_closedLocus :
    reciprocalGraphSegment =
      {p : ℝ × ℝ | p.1 * p.2 = 1 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1} := by
  -- Translate graph membership into an equation without division.
  ext p
  rw [mem_reciprocalGraphSegment_iff]
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨hpos, hle, hrecip⟩
    have hprod : p.1 * p.2 = 1 := by
      rw [hrecip, one_div, mul_inv_cancel₀ hpos.ne']
    exact ⟨hprod, hpos.le, hle⟩
  · rintro ⟨hprod, hnonneg, hle⟩
    have hne : p.1 ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hprod
      norm_num at hprod
    have hpos : 0 < p.1 := lt_of_le_of_ne hnonneg (Ne.symm hne)
    refine ⟨hpos, hle, ?_⟩
    rw [eq_div_iff hne]
    simpa only [mul_comm] using hprod

/-- Example 27.1 (3): The positive reciprocal graph segment is closed in `ℝ × ℝ`. -/
theorem reciprocalGraphSegment_isClosed :
    IsClosed reciprocalGraphSegment := by
  -- Each condition in the closed-locus description is the inverse image of a closed order locus.
  rw [reciprocalGraphSegment_eq_closedLocus]
  have hproduct : IsClosed {p : ℝ × ℝ | p.1 * p.2 = 1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) continuous_const
  have hlower : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hupper : IsClosed {p : ℝ × ℝ | p.1 ≤ 1} :=
    isClosed_le continuous_fst continuous_const
  simpa only [setOf_and] using
    hproduct.inter (hlower.inter hupper)

/-- Helper for Example 27.1: the second coordinates of the reciprocal graph segment
are unbounded above. -/
lemma reciprocalGraphSegment_snd_unboundedAbove (b : ℝ) :
    ∃ p ∈ reciprocalGraphSegment, b < p.2 := by
  -- The point `(1 / (|b| + 1), |b| + 1)` lies on the graph and escapes the bound `b`.
  have hypos : 0 < |b| + 1 := by positivity
  refine ⟨(1 / (|b| + 1), |b| + 1), ?_, ?_⟩
  · rw [mem_reciprocalGraphSegment_iff]
    refine ⟨one_div_pos.mpr hypos, ?_, ?_⟩
    · apply (div_le_iff₀ hypos).2
      linarith [abs_nonneg b]
    · simp only [one_div, inv_inv]
  · linarith [le_abs_self b]

/-- Example 27.1 (4): The positive reciprocal graph segment is not bounded. -/
theorem reciprocalGraphSegment_not_isBounded :
    ¬ Bornology.IsBounded reciprocalGraphSegment := by
  -- A bounded set would give an upper bound for all second coordinates.
  intro hbounded
  obtain ⟨b, hb⟩ := hbounded.image_snd.bddAbove
  obtain ⟨p, hp, hbp⟩ := reciprocalGraphSegment_snd_unboundedAbove b
  exact (not_lt_of_ge (hb ⟨p, hp, rfl⟩)) hbp

/-- Example 27.1 (5): The positive reciprocal graph segment is not compact. -/
theorem reciprocalGraphSegment_not_isCompact :
    ¬ IsCompact reciprocalGraphSegment := by
  intro hcompact
  exact reciprocalGraphSegment_not_isBounded hcompact.isBounded

end RealPlane

namespace TopologistsSineCurve

/-- Helper for Example 27.1: the oscillating sine graph lies in a fixed closed rectangle. -/
lemma curve_subset_closedRectangle :
    curve ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
  -- Read off the first-coordinate bounds from the parameter interval and use the sine bounds.
  rintro p ⟨x, hx, rfl⟩
  exact ⟨⟨hx.1.le, hx.2⟩, Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- Example 27.1 (6): The oscillating sine graph segment is bounded in `ℝ × ℝ`. -/
theorem curve_isBounded :
    Bornology.IsBounded curve := by
  -- Boundedness descends from the product of the two bounded coordinate intervals.
  exact ((Metric.isBounded_Icc (0 : ℝ) 1).prod
    (Metric.isBounded_Icc (-1 : ℝ) 1)).subset curve_subset_closedRectangle

/-- Helper for Example 27.1: the origin is a limit point of the oscillating sine graph. -/
lemma origin_mem_closure_curve :
    ((0, 0) : ℝ × ℝ) ∈ closure curve := by
  -- The closure decomposition contains the entire limiting vertical interval.
  change ((0, 0) : ℝ × ℝ) ∈ carrier
  rw [carrier_eq_curve_union_vertical]
  right
  rw [mem_vertical_iff]
  constructor
  · rfl
  · constructor
    · norm_num
    · norm_num

/-- Example 27.1 (7): The oscillating sine graph segment is not closed in `ℝ × ℝ`. -/
theorem curve_not_isClosed :
    ¬ IsClosed curve := by
  -- Closedness would put the origin on the graph, contradicting positivity of its parameter.
  intro hclosed
  have horigin_curve : ((0, 0) : ℝ × ℝ) ∈ curve :=
    hclosed.closure_subset origin_mem_closure_curve
  rw [curve] at horigin_curve
  obtain ⟨x, hx, hpair⟩ := horigin_curve
  have hxzero : x = 0 := by
    simpa only [Prod.fst] using congrArg Prod.fst hpair
  exact (ne_of_gt hx.1) hxzero

/-- Example 27.1 (8): The oscillating sine graph segment is not compact. -/
theorem curve_not_isCompact :
    ¬ IsCompact curve := by
  intro hcompact
  exact curve_not_isClosed hcompact.isClosed

end TopologistsSineCurve


end
