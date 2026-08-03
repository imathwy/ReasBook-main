module

public import Topology_Munkres_2000.Book.Definition_76_3.Reassembly

public section

namespace CyclicPolygon.EdgeCompression

noncomputable section

/-- Helper for Theorem 77.1: one half belongs to the unit interval. -/
private lemma oneHalf_mem_unitInterval : (1 / 2 : ℝ) ∈ unitInterval := by
  -- Both endpoint inequalities are elementary real arithmetic.
  norm_num [unitInterval]

/-- Helper for Theorem 77.1: the midpoint of the unit interval. -/
private def oneHalf : unitInterval :=
  ⟨1 / 2, oneHalf_mem_unitInterval⟩

/-- Helper for Theorem 77.1: the affine parametrization of the lower half of an edge. -/
def lowerHalfParameter (t : unitInterval) : unitInterval :=
  Set.Icc.convexComb 0 oneHalf t

/-- Helper for Theorem 77.1: the affine parametrization of the upper half of an edge. -/
def upperHalfParameter (t : unitInterval) : unitInterval :=
  Set.Icc.convexComb oneHalf 1 t

/-- Helper for Theorem 77.1: the lower-half parameter has real value `t / 2`. -/
theorem lowerHalfParameter_coe (t : unitInterval) :
    (lowerHalfParameter t : ℝ) = (t : ℝ) / 2 := by
  -- Expand the convex combination and normalize its two fixed endpoints.
  simp only [lowerHalfParameter, Set.Icc.coe_convexComb, oneHalf,
    unitInterval_coe_zero]
  ring

/-- Helper for Theorem 77.1: the upper-half parameter has real value `(1 + t) / 2`. -/
theorem upperHalfParameter_coe (t : unitInterval) :
    (upperHalfParameter t : ℝ) = (1 + (t : ℝ)) / 2 := by
  -- Expand the convex combination and normalize its two fixed endpoints.
  simp only [upperHalfParameter, Set.Icc.coe_convexComb, oneHalf,
    unitInterval_coe_one]
  ring

/-- Helper for Theorem 77.1: lower-half contraction is injective. -/
private lemma lowerHalfParameter_eq_iff (s t : unitInterval) :
    lowerHalfParameter s = lowerHalfParameter t ↔ s = t := by
  -- Equality of real values cancels the common factor one half.
  constructor
  · intro h
    apply Subtype.ext
    have hcoe := congrArg Subtype.val h
    rw [lowerHalfParameter_coe, lowerHalfParameter_coe] at hcoe
    linarith
  · exact congrArg lowerHalfParameter

/-- Helper for Theorem 77.1: upper-half contraction is injective. -/
private lemma upperHalfParameter_eq_iff (s t : unitInterval) :
    upperHalfParameter s = upperHalfParameter t ↔ s = t := by
  -- Equality of real values cancels the common affine shift and factor one half.
  constructor
  · intro h
    apply Subtype.ext
    have hcoe := congrArg Subtype.val h
    rw [upperHalfParameter_coe, upperHalfParameter_coe] at hcoe
    linarith
  · exact congrArg upperHalfParameter

/-- Helper for Theorem 77.1: the lower half starts at parameter zero. -/
private lemma lowerHalfParameter_eq_zero_iff (t : unitInterval) :
    lowerHalfParameter t = 0 ↔ t = 0 := by
  -- Compare real values and use injectivity of division by two.
  constructor
  · intro h
    apply Subtype.ext
    rw [unitInterval_coe_zero]
    have hcoe := congrArg Subtype.val h
    rw [lowerHalfParameter_coe, unitInterval_coe_zero] at hcoe
    norm_num at hcoe
    exact congrArg Subtype.val hcoe
  · rintro rfl
    apply Subtype.ext
    rw [lowerHalfParameter_coe]
    norm_num

/-- Helper for Theorem 77.1: the lower half never reaches parameter one. -/
private lemma lowerHalfParameter_ne_one (t : unitInterval) : lowerHalfParameter t ≠ 1 := by
  -- Its real value is at most one half.
  intro h
  have hcoe := congrArg Subtype.val h
  rw [lowerHalfParameter_coe, unitInterval_coe_one] at hcoe
  linarith [t.property.2]

/-- Helper for Theorem 77.1: the upper half never reaches parameter zero. -/
private lemma upperHalfParameter_ne_zero (t : unitInterval) : upperHalfParameter t ≠ 0 := by
  -- Its real value is at least one half.
  intro h
  have hcoe := congrArg Subtype.val h
  rw [upperHalfParameter_coe, unitInterval_coe_zero] at hcoe
  linarith [t.property.1]

/-- Helper for Theorem 77.1: the upper half ends at parameter one. -/
private lemma upperHalfParameter_eq_one_iff (t : unitInterval) :
    upperHalfParameter t = 1 ↔ t = 1 := by
  -- Compare real values and cancel the affine shift and factor two.
  constructor
  · intro h
    apply Subtype.ext
    rw [unitInterval_coe_one]
    have hcoe := congrArg Subtype.val h
    rw [upperHalfParameter_coe, unitInterval_coe_one] at hcoe
    rw [div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)] at hcoe
    norm_num at hcoe
    linarith
  · rintro rfl
    apply Subtype.ext
    rw [upperHalfParameter_coe]
    norm_num

/-- Helper for Theorem 77.1: the two target half-edges meet only at their midpoint. -/
private lemma lowerHalfParameter_eq_upperHalfParameter_iff (s t : unitInterval) :
    lowerHalfParameter s = upperHalfParameter t ↔ s = 1 ∧ t = 0 := by
  -- The equality forces the maximal lower parameter and minimal upper parameter.
  constructor
  · intro h
    have hcoe := congrArg Subtype.val h
    rw [lowerHalfParameter_coe, upperHalfParameter_coe] at hcoe
    constructor <;> apply Subtype.ext
    · rw [unitInterval_coe_one]
      linarith [s.property.2, t.property.1]
    · rw [unitInterval_coe_zero]
      linarith [s.property.2, t.property.1]
  · rintro ⟨rfl, rfl⟩
    apply Subtype.ext
    rw [lowerHalfParameter_coe, upperHalfParameter_coe]
    norm_num

/-- Helper for Theorem 77.1: the reverse comparison of the two target half-edges
also meets only at their midpoint. -/
private lemma upperHalfParameter_eq_lowerHalfParameter_iff (s t : unitInterval) :
    upperHalfParameter s = lowerHalfParameter t ↔ s = 0 ∧ t = 1 := by
  -- Reverse the preceding midpoint characterization.
  rw [eq_comm, lowerHalfParameter_eq_upperHalfParameter_iff, and_comm]

/-- Helper for Theorem 77.1: the lower-half parametrization is continuous. -/
private lemma continuous_lowerHalfParameter : Continuous lowerHalfParameter := by
  -- This is continuity of a fixed-endpoint convex combination.
  exact Set.Icc.continuous_convexComb 0 oneHalf

/-- Helper for Theorem 77.1: the upper-half parametrization is continuous. -/
private lemma continuous_upperHalfParameter : Continuous upperHalfParameter := by
  -- This is continuity of a fixed-endpoint convex combination.
  exact Set.Icc.continuous_convexComb oneHalf 1

/-- Helper for Theorem 77.1: after subdividing the final target edge, a source edge
is sent either to the equally indexed target edge or to the target's final edge. -/
private def subdivisionIndex (k : ℕ) (i : Fin (k + 2)) : Fin (k + 1) :=
  if hi : i.val < k then ⟨i.val, Nat.lt_succ_of_lt hi⟩ else Fin.last k

/-- Helper for Theorem 77.1: the affine parameter attached to a subdivided source edge. -/
private def subdivisionParameter (k : ℕ) (i : Fin (k + 2))
    (t : unitInterval) : unitInterval :=
  if i.val < k then t
  else if i.val = k then lowerHalfParameter t else upperHalfParameter t

/-- Helper for Theorem 77.1: the common parameter-space map whose final two source
edges traverse the lower and upper halves of the final target edge. -/
private def subdivisionPoint (k : ℕ) (target : CyclicPolygon (k + 1))
    (z : Fin (k + 2) × unitInterval) : target.boundary :=
  target.edgePoint (subdivisionIndex k z.1) (subdivisionParameter k z.1 z.2)

/-- Helper for Theorem 77.1: an edge before the subdivided pair keeps its index. -/
private lemma subdivisionIndex_of_lt {k : ℕ} (i : Fin (k + 2)) (hi : i.val < k) :
    (subdivisionIndex k i).val = i.val := by
  -- Select the unchanged-index branch of the definition.
  simp only [subdivisionIndex, dif_pos hi]

/-- Helper for Theorem 77.1: an edge before the subdivided pair keeps its parameter. -/
private lemma subdivisionParameter_of_lt {k : ℕ} (i : Fin (k + 2))
    (hi : i.val < k) (t : unitInterval) :
    subdivisionParameter k i t = t := by
  -- Select the unchanged-parameter branch of the definition.
  simp only [subdivisionParameter, if_pos hi]

/-- Helper for Theorem 77.1: source edge `k` maps to the final target edge. -/
private lemma subdivisionIndex_of_eq {k : ℕ} (i : Fin (k + 2)) (hi : i.val = k) :
    subdivisionIndex k i = Fin.last k := by
  -- At `k` the unchanged-index test fails, leaving the final target edge.
  have hnot : ¬ i.val < k := by omega
  simp only [subdivisionIndex, dif_neg hnot]

/-- Helper for Theorem 77.1: source edge `k` traverses the lower half of the final edge. -/
private lemma subdivisionParameter_of_eq {k : ℕ} (i : Fin (k + 2))
    (hi : i.val = k) (t : unitInterval) :
    subdivisionParameter k i t = lowerHalfParameter t := by
  -- At `k` the lower-half branch is selected.
  have hnot : ¬ i.val < k := by omega
  simp only [subdivisionParameter, if_neg hnot, if_pos hi]

/-- Helper for Theorem 77.1: source edge `k + 1` maps to the final target edge. -/
private lemma subdivisionIndex_of_eq_succ {k : ℕ} (i : Fin (k + 2))
    (hi : i.val = k + 1) : subdivisionIndex k i = Fin.last k := by
  -- At `k + 1` the unchanged-index test fails, leaving the final target edge.
  have hnot : ¬ i.val < k := by omega
  simp only [subdivisionIndex, dif_neg hnot]

/-- Helper for Theorem 77.1: source edge `k + 1` traverses the upper half of the
final target edge. -/
private lemma subdivisionParameter_of_eq_succ {k : ℕ} (i : Fin (k + 2))
    (hi : i.val = k + 1) (t : unitInterval) :
    subdivisionParameter k i t = upperHalfParameter t := by
  -- At `k + 1` the upper-half branch is selected.
  have hnotLt : ¬ i.val < k := by omega
  have hnotEq : i.val ≠ k := by omega
  simp only [subdivisionParameter, if_neg hnotLt, if_neg hnotEq]

/-- Helper for Theorem 77.1: every source edge is in exactly one of the unchanged,
lower-half, or upper-half index ranges. -/
private lemma subdivisionIndex_trichotomy {k : ℕ} (i : Fin (k + 2)) :
    i.val < k ∨ i.val = k ∨ i.val = k + 1 := by
  -- The source index is strictly below `k + 2`.
  omega

/-- Helper for Theorem 77.1: the subdivision parameter-space map is continuous. -/
private lemma continuous_subdivisionPoint (k : ℕ) (target : CyclicPolygon (k + 1)) :
    Continuous (subdivisionPoint k target) := by
  -- The finite edge index is discrete; on each component the parameter map is affine.
  refine continuous_prod_of_discrete_left.mpr ?_
  intro i
  rcases subdivisionIndex_trichotomy i with hi | hi | hi
  · have hindex : subdivisionIndex k i =
        ⟨i.val, Nat.lt_succ_of_lt hi⟩ := by
      apply Fin.ext
      exact subdivisionIndex_of_lt i hi
    simp only [subdivisionPoint, hindex, subdivisionParameter_of_lt i hi]
    exact target.continuous_edgePoint.comp
      (continuous_const.prodMk continuous_id)
  · dsimp only [subdivisionPoint]
    rw [subdivisionIndex_of_eq i hi]
    have hcontinuous : Continuous
        (fun t ↦ target.edgePoint (Fin.last k) (lowerHalfParameter t)) := by
      exact target.continuous_edgePoint.comp
        (continuous_const.prodMk continuous_lowerHalfParameter)
    exact hcontinuous.congr fun t ↦ by
      rw [subdivisionParameter_of_eq i hi]
  · dsimp only [subdivisionPoint]
    rw [subdivisionIndex_of_eq_succ i hi]
    have hcontinuous : Continuous
        (fun t ↦ target.edgePoint (Fin.last k) (upperHalfParameter t)) := by
      exact target.continuous_edgePoint.comp
        (continuous_const.prodMk continuous_upperHalfParameter)
    exact hcontinuous.congr fun t ↦ by
      rw [subdivisionParameter_of_eq_succ i hi]

/-- Helper for Theorem 77.1: doubling a lower-half parameter remains in the unit interval. -/
private lemma twice_mem_unitInterval (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    2 * (t : ℝ) ∈ unitInterval := by
  -- The original parameter is nonnegative and at most one half.
  constructor
  · nlinarith [t.property.1]
  · linarith

/-- Helper for Theorem 77.1: rescaling a lower-half parameter back to the full interval. -/
private def lowerHalfSourceParameter (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    unitInterval :=
  ⟨2 * (t : ℝ), twice_mem_unitInterval t ht⟩

/-- Helper for Theorem 77.1: rescaling an upper-half parameter remains in the unit interval. -/
private lemma twiceSubOne_mem_unitInterval (t : unitInterval) (ht : 1 / 2 < (t : ℝ)) :
    2 * (t : ℝ) - 1 ∈ unitInterval := by
  -- Strictly exceeding one half gives the lower bound; `t ≤ 1` gives the upper bound.
  constructor
  · linarith
  · linarith [t.property.2]

/-- Helper for Theorem 77.1: rescaling an upper-half parameter back to the full interval. -/
private def upperHalfSourceParameter (t : unitInterval) (ht : 1 / 2 < (t : ℝ)) :
    unitInterval :=
  ⟨2 * (t : ℝ) - 1, twiceSubOne_mem_unitInterval t ht⟩

/-- Helper for Theorem 77.1: lower-half rescaling is inverse to lower-half contraction. -/
private lemma lowerHalfParameter_source (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    lowerHalfParameter (lowerHalfSourceParameter t ht) = t := by
  -- Compare real values and cancel the factor two.
  apply Subtype.ext
  rw [lowerHalfParameter_coe]
  dsimp only [lowerHalfSourceParameter]
  ring

/-- Helper for Theorem 77.1: upper-half rescaling is inverse to upper-half contraction. -/
private lemma upperHalfParameter_source (t : unitInterval) (ht : 1 / 2 < (t : ℝ)) :
    upperHalfParameter (upperHalfSourceParameter t ht) = t := by
  -- Compare real values and cancel the affine shift and factor two.
  apply Subtype.ext
  rw [upperHalfParameter_coe]
  dsimp only [upperHalfSourceParameter]
  ring

/-- Helper for Theorem 77.1: the source index of the lower half of the subdivided edge. -/
private def lowerSubdivisionIndex (k : ℕ) : Fin (k + 2) :=
  (Fin.last k).castSucc

/-- Helper for Theorem 77.1: the source index of the upper half of the subdivided edge. -/
private def upperSubdivisionIndex (k : ℕ) : Fin (k + 2) :=
  Fin.last (k + 1)

/-- Helper for Theorem 77.1: the lower subdivided source index has value `k`. -/
private lemma lowerSubdivisionIndex_val (k : ℕ) : (lowerSubdivisionIndex k).val = k := by
  -- `castSucc` preserves the value of the last index of `Fin (k + 1)`.
  rfl

/-- Helper for Theorem 77.1: the upper subdivided source index has value `k + 1`. -/
private lemma upperSubdivisionIndex_val (k : ℕ) :
    (upperSubdivisionIndex k).val = k + 1 := by
  -- This is the value of the last index of `Fin (k + 2)`.
  rfl

/-- Helper for Theorem 77.1: the common subdivision map covers the target boundary. -/
private lemma subdivisionPoint_surjective (k : ℕ) (target : CyclicPolygon (k + 1)) :
    Function.Surjective (subdivisionPoint k target) := by
  intro x
  obtain ⟨⟨j, t⟩, rfl⟩ := target.edgePoint_surjective x
  by_cases hj : j.val < k
  · let i : Fin (k + 2) := j.castSucc
    have hi : i.val < k := by
      exact hj
    refine ⟨(i, t), ?_⟩
    dsimp only [subdivisionPoint]
    rw [subdivisionParameter_of_lt i hi]
    congr 1
    apply Fin.ext
    exact subdivisionIndex_of_lt i hi
  · have hjval : j.val = k := by omega
    have hjlast : j = Fin.last k := by
      apply Fin.ext
      exact hjval
    subst j
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · refine ⟨(lowerSubdivisionIndex k, lowerHalfSourceParameter t ht), ?_⟩
      dsimp only [subdivisionPoint]
      rw [subdivisionIndex_of_eq _ (lowerSubdivisionIndex_val k),
        subdivisionParameter_of_eq _ (lowerSubdivisionIndex_val k),
        lowerHalfParameter_source t ht]
    · have ht' : 1 / 2 < (t : ℝ) := lt_of_not_ge ht
      refine ⟨(upperSubdivisionIndex k, upperHalfSourceParameter t ht'), ?_⟩
      dsimp only [subdivisionPoint]
      rw [subdivisionIndex_of_eq_succ _ (upperSubdivisionIndex_val k),
        subdivisionParameter_of_eq_succ _ (upperSubdivisionIndex_val k),
        upperHalfParameter_source t ht']

/-- Helper for Theorem 77.1: subdividing the final boundary edge preserves exactly
the endpoint identifications in the cyclic edge parameter space. -/
private lemma subdivisionPoint_eq_iff {k : ℕ} (source : CyclicPolygon (k + 2))
    (target : CyclicPolygon (k + 1)) (i j : Fin (k + 2)) (s t : unitInterval) :
    source.edgePoint i s = source.edgePoint j t ↔
      subdivisionPoint k target (i, s) = subdivisionPoint k target (j, t) := by
  rw [source.edgePoint_eq_iff]
  dsimp only [subdivisionPoint]
  rw [target.edgePoint_eq_iff]
  have hk : 2 ≤ k := by
    -- The target is a cyclic polygon, so its `k + 1` sides number at least three.
    have hthree := target.three_le
    omega
  rcases subdivisionIndex_trichotomy i with hi | hi | hi <;>
    rcases subdivisionIndex_trichotomy j with hj | hj | hj
  · have hiSource : i.val < k + 1 := by omega
    have hjSource : j.val < k + 1 := by omega
    have hiIndex : subdivisionIndex k i = ⟨i.val, Nat.lt_succ_of_lt hi⟩ := by
      apply Fin.ext
      exact subdivisionIndex_of_lt i hi
    have hjIndex : subdivisionIndex k j = ⟨j.val, Nat.lt_succ_of_lt hj⟩ := by
      apply Fin.ext
      exact subdivisionIndex_of_lt j hj
    rw [subdivisionParameter_of_lt i hi, subdivisionParameter_of_lt j hj,
      hiIndex, hjIndex, finRotate_of_lt hiSource, finRotate_of_lt hjSource,
      finRotate_of_lt hi, finRotate_of_lt hj]
    simp only [Fin.ext_iff]
  · have hiSource : i.val < k + 1 := by omega
    have hjSource : j.val < k + 1 := by omega
    have hiIndex : subdivisionIndex k i = ⟨i.val, Nat.lt_succ_of_lt hi⟩ := by
      apply Fin.ext
      exact subdivisionIndex_of_lt i hi
    rw [subdivisionParameter_of_lt i hi, subdivisionParameter_of_eq j hj,
      hiIndex, subdivisionIndex_of_eq j hj,
      finRotate_of_lt hiSource, finRotate_of_lt hjSource,
      finRotate_of_lt hi, finRotate_last]
    simp only [Fin.ext_iff, Fin.val_last, lowerHalfParameter_ne_one,
      lowerHalfParameter_eq_zero_iff]
    constructor
    · rintro (⟨hij, -⟩ | ⟨-, -, hij⟩ | ⟨hs, ht, hij⟩)
      · exfalso
        omega
      · exfalso
        omega
      · exact Or.inr (Or.inr ⟨hs, ht, by omega⟩)
    · rintro (⟨hij, -⟩ | ⟨-, hfalse, -⟩ | ⟨hs, ht, hij⟩)
      · exfalso
        omega
      · contradiction
      · exact Or.inr (Or.inr ⟨hs, ht, by omega⟩)
  · have hiSource : i.val < k + 1 := by omega
    have hjLast : j = Fin.last (k + 1) := by
      apply Fin.ext
      simpa using hj
    subst j
    have hiIndex : subdivisionIndex k i = ⟨i.val, Nat.lt_succ_of_lt hi⟩ := by
      apply Fin.ext
      exact subdivisionIndex_of_lt i hi
    rw [subdivisionParameter_of_lt i hi,
      subdivisionParameter_of_eq_succ _ hj,
      hiIndex, subdivisionIndex_of_eq_succ _ hj,
      finRotate_of_lt hiSource, finRotate_last,
      finRotate_of_lt hi, finRotate_last]
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero, upperHalfParameter_eq_one_iff,
      upperHalfParameter_ne_zero]
    constructor
    · rintro (⟨hij, -⟩ | ⟨hs, ht, hij⟩ | ⟨-, -, hij⟩)
      · exfalso
        omega
      · exact Or.inr (Or.inl ⟨hs, ht, by omega⟩)
      · exfalso
        omega
    · rintro (⟨hij, -⟩ | ⟨hs, ht, hij⟩ | ⟨-, hfalse, -⟩)
      · exfalso
        omega
      · exact Or.inr (Or.inl ⟨hs, ht, by omega⟩)
      · contradiction
  · have hiSource : i.val < k + 1 := by omega
    have hjSource : j.val < k + 1 := by omega
    have hjIndex : subdivisionIndex k j = ⟨j.val, Nat.lt_succ_of_lt hj⟩ := by
      apply Fin.ext
      exact subdivisionIndex_of_lt j hj
    rw [subdivisionParameter_of_eq i hi, subdivisionParameter_of_lt j hj,
      subdivisionIndex_of_eq i hi, hjIndex,
      finRotate_of_lt hiSource, finRotate_of_lt hjSource,
      finRotate_last, finRotate_of_lt hj]
    simp only [Fin.ext_iff, Fin.val_last, lowerHalfParameter_eq_zero_iff,
      lowerHalfParameter_ne_one]
    constructor
    · rintro (⟨hij, -⟩ | ⟨hs, ht, hij⟩ | ⟨-, -, hij⟩)
      · exfalso
        omega
      · exact Or.inr (Or.inl ⟨hs, ht, by omega⟩)
      · exfalso
        omega
    · rintro (⟨hij, -⟩ | ⟨hs, ht, hij⟩ | ⟨hfalse, -, -⟩)
      · exfalso
        omega
      · exact Or.inr (Or.inl ⟨hs, ht, by omega⟩)
      · contradiction
  · have hiSource : i.val < k + 1 := by omega
    have hjSource : j.val < k + 1 := by omega
    rw [subdivisionParameter_of_eq i hi, subdivisionParameter_of_eq j hj,
      subdivisionIndex_of_eq i hi, subdivisionIndex_of_eq j hj,
      finRotate_of_lt hiSource, finRotate_of_lt hjSource,
      finRotate_last]
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero,
      lowerHalfParameter_eq_iff, lowerHalfParameter_eq_zero_iff,
      lowerHalfParameter_ne_one]
    constructor
    · rintro (⟨-, hst⟩ | ⟨-, -, hij⟩ | ⟨-, -, hij⟩)
      · exact Or.inl ⟨True.intro, hst⟩
      · exfalso
        omega
      · exfalso
        omega
    · rintro (⟨-, hst⟩ | ⟨-, hfalse, -⟩ | ⟨hfalse, -, -⟩)
      · exact Or.inl ⟨by omega, hst⟩
      · contradiction
      · contradiction
  · have hiSource : i.val < k + 1 := by omega
    have hjLast : j = Fin.last (k + 1) := by
      apply Fin.ext
      simpa using hj
    subst j
    rw [subdivisionParameter_of_eq i hi,
      subdivisionParameter_of_eq_succ _ hj,
      subdivisionIndex_of_eq i hi, subdivisionIndex_of_eq_succ _ hj,
      finRotate_of_lt hiSource, finRotate_last, finRotate_last]
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero,
      lowerHalfParameter_eq_upperHalfParameter_iff,
      lowerHalfParameter_eq_zero_iff, upperHalfParameter_eq_one_iff,
      lowerHalfParameter_ne_one, upperHalfParameter_ne_zero]
    constructor
    · rintro (⟨hij, -⟩ | ⟨-, -, hij⟩ | ⟨hs, ht, hij⟩)
      · exfalso
        omega
      · exfalso
        omega
      · exact Or.inl ⟨True.intro, hs, ht⟩
    · rintro (⟨-, hs, ht⟩ | ⟨-, -, hij⟩ | ⟨hfalse, -, -⟩)
      · exact Or.inr (Or.inr ⟨hs, ht, by omega⟩)
      · exfalso
        omega
      · contradiction
  · have hiLast : i = Fin.last (k + 1) := by
      apply Fin.ext
      simpa using hi
    subst i
    have hjSource : j.val < k + 1 := by omega
    have hjIndex : subdivisionIndex k j = ⟨j.val, Nat.lt_succ_of_lt hj⟩ := by
      apply Fin.ext
      exact subdivisionIndex_of_lt j hj
    rw [subdivisionParameter_of_eq_succ _ hi,
      subdivisionParameter_of_lt j hj,
      subdivisionIndex_of_eq_succ _ hi, hjIndex,
      finRotate_last, finRotate_of_lt hjSource,
      finRotate_of_lt hj, finRotate_last]
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero,
      upperHalfParameter_ne_zero, upperHalfParameter_eq_one_iff]
    constructor
    · rintro (⟨hij, -⟩ | ⟨-, -, hij⟩ | ⟨hs, ht, hij⟩)
      · exfalso
        omega
      · exfalso
        omega
      · exact Or.inr (Or.inr ⟨hs, ht, by omega⟩)
    · rintro (⟨hij, -⟩ | ⟨hfalse, -, -⟩ | ⟨hs, ht, hij⟩)
      · exfalso
        omega
      · contradiction
      · exact Or.inr (Or.inr ⟨hs, ht, by omega⟩)
  · have hiLast : i = Fin.last (k + 1) := by
      apply Fin.ext
      simpa using hi
    subst i
    have hjSource : j.val < k + 1 := by omega
    rw [subdivisionParameter_of_eq_succ _ hi,
      subdivisionParameter_of_eq j hj,
      subdivisionIndex_of_eq_succ _ hi, subdivisionIndex_of_eq j hj,
      finRotate_last, finRotate_of_lt hjSource,
      finRotate_last]
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero,
      upperHalfParameter_eq_lowerHalfParameter_iff,
      upperHalfParameter_ne_zero, lowerHalfParameter_ne_one]
    constructor
    · rintro (⟨hij, -⟩ | ⟨hs, ht, hij⟩ | ⟨-, -, hij⟩)
      · exfalso
        omega
      · exact Or.inl ⟨True.intro, hs, ht⟩
      · exfalso
        omega
    · rintro (⟨-, hs, ht⟩ | ⟨hfalse, -, -⟩ | ⟨-, -, hij⟩)
      · exact Or.inr (Or.inl ⟨hs, ht, by omega⟩)
      · contradiction
      · exfalso
        omega
  · have hiLast : i = Fin.last (k + 1) := by
      apply Fin.ext
      simpa using hi
    have hjLast : j = Fin.last (k + 1) := by
      apply Fin.ext
      simpa using hj
    subst i
    subst j
    rw [subdivisionParameter_of_eq_succ _ hi,
      subdivisionParameter_of_eq_succ _ hj,
      subdivisionIndex_of_eq_succ _ hi,
      finRotate_last, finRotate_last]
    simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero,
      upperHalfParameter_eq_iff, upperHalfParameter_ne_zero]
    constructor
    · rintro (⟨-, hst⟩ | ⟨-, -, hij⟩ | ⟨-, -, hij⟩)
      · exact Or.inl ⟨True.intro, hst⟩
      · exfalso
        omega
      · exfalso
        omega
    · rintro (⟨-, hst⟩ | ⟨hfalse, -, -⟩ | ⟨-, hfalse, -⟩)
      · exact Or.inl ⟨True.intro, hst⟩
      · contradiction
      · contradiction

/-- Helper for Theorem 77.1: the final-edge subdivision quotient induces a
boundary homeomorphism with the prescribed parameter-space formula. -/
private lemma existsBoundaryHomeomorphForSubdivision {k : ℕ}
    (source : CyclicPolygon (k + 2)) (target : CyclicPolygon (k + 1)) :
    ∃ h : source.boundary ≃ₜ target.boundary,
      ∀ (i : Fin (k + 2)) (s : unitInterval),
        h (source.edgePoint i s) = subdivisionPoint k target (i, s) := by
  -- Present both boundaries as quotients of the same subdivided edge-parameter space.
  let f : C(Fin (k + 2) × unitInterval, source.boundary) :=
    ⟨fun z ↦ source.edgePoint z.1 z.2, source.continuous_edgePoint⟩
  let g : C(Fin (k + 2) × unitInterval, target.boundary) :=
    ⟨subdivisionPoint k target, continuous_subdivisionPoint k target⟩
  have hf : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous
      source.edgePoint_surjective source.continuous_edgePoint
  have hg : Topology.IsQuotientMap g :=
    Topology.IsQuotientMap.of_surjective_continuous
      (subdivisionPoint_surjective k target) (continuous_subdivisionPoint k target)
  have hker : ∀ z z', f z = f z' ↔ g z = g z' := by
    intro z z'
    exact subdivisionPoint_eq_iff source target z.1 z'.1 z.2 z'.2
  obtain ⟨h, hh⟩ := existsHomeomorphOfQuotientPresentations
    f g hf hg (Homeomorph.refl _) hker
  refine ⟨h, ?_⟩
  intro i s
  -- Evaluate the induced quotient homeomorphism on the selected edge representative.
  exact hh (i, s)

/-- Helper for Theorem 77.1: a boundary homeomorphism between cyclic polygons
with possibly different side counts admits a radial filled-region extension. -/
lemma existsRadialExtensionBetween {m n : ℕ}
    (source : CyclicPolygon m) (target : CyclicPolygon n)
    (p : source.interior) (q : target.interior)
    (h : source.boundary ≃ₜ target.boundary) :
    ∃ H : source.region ≃ₜ target.region,
      ∀ (x : source.boundary) (s : unitInterval),
        H (source.radialPoint p x s) = target.radialPoint q (h x) s := by
  -- Local instance justification (compact quotient presentation): each boundary
  -- is compact, and the instances are needed only for the radial quotient maps.
  letI : CompactSpace source.boundary :=
    isCompact_univ_iff.mp source.boundary_isCompact
  letI : CompactSpace target.boundary :=
    isCompact_univ_iff.mp target.boundary_isCompact
  let f : C(source.boundary × unitInterval, source.region) :=
    ⟨fun z ↦ source.radialPoint p z.1 z.2, source.continuous_radialPoint p⟩
  let g : C(target.boundary × unitInterval, target.region) :=
    ⟨fun z ↦ target.radialPoint q z.1 z.2, target.continuous_radialPoint q⟩
  have hf : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous
      (source.radialPoint_surjective p) (source.continuous_radialPoint p)
  have hg : Topology.IsQuotientMap g :=
    Topology.IsQuotientMap.of_surjective_continuous
      (target.radialPoint_surjective q) (target.continuous_radialPoint q)
  let etop := h.prodCongr (Homeomorph.refl unitInterval)
  have etop_apply (z : source.boundary × unitInterval) :
      etop z = (h z.1, z.2) := rfl
  have hker : ∀ z z', f z = f z' ↔ g (etop z) = g (etop z') := by
    intro z z'
    dsimp only [f, g]
    simp only [ContinuousMap.coe_mk]
    rw [etop_apply, etop_apply, source.radialPoint_eq_iff,
      target.radialPoint_eq_iff]
    exact or_congr Iff.rfl (and_congr h.injective.eq_iff.symm Iff.rfl)
  obtain ⟨H, hH⟩ := existsHomeomorphOfQuotientPresentations
    f g hf hg etop hker
  refine ⟨H, ?_⟩
  intro x s
  -- Evaluate the radial quotient comparison on one boundary ray.
  have hspec := hH (x, s)
  dsimp only [f, g, etop] at hspec
  exact hspec

/-- Helper for Theorem 77.1: combining the final two source edges into the
two affine halves of the final target edge extends to a region homeomorphism. -/
theorem existsRegionHomeomorph {k : ℕ}
    (source : CyclicPolygon (k + 2)) (target : CyclicPolygon (k + 1)) :
    ∃ H : source.region ≃ₜ target.region,
      (∀ (i : Fin (k + 2)) (hi : i.val < k) (s : unitInterval),
        H (source.boundaryToRegion (source.edgePoint i s)) =
          target.boundaryToRegion
            (target.edgePoint ⟨i.val, Nat.lt_succ_of_lt hi⟩ s)) ∧
      (∀ s : unitInterval,
        H (source.boundaryToRegion
            (source.edgePoint (Fin.last k).castSucc s)) =
          target.boundaryToRegion
            (target.edgePoint (Fin.last k) (lowerHalfParameter s))) ∧
      (∀ s : unitInterval,
        H (source.boundaryToRegion
            (source.edgePoint (Fin.last (k + 1)) s)) =
          target.boundaryToRegion
            (target.edgePoint (Fin.last k) (upperHalfParameter s))) := by
  classical
  let p : source.interior :=
    Classical.choice source.regionInterior_nonempty.to_subtype
  let q : target.interior :=
    Classical.choice target.regionInterior_nonempty.to_subtype
  obtain ⟨h, hedge⟩ := existsBoundaryHomeomorphForSubdivision source target
  obtain ⟨H, hradial⟩ := existsRadialExtensionBetween source target p q h
  have hboundary (i : Fin (k + 2)) (s : unitInterval) :
      H (source.boundaryToRegion (source.edgePoint i s)) =
        target.boundaryToRegion (subdivisionPoint k target (i, s)) := by
    -- Express a boundary point as the endpoint of its radial segment, then use
    -- the boundary quotient formula inside the radial extension.
    rw [← source.radialPoint_one_eq_boundaryToRegion p (source.edgePoint i s)]
    rw [hradial, hedge]
    exact target.radialPoint_one_eq_boundaryToRegion q
      (subdivisionPoint k target (i, s))
  refine ⟨H, ?_, ?_, ?_⟩
  · intro i hi s
    rw [hboundary]
    apply congrArg target.boundaryToRegion
    dsimp only [subdivisionPoint]
    rw [subdivisionParameter_of_lt i hi]
    congr 1
    apply Fin.ext
    exact subdivisionIndex_of_lt i hi
  · intro s
    rw [hboundary]
    dsimp only [subdivisionPoint]
    have hlower : ((Fin.last k).castSucc : Fin (k + 2)).val = k := rfl
    rw [subdivisionIndex_of_eq _ hlower,
      subdivisionParameter_of_eq _ hlower]
  · intro s
    rw [hboundary]
    dsimp only [subdivisionPoint]
    have hupper : (Fin.last (k + 1) : Fin (k + 2)).val = k + 1 := rfl
    rw [subdivisionIndex_of_eq_succ _ hupper,
      subdivisionParameter_of_eq_succ _ hupper]

end

end CyclicPolygon.EdgeCompression
