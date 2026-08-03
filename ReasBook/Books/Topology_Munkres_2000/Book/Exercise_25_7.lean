module

public import Topology_Munkres_2000.Book.Exercise_25_6.WeaklyLocallyConnected
public import Topology_Munkres_2000.Book.Definition_25_4.Neighborhoods
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex

public section

open Filter Set Topology
open scoped Convex

namespace InfiniteBroom

/-- The point `aₙ₊₁` on the horizontal handle of the infinite broom. -/
noncomputable def handlePoint (n : ℕ) : ℝ × ℝ := ((n + 1 : ℝ)⁻¹, 0)

/-- The `k`th tip above `aₙ₊₂` of a bristle with common origin `aₙ₊₁`. -/
noncomputable def bristleTip (n k : ℕ) : ℝ × ℝ :=
  ((n + 2 : ℝ)⁻¹, ((n + 1 : ℝ)⁻¹ - (n + 2 : ℝ)⁻¹) / (k + 1 : ℝ))

/-- The `k`th bristle of the fan based at `aₙ₊₁`. -/
def bristle (n k : ℕ) : Set (ℝ × ℝ) :=
  segment ℝ (handlePoint n) (bristleTip n k)

/-- The infinite fan in the strip from `aₙ₊₂` to `aₙ₊₁`. All of its bristles
have the common origin `aₙ₊₁`, as in Figure 25.1. -/
def subBroom (n : ℕ) : Set (ℝ × ℝ) := ⋃ k : ℕ, bristle n k

/-- Every bristle in the `n`th sub-broom has the common origin `aₙ₊₁`. -/
theorem handlePoint_mem_bristle (n k : ℕ) : handlePoint n ∈ bristle n k :=
  left_mem_segment ℝ _ _

/-- The planar infinite broom pictured in Figure 25.1: its horizontal handle
together with the successive common-origin infinite fans based at the points `aᵢ`. -/
def carrier : Set (ℝ × ℝ) :=
  segment ℝ (0, 0) (1, 0) ∪ ⋃ n : ℕ, subBroom n

/-- A point belongs to the fan based at `aₙ₊₁` exactly when it lies on one of
the bristles sharing that origin. -/
theorem mem_subBroom_iff (n : ℕ) (x : ℝ × ℝ) :
    x ∈ subBroom n ↔ ∃ k : ℕ, x ∈ bristle n k := by
  simp [subBroom]

/-- A point belongs to the infinite broom exactly when it lies on the handle or
in one of its common-origin sub-brooms. -/
theorem mem_carrier_iff (x : ℝ × ℝ) :
    x ∈ carrier ↔
      x ∈ segment ℝ (0, 0) (1, 0) ∨
        ∃ n : ℕ, x ∈ subBroom n := by
  simp [carrier]

/-- The infinite broom with its subspace topology. -/
abbrev Space := carrier

/-- The limiting point `p` belongs to the horizontal handle. -/
theorem point_mem_carrier : (0, 0) ∈ carrier :=
  Or.inl (left_mem_segment ℝ _ _)

/-- The distinguished limiting point `p` of the infinite broom. -/
def point : Space := ⟨(0, 0), point_mem_carrier⟩

/-- Each point `aₙ₊₁` belongs to the horizontal handle of the infinite broom. -/
theorem handlePoint_mem_carrier (n : ℕ) : handlePoint n ∈ carrier := by
  refine Or.inr (mem_iUnion.2 ⟨n, ?_⟩)
  exact mem_iUnion.2 ⟨0, handlePoint_mem_bristle n 0⟩

/-- The point `aₙ₊₁`, regarded as a point of the infinite broom. -/
noncomputable def handlePointInSpace (n : ℕ) : Space :=
  ⟨handlePoint n, handlePoint_mem_carrier n⟩

/-- Helper for Exercise 25.7: the reciprocal coordinates of the handle points
reverse the order of their natural-number indices. -/
private lemma handleReciprocal_lt_handleReciprocal_iff {m n : ℕ} :
    ((m + 1 : ℕ) : ℝ)⁻¹ < ((n + 1 : ℕ) : ℝ)⁻¹ ↔ n < m := by
  -- Positive denominators let inversion turn the real inequality around.
  rw [inv_lt_inv₀]
  · norm_cast
    omega
  · positivity
  · positivity

/-- Helper for Exercise 25.7: increasing the handle index weakly decreases its
reciprocal horizontal coordinate. -/
private lemma handleReciprocal_anti {m n : ℕ} (h : n ≤ m) :
    ((m + 1 : ℕ) : ℝ)⁻¹ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- The same inversion comparison works for weak inequalities.
  rw [inv_le_inv₀]
  · norm_cast
    omega
  · positivity
  · positivity

/-- Helper for Exercise 25.7: every bristle tip is a point of the broom. -/
private lemma bristleTip_mem_carrier (n k : ℕ) : bristleTip n k ∈ carrier := by
  -- The tip is the right endpoint of its named bristle.
  refine Or.inr (mem_iUnion.2 ⟨n, ?_⟩)
  exact mem_iUnion.2 ⟨k, right_mem_segment ℝ _ _⟩

/-- Helper for Exercise 25.7: a bristle tip regarded as a point of `Space`. -/
private noncomputable def bristleTipInSpace (n k : ℕ) : Space :=
  ⟨bristleTip n k, bristleTip_mem_carrier n k⟩

/-- Helper for Exercise 25.7: the handle points converge to the distinguished
point `point`. -/
private lemma tendsto_handlePointInSpace : Tendsto handlePointInSpace atTop (𝓝 point) := by
  -- It suffices to check the two planar coordinates after the subtype inclusion.
  rw [tendsto_subtype_rng, Prod.tendsto_iff]
  constructor
  · simpa only [handlePointInSpace, handlePoint, point, Prod.fst, Nat.cast_add,
      Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  · simpa only [handlePointInSpace, handlePoint, point, Prod.snd] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

/-- Helper for Exercise 25.7: for a fixed fan, its bristle tips converge to the
next handle point. -/
private lemma tendsto_bristleTipInSpace (n : ℕ) :
    Tendsto (bristleTipInSpace n) atTop (𝓝 (handlePointInSpace (n + 1))) := by
  -- The first coordinate is constant, and the second is a constant multiple
  -- of the reciprocal sequence tending to zero.
  rw [tendsto_subtype_rng, Prod.tendsto_iff]
  constructor
  · norm_num [bristleTipInSpace, bristleTip, handlePointInSpace, handlePoint,
      Nat.cast_add, Nat.cast_one, add_assoc]
  · have hrecip : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hscaled := hrecip.const_mul
      (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹)
    simpa [bristleTipInSpace, bristleTip, handlePointInSpace, handlePoint,
      div_eq_mul_inv, add_assoc] using hscaled

/-- Helper for Exercise 25.7: membership in a bristle admits the standard
line-parameter description. -/
private lemma bristleCoordinates {n k : ℕ} {z : ℝ × ℝ} (hz : z ∈ bristle n k) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      z.1 = (1 - t) * ((n + 1 : ℕ) : ℝ)⁻¹ +
          t * ((n + 2 : ℕ) : ℝ)⁻¹ ∧
        z.2 = t * ((((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹) /
          ((k + 1 : ℕ) : ℝ)) := by
  -- Expand only the segment parameterization, leaving the broom opaque.
  rw [bristle, segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨t, ht, ?_, ?_⟩
  · simp [AffineMap.lineMap_apply_module, handlePoint, bristleTip]
  · simp [AffineMap.lineMap_apply_module, handlePoint, bristleTip]

/-- Helper for Exercise 25.7: along a bristle, height is its reciprocal slope
times the remaining horizontal distance to the common origin. -/
private lemma bristle_height_eq {n k : ℕ} {z : ℝ × ℝ} (hz : z ∈ bristle n k) :
    z.2 = ((k + 1 : ℕ) : ℝ)⁻¹ *
      (((n + 1 : ℕ) : ℝ)⁻¹ - z.1) := by
  -- Substitute the line coordinates and normalize the scalar identity.
  obtain ⟨t, -, hfst, hsnd⟩ := bristleCoordinates hz
  rw [hfst, hsnd]
  field_simp
  ring

/-- Helper for Exercise 25.7: a non-origin point on a bristle has positive
height and lies strictly to the left of its common origin. -/
private lemma bristle_strict_coordinates {n k : ℕ} {z : ℝ × ℝ} (hz : z ∈ bristle n k)
    (hne : z ≠ handlePoint n) :
    0 < z.2 ∧ z.1 < ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- The segment parameter cannot be zero away from its left endpoint.
  obtain ⟨t, ht, hfst, hsnd⟩ := bristleCoordinates hz
  have hgap : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹ := by
    rw [sub_pos, handleReciprocal_lt_handleReciprocal_iff]
    omega
  have ht_ne : t ≠ 0 := by
    intro ht_zero
    apply hne
    ext
    · simpa [ht_zero, handlePoint] using hfst
    · simpa [ht_zero, handlePoint] using hsnd
  have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_ne)
  constructor
  · rw [hsnd]
    positivity
  · rw [hfst]
    nlinarith [ht.2]

/-- Helper for Exercise 25.7: the first coordinate on a bristle lies between
the two adjacent handle coordinates. -/
private lemma bristle_fst_bounds {n k : ℕ} {z : ℝ × ℝ} (hz : z ∈ bristle n k) :
    ((n + 2 : ℕ) : ℝ)⁻¹ ≤ z.1 ∧ z.1 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- Both bounds follow directly from the convex line parameter.
  obtain ⟨t, ht, hfst, -⟩ := bristleCoordinates hz
  have hgap : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹ := by
    rw [sub_nonneg]
    exact handleReciprocal_anti (Nat.le_succ n)
  rw [hfst]
  constructor
  · nlinarith [ht.2]
  · nlinarith [ht.1]

/-- Helper for Exercise 25.7: on the `n`th sub-broom, the sum of the planar
coordinates is at most the coordinate of its common origin. -/
private lemma bristle_add_le_handleReciprocal {n k : ℕ} {z : ℝ × ℝ}
    (hz : z ∈ bristle n k) :
    z.1 + z.2 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- The reciprocal bristle slope is at most one, so height cannot exceed the
  -- horizontal distance remaining to the common origin.
  have hfst := (bristle_fst_bounds hz).2
  have hslope : ((k + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    simpa using (handleReciprocal_anti (m := k) (n := 0) (Nat.zero_le k))
  have hslope_nonneg : 0 ≤ ((k + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hdistance : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ - z.1 := sub_nonneg.2 hfst
  have hproduct :
      0 ≤ (1 - ((k + 1 : ℕ) : ℝ)⁻¹) *
        (((n + 1 : ℕ) : ℝ)⁻¹ - z.1) :=
    mul_nonneg (sub_nonneg.2 hslope) hdistance
  rw [bristle_height_eq hz]
  nlinarith

/-- Helper for Exercise 25.7: the open planar cell occupied by the non-origin
part of the `n`th fan. -/
private def fanCell (n : ℕ) : Set (ℝ × ℝ) :=
  {z | 0 < z.2 ∧ z.1 < ((n + 1 : ℕ) : ℝ)⁻¹ ∧
    ((n + 2 : ℕ) : ℝ)⁻¹ < z.1 + z.2}

/-- Helper for Exercise 25.7: the upper neighboring slope used to isolate the
`k`th bristle. -/
private noncomputable def upperBristleSlope (k : ℕ) : ℝ :=
  if k = 0 then 2 else (k : ℝ)⁻¹

/-- Helper for Exercise 25.7: an open planar cell isolating one bristle away
from its common origin. -/
private def bristleCell (n k : ℕ) : Set (ℝ × ℝ) :=
  {z | z ∈ fanCell n ∧
    ((k + 2 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ)⁻¹ - z.1) < z.2 ∧
    z.2 < upperBristleSlope k * (((n + 1 : ℕ) : ℝ)⁻¹ - z.1)}

/-- Helper for Exercise 25.7: each isolating bristle cell is open in the
ambient plane. -/
private lemma isOpen_bristleCell (n k : ℕ) : IsOpen (bristleCell n k) := by
  -- Every defining inequality compares continuous real-valued coordinate
  -- expressions.
  have hfan : IsOpen (fanCell n) := by
    have hy : IsOpen {z : ℝ × ℝ | (0 : ℝ) < z.2} :=
      isOpen_lt continuous_const continuous_snd
    have hx : IsOpen {z : ℝ × ℝ | z.1 < ((n + 1 : ℕ) : ℝ)⁻¹} :=
      isOpen_lt continuous_fst continuous_const
    have hsum : IsOpen {z : ℝ × ℝ |
        ((n + 2 : ℕ) : ℝ)⁻¹ < z.1 + z.2} :=
      isOpen_lt continuous_const (continuous_fst.add continuous_snd)
    change IsOpen ({z : ℝ × ℝ | (0 : ℝ) < z.2} ∩
      ({z : ℝ × ℝ | z.1 < ((n + 1 : ℕ) : ℝ)⁻¹} ∩
        {z : ℝ × ℝ | ((n + 2 : ℕ) : ℝ)⁻¹ < z.1 + z.2}))
    exact hy.inter (hx.inter hsum)
  have hlower : IsOpen {z : ℝ × ℝ |
      ((k + 2 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ)⁻¹ - z.1) < z.2} :=
    isOpen_lt (continuous_const.mul (continuous_const.sub continuous_fst)) continuous_snd
  have hupper : IsOpen {z : ℝ × ℝ | z.2 <
      upperBristleSlope k * (((n + 1 : ℕ) : ℝ)⁻¹ - z.1)} :=
    isOpen_lt continuous_snd
      (continuous_const.mul (continuous_const.sub continuous_fst))
  change IsOpen (fanCell n ∩
    ({z : ℝ × ℝ |
      ((k + 2 : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ)⁻¹ - z.1) < z.2} ∩
      {z : ℝ × ℝ | z.2 <
        upperBristleSlope k * (((n + 1 : ℕ) : ℝ)⁻¹ - z.1)}))
  exact hfan.inter (hlower.inter hupper)

/-- Helper for Exercise 25.7: within the broom, `fanCell n` is precisely the
`n`th sub-broom with its common origin removed. -/
private lemma mem_fanCell_iff {n : ℕ} {z : ℝ × ℝ} (hz : z ∈ carrier) :
    z ∈ fanCell n ↔ z ∈ subBroom n ∧ z ≠ handlePoint n := by
  constructor
  · intro hcell
    rcases hcell with ⟨hy, hx, hsum⟩
    rcases (mem_carrier_iff z).1 hz with hhandle | ⟨m, hm⟩
    · have hsnd :=
        ((Prod.segment_subset (𝕜 := ℝ) ((0, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)) hhandle).2
      have hyzero : z.2 = 0 := by
        simpa only [segment_same, mem_singleton_iff] using hsnd
      linarith
    · obtain ⟨j, hj⟩ := (mem_subBroom_iff m z).1 hm
      have hlower := (bristle_fst_bounds hj).1
      have hupp := bristle_add_le_handleReciprocal hj
      have hnm : n ≤ m := by
        have hstrict : ((m + 2 : ℕ) : ℝ)⁻¹ < ((n + 1 : ℕ) : ℝ)⁻¹ :=
          lt_of_le_of_lt hlower hx
        rw [handleReciprocal_lt_handleReciprocal_iff] at hstrict
        omega
      have hmn : m ≤ n := by
        have hstrict : ((n + 2 : ℕ) : ℝ)⁻¹ < ((m + 1 : ℕ) : ℝ)⁻¹ :=
          lt_of_lt_of_le hsum hupp
        rw [handleReciprocal_lt_handleReciprocal_iff] at hstrict
        omega
      have hmn_eq : m = n := Nat.le_antisymm hmn hnm
      subst m
      refine ⟨hm, ?_⟩
      intro hbase
      rw [hbase, handlePoint] at hy
      exact lt_irrefl 0 hy
  · rintro ⟨hsub, hne⟩
    obtain ⟨k, hk⟩ := (mem_subBroom_iff n z).1 hsub
    have hstrict := bristle_strict_coordinates hk hne
    have hlower := (bristle_fst_bounds hk).1
    exact ⟨hstrict.1, hstrict.2, lt_of_le_of_lt hlower (lt_add_of_pos_right _ hstrict.1)⟩

/-- Helper for Exercise 25.7: the isolating cell meets the broom exactly in
the selected bristle with its common origin removed. -/
private lemma mem_bristleCell_iff {n k : ℕ} {z : ℝ × ℝ} (hz : z ∈ carrier) :
    z ∈ bristleCell n k ↔ z ∈ bristle n k ∧ z ≠ handlePoint n := by
  constructor
  · rintro ⟨hfan, hlower, hupper⟩
    obtain ⟨hsub, hne⟩ := (mem_fanCell_iff hz).1 hfan
    obtain ⟨j, hj⟩ := (mem_subBroom_iff n z).1 hsub
    have hdistance : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ - z.1 :=
      sub_pos.2 hfan.2.1
    rw [bristle_height_eq hj] at hlower hupper
    have hj_le_k : j ≤ k := by
      have hslope : ((k + 2 : ℕ) : ℝ)⁻¹ < ((j + 1 : ℕ) : ℝ)⁻¹ :=
        (mul_lt_mul_iff_of_pos_right hdistance).1 hlower
      rw [handleReciprocal_lt_handleReciprocal_iff] at hslope
      omega
    have hk_le_j : k ≤ j := by
      rcases k with _ | k
      · exact Nat.zero_le j
      · have hupper' : ((j + 1 : ℕ) : ℝ)⁻¹ < ((k + 1 : ℕ) : ℝ)⁻¹ := by
          simpa [upperBristleSlope] using
            (mul_lt_mul_iff_of_pos_right hdistance).1 hupper
        rw [handleReciprocal_lt_handleReciprocal_iff] at hupper'
        omega
    have hjk : j = k := Nat.le_antisymm hj_le_k hk_le_j
    subst j
    exact ⟨hj, hne⟩
  · rintro ⟨hk, hne⟩
    have hfan := (mem_fanCell_iff hz).2
      ⟨(mem_subBroom_iff n z).2 ⟨k, hk⟩, hne⟩
    have hdistance : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ - z.1 :=
      sub_pos.2 hfan.2.1
    refine ⟨hfan, ?_, ?_⟩
    · rw [bristle_height_eq hk]
      exact (mul_lt_mul_iff_of_pos_right hdistance).2 <| by
        rw [handleReciprocal_lt_handleReciprocal_iff]
        omega
    · rw [bristle_height_eq hk]
      rcases k with _ | k
      · norm_num [upperBristleSlope, Nat.cast_add, Nat.cast_one] at hdistance ⊢
        nlinarith
      · exact (mul_lt_mul_iff_of_pos_right hdistance).2 <| by
          simp only [upperBristleSlope, Nat.succ_ne_zero, ↓reduceIte, Nat.cast_add,
            Nat.cast_one]
          rw [inv_lt_inv₀]
          · norm_num
          · positivity
          · positivity

/-- Helper for Exercise 25.7: the broom with one handle point removed. -/
private abbrev PuncturedAtHandle (n : ℕ) :=
  {x : Space // x ≠ handlePointInSpace n}

/-- Helper for Exercise 25.7: the selected bristle inside the broom punctured
at its common origin. -/
private def bristleInPunctured (n k : ℕ) : Set (PuncturedAtHandle n) :=
  {x | (x.1 : ℝ × ℝ) ∈ bristle n k}

/-- Helper for Exercise 25.7: a planar bristle is closed. -/
private lemma isClosed_bristle (n k : ℕ) : IsClosed (bristle n k) := by
  -- A segment is the compact continuous image of `[0, 1]`.
  have hcompact : IsCompact (bristle n k) := by
    rw [bristle, segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  exact hcompact.isClosed

/-- Helper for Exercise 25.7: a bristle becomes clopen after its common origin
is removed from the broom. -/
private lemma isClopen_bristleInPunctured (n k : ℕ) :
    IsClopen (bristleInPunctured n k) := by
  -- The open isolating cell gives openness, while compactness of the full
  -- segment gives closedness.
  have hcontinuous : Continuous (fun x : PuncturedAtHandle n ↦ (x.1 : ℝ × ℝ)) :=
    continuous_subtype_val.subtype_val
  have heq : bristleInPunctured n k =
      (fun x : PuncturedAtHandle n ↦ (x.1 : ℝ × ℝ)) ⁻¹' bristleCell n k := by
    ext x
    have hcarrier : (x.1 : ℝ × ℝ) ∈ carrier := x.1.property
    have hne : (x.1 : ℝ × ℝ) ≠ handlePoint n := by
      intro h
      apply x.property
      apply Subtype.ext
      exact h
    change (x.1 : ℝ × ℝ) ∈ bristle n k ↔ (x.1 : ℝ × ℝ) ∈ bristleCell n k
    rw [mem_bristleCell_iff hcarrier]
    exact (and_iff_left hne).symm
  constructor
  · exact (isClosed_bristle n k).preimage hcontinuous
  · rw [heq]
    exact (isOpen_bristleCell n k).preimage hcontinuous

/-- Helper for Exercise 25.7: a bristle tip is distinct from the common
origin of its fan. -/
private lemma bristleTipInSpace_ne_handlePointInSpace (n k : ℕ) :
    bristleTipInSpace n k ≠ handlePointInSpace n := by
  -- Their second coordinates differ by a strictly positive amount.
  intro h
  have hsnd := congrArg (fun x : Space ↦ (x : ℝ × ℝ).2) h
  have hgap : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹ := by
    rw [sub_pos, handleReciprocal_lt_handleReciprocal_iff]
    omega
  simp only [bristleTipInSpace, bristleTip, handlePointInSpace, handlePoint] at hsnd
  norm_num [Nat.cast_add, Nat.cast_one] at hgap hsnd
  rcases hsnd with hgap_zero | hdenominator_zero
  · linarith
  · have hdenominator : 0 < (k : ℝ) + 1 := by positivity
    exact hdenominator.ne' hdenominator_zero

/-- Helper for Exercise 25.7: a bristle tip as a point of the corresponding
punctured broom. -/
private noncomputable def bristleTipInPunctured (n k : ℕ) : PuncturedAtHandle n :=
  ⟨bristleTipInSpace n k, bristleTipInSpace_ne_handlePointInSpace n k⟩

/-- Helper for Exercise 25.7: the named punctured tip lies on its bristle. -/
private lemma bristleTipInPunctured_mem (n k : ℕ) :
    bristleTipInPunctured n k ∈ bristleInPunctured n k := by
  -- This is the right endpoint incidence of the defining segment.
  exact right_mem_segment ℝ _ _

/-- Helper for Exercise 25.7: successive handle points are distinct. -/
private lemma handlePointInSpace_succ_ne (n : ℕ) :
    handlePointInSpace (n + 1) ≠ handlePointInSpace n := by
  -- Their first coordinates are distinct reciprocal numbers.
  intro h
  have hfst := congrArg (fun x : Space ↦ (x : ℝ × ℝ).1) h
  have hlt : ((n + 2 : ℕ) : ℝ)⁻¹ < ((n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [handleReciprocal_lt_handleReciprocal_iff]
    omega
  simp [handlePointInSpace, handlePoint, add_assoc] at hfst

/-- Helper for Exercise 25.7: the next handle point as a point of the broom
punctured at the current one. -/
private noncomputable def successorInPunctured (n : ℕ) : PuncturedAtHandle n :=
  ⟨handlePointInSpace (n + 1), handlePointInSpace_succ_ne n⟩

/-- Helper for Exercise 25.7: the next handle point is not on any bristle of
the preceding fan. -/
private lemma handlePoint_succ_not_mem_bristle (n k : ℕ) :
    handlePoint (n + 1) ∉ bristle n k := by
  -- The bristle equation would give the zero-height point a positive height.
  intro hmem
  have hheight := bristle_height_eq hmem
  have hgap :
      0 < ((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 1 + 1 : ℕ) : ℝ)⁻¹ := by
    rw [sub_pos, handleReciprocal_lt_handleReciprocal_iff]
    omega
  have hpositive :
      0 < ((k + 1 : ℕ) : ℝ)⁻¹ *
        (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 1 + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  have hzero :
      ((k + 1 : ℕ) : ℝ)⁻¹ *
        (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 1 + 1 : ℕ) : ℝ)⁻¹) = 0 := by
    simpa only [handlePoint, Prod.snd, Prod.fst, Nat.cast_add, Nat.cast_one,
      add_assoc] using hheight.symm
  exact hpositive.ne' hzero

/-- Helper for Exercise 25.7: membership of one handle point in an open
connected set forces membership of its predecessor. -/
private lemma handlePointInSpace_mem_of_succ_mem {C : Set Space} (hC_open : IsOpen C)
    (hC_connected : IsConnected C) (n : ℕ)
    (hsucc : handlePointInSpace (n + 1) ∈ C) : handlePointInSpace n ∈ C := by
  -- If the predecessor were omitted, lift the connected set to the punctured
  -- broom and separate a nearby bristle tip from the successor handle point.
  by_contra hbase
  have heventually : ∀ᶠ k in atTop, bristleTipInSpace n k ∈ C :=
    (tendsto_bristleTipInSpace n) (hC_open.mem_nhds hsucc)
  obtain ⟨k, htip⟩ := heventually.exists
  have hopenMap : IsOpenMap ((↑) : PuncturedAtHandle n → Space) := by
    exact isOpen_compl_singleton.isOpenMap_subtype_val
  have hsubsetRange : C ⊆ range ((↑) : PuncturedAtHandle n → Space) := by
    intro x hx
    have hxne : x ≠ handlePointInSpace n := by
      intro hxeq
      apply hbase
      rwa [← hxeq]
    let y : PuncturedAtHandle n := ⟨x, hxne⟩
    exact ⟨y, rfl⟩
  have hlifted : IsConnected (((↑) : PuncturedAtHandle n → Space) ⁻¹' C) :=
    hC_connected.preimage_of_isOpenMap Subtype.val_injective hopenMap hsubsetRange
  have hintersects :
      ((((↑) : PuncturedAtHandle n → Space) ⁻¹' C) ∩ bristleInPunctured n k).Nonempty := by
    exact ⟨bristleTipInPunctured n k, htip, bristleTipInPunctured_mem n k⟩
  have hcontained : ((↑) : PuncturedAtHandle n → Space) ⁻¹' C ⊆
      bristleInPunctured n k :=
    hlifted.isPreconnected.subset_isClopen (isClopen_bristleInPunctured n k) hintersects
  have hsuccessor : successorInPunctured n ∈
      ((↑) : PuncturedAtHandle n → Space) ⁻¹' C := hsucc
  exact handlePoint_succ_not_mem_bristle n k (hcontained hsuccessor)

/-- Any open connected neighborhood of `p` contains every point `aₙ₊₁`. -/
theorem handlePointInSpace_mem_of_isOpen_isConnected {C : Set Space} (hC_open : IsOpen C)
    (hpoint : point ∈ C) (hC_connected : IsConnected C) (n : ℕ) :
    handlePointInSpace n ∈ C := by
  -- Openness first captures an eventual tail of the handle-point sequence;
  -- the predecessor lemma then propagates membership back to the requested index.
  have heventually : ∀ᶠ m in atTop, handlePointInSpace m ∈ C :=
    tendsto_handlePointInSpace (hC_open.mem_nhds hpoint)
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  rcases le_total N n with hNn | hnN
  · exact hN n hNn
  · exact Nat.decreasingInduction
      (fun k _ hk ↦ handlePointInSpace_mem_of_succ_mem hC_open hC_connected k hk)
      (hN N le_rfl) hnN

/-- Helper for Exercise 25.7: a point on the horizontal axis between `point`
and `handlePoint n` belongs to their segment. -/
private lemma mem_initialHandleSegment (n : ℕ) {z : ℝ × ℝ} (hx_nonneg : 0 ≤ z.1)
    (hx_le : z.1 ≤ ((n + 1 : ℕ) : ℝ)⁻¹) (hy : z.2 = 0) :
    z ∈ segment ℝ (0, 0) (handlePoint n) := by
  -- Use the normalized horizontal coordinate as the line parameter.
  let t : ℝ := z.1 / ((n + 1 : ℕ) : ℝ)⁻¹
  have hcoordinate : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have ht_nonneg : 0 ≤ t := div_nonneg hx_nonneg hcoordinate.le
  have ht_le : t ≤ 1 := (div_le_one hcoordinate).2 hx_le
  have hline : AffineMap.lineMap ((0, 0) : ℝ × ℝ) (handlePoint n) t = z := by
    ext
    · simp [AffineMap.lineMap_apply_module, handlePoint, t]
      field_simp
    · simp [AffineMap.lineMap_apply_module, handlePoint, hy]
  rw [← hline]
  exact lineMap_mem_segment ℝ _ _ ⟨ht_nonneg, ht_le⟩

/-- Helper for Exercise 25.7: later handle points lie on every earlier initial
handle segment. -/
private lemma handlePoint_mem_initialHandleSegment {n m : ℕ} (h : n ≤ m) :
    handlePoint m ∈ segment ℝ (0, 0) (handlePoint n) := by
  -- Reciprocal antitonicity supplies the required horizontal bound.
  apply mem_initialHandleSegment n
  · simp only [handlePoint]
    positivity
  · have hanti := handleReciprocal_anti h
    norm_num [handlePoint, Nat.cast_add, Nat.cast_one] at hanti ⊢
    exact hanti
  · rfl

/-- Helper for Exercise 25.7: the common origin belongs to its entire family
of bristles. -/
private lemma handlePoint_mem_all_bristles (n : ℕ) :
    handlePoint n ∈ ⋂ k : ℕ, bristle n k := by
  -- Every member of the intersection has the same left endpoint.
  exact mem_iInter.2 (fun k ↦ handlePoint_mem_bristle n k)

/-- Helper for Exercise 25.7: every individual sub-broom is connected. -/
private lemma isConnected_subBroom (n : ℕ) : IsConnected (subBroom n) := by
  -- It is a union of connected segments with a common origin.
  refine ⟨⟨handlePoint n, (mem_subBroom_iff n _).2 ⟨0, handlePoint_mem_bristle n 0⟩⟩, ?_⟩
  exact isPreconnected_iUnion
    ⟨handlePoint n, handlePoint_mem_all_bristles n⟩
    (fun k ↦ (convex_segment (handlePoint n) (bristleTip n k)).isPreconnected)

/-- Helper for Exercise 25.7: the `n`th tail consists of the initial handle up
to `aₙ₊₁` and every sub-broom based no farther from `point`. -/
private def tail (n : ℕ) : Set (ℝ × ℝ) :=
  segment ℝ (0, 0) (handlePoint n) ∪ ⋃ m : ℕ, subBroom (n + m)

/-- Helper for Exercise 25.7: the planar tail is contained in the broom. -/
private lemma tail_subset_carrier (n : ℕ) : tail n ⊆ carrier := by
  -- The initial handle lies in the full handle, while every listed fan is one
  -- of the carrier's sub-brooms.
  intro z hz
  rcases hz with hhandle | hfans
  · apply Or.inl
    have hendpoint : handlePoint n ∈ segment ℝ (0, 0) ((1, 0) : ℝ × ℝ) := by
      simpa [handlePoint] using
        (handlePoint_mem_initialHandleSegment (n := 0) (m := n) (Nat.zero_le n))
    exact (convex_segment ((0, 0) : ℝ × ℝ) (1, 0)).segment_subset
      (left_mem_segment ℝ _ _) hendpoint hhandle
  · obtain ⟨m, hm⟩ := mem_iUnion.1 hfans
    exact Or.inr (mem_iUnion.2 ⟨n + m, hm⟩)

/-- Helper for Exercise 25.7: the distinguished planar point lies in every
tail. -/
private lemma point_mem_tail (n : ℕ) : ((0, 0) : ℝ × ℝ) ∈ tail n := by
  -- It is the left endpoint of the initial handle segment.
  exact Or.inl (left_mem_segment ℝ _ _)

/-- Helper for Exercise 25.7: every planar tail is connected. -/
private lemma isConnected_tail (n : ℕ) : IsConnected (tail n) := by
  -- Join any point to `point` inside either the initial handle or the union of
  -- that handle with the one sub-broom containing the point.
  refine ⟨⟨(0, 0), point_mem_tail n⟩, isPreconnected_of_forall (0, 0) ?_⟩
  intro z hz
  rcases hz with hhandle | hfans
  · exact ⟨segment ℝ (0, 0) (handlePoint n), subset_union_left, left_mem_segment ℝ _ _,
        hhandle, (convex_segment ((0, 0) : ℝ × ℝ) (handlePoint n)).isPreconnected⟩
  · obtain ⟨m, hm⟩ := mem_iUnion.1 hfans
    let piece : Set (ℝ × ℝ) :=
      segment ℝ (0, 0) (handlePoint n) ∪ subBroom (n + m)
    have horigin_handle :
        handlePoint (n + m) ∈ segment ℝ (0, 0) (handlePoint n) :=
      handlePoint_mem_initialHandleSegment (Nat.le_add_right n m)
    have horigin_fan : handlePoint (n + m) ∈ subBroom (n + m) :=
      (mem_subBroom_iff (n + m) _).2 ⟨0, handlePoint_mem_bristle (n + m) 0⟩
    have hpiece_preconnected : IsPreconnected piece :=
      (convex_segment ((0, 0) : ℝ × ℝ) (handlePoint n)).isPreconnected.union'
        ⟨handlePoint (n + m), horigin_handle, horigin_fan⟩
        (isConnected_subBroom (n + m)).isPreconnected
    refine ⟨piece, ?_, Or.inl (left_mem_segment ℝ _ _), Or.inr hm, hpiece_preconnected⟩
    intro y hy
    rcases hy with hyhandle | hyfan
    · exact Or.inl hyhandle
    · exact Or.inr (mem_iUnion.2 ⟨m, hyfan⟩)

/-- Helper for Exercise 25.7: the `n`th tail as a subset of the broom space. -/
private def tailInSpace (n : ℕ) : Set Space :=
  ((↑) : Space → ℝ × ℝ) ⁻¹' tail n

/-- Helper for Exercise 25.7: every tail is connected in the subspace
topology of the broom. -/
private lemma isConnected_tailInSpace (n : ℕ) : IsConnected (tailInSpace n) := by
  -- The subtype inclusion is inducing and its image of the lifted tail is the
  -- planar tail itself.
  have himage : ((↑) : Space → ℝ × ℝ) '' tailInSpace n = tail n := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      exact hx
    · intro z hz
      have hcarrier := tail_subset_carrier n hz
      let x : Space := ⟨z, hcarrier⟩
      exact ⟨x, hz, rfl⟩
  refine ⟨⟨point, point_mem_tail n⟩, ?_⟩
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himage]
  exact (isConnected_tail n).isPreconnected

/-- Helper for Exercise 25.7: a carrier point whose first coordinate is below
the `n`th handle coordinate belongs to the `n`th tail. -/
private lemma mem_tail_of_fst_lt {n : ℕ} {z : ℝ × ℝ} (hz : z ∈ carrier)
    (hx : z.1 < ((n + 1 : ℕ) : ℝ)⁻¹) : z ∈ tail n := by
  -- The first-coordinate bound either shortens the horizontal handle or
  -- forces the index of the containing fan to be at least `n`.
  rcases (mem_carrier_iff z).1 hz with hhandle | ⟨m, hm⟩
  · have hcoordinates :=
      (Prod.segment_subset (𝕜 := ℝ) ((0, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)) hhandle
    have hx_nonneg : 0 ≤ z.1 := by
      have hzero_le_one : (0 : ℝ) ≤ 1 := by norm_num
      rw [segment_eq_Icc hzero_le_one] at hcoordinates
      exact hcoordinates.1.1
    have hy : z.2 = 0 := by
      simpa only [segment_same, mem_singleton_iff] using hcoordinates.2
    exact Or.inl (mem_initialHandleSegment n hx_nonneg hx.le hy)
  · obtain ⟨k, hk⟩ := (mem_subBroom_iff m z).1 hm
    have hlower := (bristle_fst_bounds hk).1
    have hnm : n ≤ m := by
      have hstrict : ((m + 2 : ℕ) : ℝ)⁻¹ < ((n + 1 : ℕ) : ℝ)⁻¹ :=
        lt_of_le_of_lt hlower hx
      rw [handleReciprocal_lt_handleReciprocal_iff] at hstrict
      omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact Or.inr (mem_iUnion.2 ⟨d, hm⟩)

/-- Helper for Exercise 25.7: every tail is itself a neighborhood of `point`. -/
private lemma tailInSpace_mem_nhds (n : ℕ) : tailInSpace n ∈ 𝓝 point := by
  -- The relatively open first-coordinate half-space below the `n`th handle
  -- coordinate is contained in the tail.
  have hopen : IsOpen {x : Space | (x : ℝ × ℝ).1 < ((n + 1 : ℕ) : ℝ)⁻¹} :=
    isOpen_lt (continuous_fst.comp continuous_subtype_val) continuous_const
  have hpoint : point ∈ {x : Space | (x : ℝ × ℝ).1 < ((n + 1 : ℕ) : ℝ)⁻¹} := by
    simp only [point, mem_setOf_eq]
    positivity
  apply mem_of_superset (hopen.mem_nhds hpoint)
  intro x hx
  exact mem_tail_of_fst_lt x.property hx

/-- Helper for Exercise 25.7: a later handle point lies in the reciprocal
closed ball determined by an earlier index. -/
private lemma handlePoint_mem_closedBall_of_le {n m : ℕ} (h : n ≤ m) :
    handlePoint m ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- The product distance is the maximum of the two coordinate distances.
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
  constructor
  · simp only [handlePoint, Real.dist_eq, sub_zero]
    have hcoordinate_nonneg : 0 ≤ (↑m + 1 : ℝ)⁻¹ := by positivity
    rw [abs_of_nonneg hcoordinate_nonneg]
    have hanti := handleReciprocal_anti h
    norm_num [Nat.cast_add, Nat.cast_one] at hanti ⊢
    exact hanti
  · simp only [handlePoint, dist_zero_right, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one]
    rw [abs_zero]
    positivity

/-- Helper for Exercise 25.7: every bristle tip in a later fan lies in the
reciprocal closed ball determined by an earlier index. -/
private lemma bristleTip_mem_closedBall_of_le {n m : ℕ} (k : ℕ) (h : n ≤ m) :
    bristleTip m k ∈
      Metric.closedBall ((0, 0) : ℝ × ℝ) ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- Both nonnegative coordinates are bounded by the earlier handle coordinate.
  have hbeta : ((m + 2 : ℕ) : ℝ)⁻¹ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ :=
    handleReciprocal_anti (h.trans (Nat.le_succ m))
  have hgap_nonneg :
      0 ≤ ((m + 1 : ℕ) : ℝ)⁻¹ - ((m + 2 : ℕ) : ℝ)⁻¹ := by
    rw [sub_nonneg]
    exact handleReciprocal_anti (Nat.le_succ m)
  have hdenominator : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    norm_cast
    omega
  have hheight_nonneg :
      0 ≤ (((m + 1 : ℕ) : ℝ)⁻¹ - ((m + 2 : ℕ) : ℝ)⁻¹) /
        ((k + 1 : ℕ) : ℝ) := by
    have hdenominator_nonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) := by positivity
    exact div_nonneg hgap_nonneg hdenominator_nonneg
  have hheight :
      (((m + 1 : ℕ) : ℝ)⁻¹ - ((m + 2 : ℕ) : ℝ)⁻¹) /
          ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
    calc
      _ ≤ ((m + 1 : ℕ) : ℝ)⁻¹ - ((m + 2 : ℕ) : ℝ)⁻¹ :=
        div_le_self hgap_nonneg hdenominator
      _ ≤ ((m + 1 : ℕ) : ℝ)⁻¹ := by
        have hnext_nonneg : 0 ≤ ((m + 2 : ℕ) : ℝ)⁻¹ := by positivity
        exact sub_le_self _ hnext_nonneg
      _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := handleReciprocal_anti h
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
  constructor
  · simp only [bristleTip, Real.dist_eq, sub_zero]
    have hbeta_nonneg : 0 ≤ (↑m + 2 : ℝ)⁻¹ := by positivity
    rw [abs_of_nonneg hbeta_nonneg]
    norm_num [Nat.cast_add, Nat.cast_one] at hbeta ⊢
    exact hbeta
  · simp only [bristleTip, Real.dist_eq, sub_zero]
    norm_num [Nat.cast_add, Nat.cast_one] at hheight_nonneg hheight ⊢
    rw [abs_of_nonneg hheight_nonneg]
    exact hheight

/-- Helper for Exercise 25.7: the `n`th planar tail lies in the reciprocal
closed ball centered at `point`. -/
private lemma tail_subset_closedBall (n : ℕ) :
    tail n ⊆ Metric.closedBall ((0, 0) : ℝ × ℝ) ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- Convexity of the ball propagates the endpoint bounds along every segment.
  intro z hz
  rcases hz with hhandle | hfans
  · have hradius_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    exact (convex_closedBall ((0, 0) : ℝ × ℝ) ((n + 1 : ℕ) : ℝ)⁻¹).segment_subset
      (Metric.mem_closedBall_self hradius_nonneg)
      (handlePoint_mem_closedBall_of_le le_rfl) hhandle
  · obtain ⟨m, hm⟩ := mem_iUnion.1 hfans
    obtain ⟨k, hk⟩ := (mem_subBroom_iff (n + m) z).1 hm
    exact (convex_closedBall ((0, 0) : ℝ × ℝ) ((n + 1 : ℕ) : ℝ)⁻¹).segment_subset
      (handlePoint_mem_closedBall_of_le (Nat.le_add_right n m))
      (bristleTip_mem_closedBall_of_le k (Nat.le_add_right n m)) hk

/-- Helper for Exercise 25.7: the lifted `n`th tail lies in the corresponding
closed ball of `Space`. -/
private lemma tailInSpace_subset_closedBall (n : ℕ) :
    tailInSpace n ⊆ Metric.closedBall point ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- Subtype distances are inherited from the ambient plane.
  intro x hx
  have hambient := tail_subset_closedBall n hx
  simpa only [Metric.mem_closedBall, point, Subtype.dist_eq] using hambient

/-- Exercise 25.7 (1): The infinite broom is not locally connected at `p`. -/
theorem notLocallyConnectedAt : ¬ IsLocallyConnectedAt point := by
  -- Exclude the first handle point; local connectedness would supply an open
  -- connected neighborhood inside that complement, contradicting the hint.
  intro hlocal
  have hpoint_ne : point ≠ handlePointInSpace 0 := by
    intro h
    have hfst := congrArg (fun x : Space ↦ (x : ℝ × ℝ).1) h
    norm_num [point, handlePointInSpace, handlePoint] at hfst
  have hcompl : {handlePointInSpace 0}ᶜ ∈ 𝓝 point :=
    isOpen_compl_singleton.mem_nhds hpoint_ne
  rw [isLocallyConnectedAt_iff_connected_neighborhoods] at hlocal
  obtain ⟨V, hVsub, hVopen, hpointV, hVconnected⟩ := hlocal _ hcompl
  have hhandle :=
    handlePointInSpace_mem_of_isOpen_isConnected hVopen hpointV hVconnected 0
  exact (hVsub hhandle) (mem_singleton _)

/-- Exercise 25.7 (2): The infinite broom is weakly locally connected at `p`:
every neighborhood of `p` contains a connected set that is itself a
neighborhood of `p`. -/
theorem weaklyLocallyConnectedAt : WeaklyLocallyConnectedAt point := by
  -- Choose a sufficiently small reciprocal closed ball inside the given
  -- neighborhood, then use the connected tail at the same index.
  rw [weaklyLocallyConnectedAt_iff]
  intro U hU
  obtain ⟨n, -, hball⟩ := Metric.nhds_basis_closedBall_inv_nat_succ.mem_iff.1 hU
  refine ⟨tailInSpace n, tailInSpace_mem_nhds n, isConnected_tailInSpace n, ?_⟩
  intro x hx
  apply hball
  have htail := tailInSpace_subset_closedBall n hx
  simpa only [one_div, Nat.cast_add, Nat.cast_one] using htail

end InfiniteBroom
