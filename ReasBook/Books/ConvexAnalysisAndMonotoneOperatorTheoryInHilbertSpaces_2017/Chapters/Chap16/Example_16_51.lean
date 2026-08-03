import Mathlib
import BauschkeLean.Chap06.Proposition_6_44
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Example_16_13

open ERealFunction
open Set
open scoped EuclideanSpace InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "cL" => (!₂[(-1 : ℝ), 0] : ℝ²)
local notation "cR" => (!₂[(1 : ℝ), 0] : ℝ²)
local notation "C" => Metric.closedBall cL 1
local notation "D" => Metric.closedBall cR 1

/-- Helper for Example 16.51: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Example 16.51: a vector in `ℝ²` is determined by its two coordinates. -/
private theorem euclideanSpace_fin2_eq (x : ℝ²) : x = !₂[x 0, x 1] := by
  ext i
  fin_cases i <;> simp

/-- Helper for Example 16.51: the squared norm in `ℝ²` is the sum of the coordinate squares. -/
private theorem norm_sq_eq_coord_sq_sum (x : ℝ²) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [euclideanSpace_fin2_eq x]
  norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- Helper for Example 16.51: membership in the left closed unit ball is the expected coordinate
inequality. -/
private theorem mem_left_closed_unit_ball_iff (x : ℝ²) :
    x ∈ C ↔ (x 0 + 1) ^ 2 + x 1 ^ 2 ≤ 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hcoord :
      ‖x - cL‖ ^ 2 = (x 0 + 1) ^ 2 + x 1 ^ 2 := by
    calc
      ‖x - cL‖ ^ 2 = (x - cL) 0 ^ 2 + (x - cL) 1 ^ 2 := norm_sq_eq_coord_sq_sum (x - cL)
      _ = (x 0 + 1) ^ 2 + x 1 ^ 2 := by simp
  constructor
  · intro hx
    have hsq : ‖x - cL‖ ^ 2 ≤ 1 := by
      have hnonneg : 0 ≤ ‖x - cL‖ := norm_nonneg (x - cL)
      nlinarith
    rw [hcoord] at hsq
    exact hsq
  · intro hx
    have hsq : ‖x - cL‖ ^ 2 ≤ 1 := by
      rw [hcoord]
      exact hx
    have hnonneg : 0 ≤ ‖x - cL‖ := norm_nonneg (x - cL)
    nlinarith

/-- Helper for Example 16.51: membership in the right closed unit ball is the expected coordinate
inequality. -/
private theorem mem_right_closed_unit_ball_iff (x : ℝ²) :
    x ∈ D ↔ (x 0 - 1) ^ 2 + x 1 ^ 2 ≤ 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hcoord :
      ‖x - cR‖ ^ 2 = (x 0 - 1) ^ 2 + x 1 ^ 2 := by
    calc
      ‖x - cR‖ ^ 2 = (x - cR) 0 ^ 2 + (x - cR) 1 ^ 2 := norm_sq_eq_coord_sq_sum (x - cR)
      _ = (x 0 - 1) ^ 2 + x 1 ^ 2 := by simp
  constructor
  · intro hx
    have hsq : ‖x - cR‖ ^ 2 ≤ 1 := by
      have hnonneg : 0 ≤ ‖x - cR‖ := norm_nonneg (x - cR)
      nlinarith
    rw [hcoord] at hsq
    exact hsq
  · intro hx
    have hsq : ‖x - cR‖ ^ 2 ≤ 1 := by
      rw [hcoord]
      exact hx
    have hnonneg : 0 ≤ ‖x - cR‖ := norm_nonneg (x - cR)
    nlinarith

/-- Helper for Example 16.51: the origin belongs to the left closed unit ball. -/
private theorem origin_mem_left_closed_unit_ball : (0 : ℝ²) ∈ C := by
  rw [mem_left_closed_unit_ball_iff]
  norm_num

/-- Helper for Example 16.51: the origin belongs to the right closed unit ball. -/
private theorem origin_mem_right_closed_unit_ball : (0 : ℝ²) ∈ D := by
  rw [mem_right_closed_unit_ball_iff]
  norm_num

/-- Helper for Example 16.51: subtracting the singleton `{0}` leaves a set unchanged. -/
private theorem sub_singleton_origin_eq_self {S : Set ℝ²} :
    S - ({0} : Set ℝ²) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, hxyz⟩
    have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
    subst hz0
    have hyx : y = x := by
      simpa using hxyz
    simpa [hyx] using hy
  · intro hx
    refine ⟨x, hx, 0, ?_, ?_⟩
    · simp
    · simp

/-- Helper for Example 16.51: the left center has inner product `-u 0` with `u`. -/
private theorem left_center_inner (u : ℝ²) : ⟪cL, u⟫_ℝ = -u 0 := by
  rw [euclideanSpace_fin2_eq u]
  norm_num [PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_mul]

/-- Helper for Example 16.51: the right center has inner product `u 0` with `u`. -/
private theorem right_center_inner (u : ℝ²) : ⟪cR, u⟫_ℝ = u 0 := by
  rw [euclideanSpace_fin2_eq u]
  norm_num [PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_mul]

/-- Helper for Example 16.51: the normalized vector has inner product `‖u‖` with `u`. -/
private theorem normalized_inner_eq_norm {u : ℝ²} (hu : u ≠ 0) :
    ⟪‖u‖⁻¹ • u, u⟫_ℝ = ‖u‖ := by
  have hnorm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  calc
    ⟪‖u‖⁻¹ • u, u⟫_ℝ = ‖u‖⁻¹ * ‖u‖ ^ 2 := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    _ = (‖u‖⁻¹ * ‖u‖) * ‖u‖ := by ring
    _ = ‖u‖ := by rw [inv_mul_cancel₀ hnorm_ne, one_mul]

/-- Helper for Example 16.51: the normalized nonzero vector has norm `1`. -/
private theorem normalized_norm_eq_one {u : ℝ²} (hu : u ≠ 0) :
    ‖‖u‖⁻¹ • u‖ = 1 := by
  have hnorm_ne : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hinv_nonneg : 0 ≤ ‖u‖⁻¹ := inv_nonneg.mpr (norm_nonneg u)
  calc
    ‖‖u‖⁻¹ • u‖ = ‖‖u‖⁻¹‖ * ‖u‖ := by rw [norm_smul]
    _ = ‖u‖⁻¹ * ‖u‖ := by rw [Real.norm_of_nonneg hinv_nonneg]
    _ = 1 := by rw [inv_mul_cancel₀ hnorm_ne]

/-- Helper for Example 16.51: if the second coordinate vanishes and the first is nonnegative, then
the norm is the first coordinate. -/
private theorem norm_eq_firstCoord_of_second_eq_zero_of_first_nonneg {u : ℝ²}
    (hu0 : 0 ≤ u 0) (hu1 : u 1 = 0) :
    ‖u‖ = u 0 := by
  have hsq : ‖u‖ ^ 2 = (u 0) ^ 2 := by
    rw [norm_sq_eq_coord_sq_sum u, hu1]
    ring
  have hnonneg : 0 ≤ ‖u‖ := norm_nonneg u
  nlinarith

/-- Helper for Example 16.51: if the second coordinate vanishes and the first is nonpositive, then
the norm is the negated first coordinate. -/
private theorem norm_eq_neg_firstCoord_of_second_eq_zero_of_first_nonpos {u : ℝ²}
    (hu0 : u 0 ≤ 0) (hu1 : u 1 = 0) :
    ‖u‖ = -u 0 := by
  have hsq : ‖u‖ ^ 2 = (-u 0) ^ 2 := by
    rw [norm_sq_eq_coord_sq_sum u, hu1]
    ring
  have hnonneg : 0 ≤ ‖u‖ := norm_nonneg u
  nlinarith

-- Proof sketch: expand membership in the two closed balls as distance inequalities to `(-1,0)`
-- and `(1,0)`. The two inequalities force both coordinates to vanish, and conversely the origin
-- satisfies both.
/-- The two opposite closed unit balls meet exactly at the origin. -/
theorem leftRightClosedUnitBall_inter_eq_singleton_origin :
    C ∩ D = ({0} : Set ℝ²) := by
  ext x
  constructor
  · rintro ⟨hxC, hxD⟩
    -- Reduce the two ball constraints to coordinate inequalities and solve them simultaneously.
    have hC : (x 0 + 1) ^ 2 + x 1 ^ 2 ≤ 1 := (mem_left_closed_unit_ball_iff x).1 hxC
    have hD : (x 0 - 1) ^ 2 + x 1 ^ 2 ≤ 1 := (mem_right_closed_unit_ball_iff x).1 hxD
    have hx0 : x 0 = 0 := by
      nlinarith
    have hx1 : x 1 = 0 := by
      nlinarith [hC, hD, hx0]
    ext i
    fin_cases i <;> simp [hx0, hx1]
  · intro hx
    -- The origin satisfies both distance bounds with equality.
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨origin_mem_left_closed_unit_ball, origin_mem_right_closed_unit_ball⟩

-- Proof sketch: `effectiveDomain_indicator` identifies each indicator domain with its underlying
-- set, so the previous intersection computation gives the common effective domain immediately.
/-- The effective domains of the two closed-ball indicators intersect exactly at the origin. -/
theorem effectiveDomain_closedBallIndicators_inter_eq_singleton_origin :
    effectiveDomain (ι[C]) ∩ effectiveDomain (ι[D]) = ({0} : Set ℝ²) := by
  -- Rewrite both effective domains as the underlying balls.
  simpa [effectiveDomain_indicator] using leftRightClosedUnitBall_inter_eq_singleton_origin

/-- Helper for Example 16.51: the sum of the two opposite closed-ball indicators is the indicator
of the singleton `{0}`. -/
private theorem opposite_closed_ball_indicators_add_eq_indicator_singleton_origin :
    ι[C] + ι[D] = ι[({0} : Set ℝ²)] := by
  funext x
  apply Subtype.ext
  change ((ι[C] x : EReal) + (ι[D] x : EReal) = (ι[({0} : Set ℝ²)] x : EReal))
  -- Both sides are pointwise `0` at the common point and `⊤` elsewhere.
  by_cases hxC : x ∈ C
  · by_cases hxD : x ∈ D
    · have hx0 : x = 0 := by
        have hxCD : x ∈ C ∩ D := ⟨hxC, hxD⟩
        have hxSingleton : x ∈ ({0} : Set ℝ²) := by
          simpa [leftRightClosedUnitBall_inter_eq_singleton_origin] using hxCD
        simpa using hxSingleton
      subst x
      have hnorm_cL : ‖cL‖ ≤ 1 := by
        have hsq : ‖cL‖ ^ 2 = 1 := by
          rw [norm_sq_eq_coord_sq_sum cL]
          norm_num
        have hnonneg : 0 ≤ ‖cL‖ := norm_nonneg cL
        nlinarith
      have hnorm_cR : ‖cR‖ ≤ 1 := by
        have hsq : ‖cR‖ ^ 2 = 1 := by
          rw [norm_sq_eq_coord_sq_sum cR]
          norm_num
        have hnonneg : 0 ≤ ‖cR‖ := norm_nonneg cR
        nlinarith
      have hleft : (ι[C] (0 : ℝ²) : EReal) = 0 := by
        simp [ERealFunction.indicator, hnorm_cL]
      have hright : (ι[D] (0 : ℝ²) : EReal) = 0 := by
        simp [ERealFunction.indicator, hnorm_cR]
      have hsingle : (ι[({0} : Set ℝ²)] (0 : ℝ²) : EReal) = 0 := by
        simp [ERealFunction.indicator]
      rw [hleft, hright, hsingle]
      norm_num
    · have hx0 : x ∉ ({0} : Set ℝ²) := by
        intro hx0
        have hxOrigin : x = 0 := Set.mem_singleton_iff.mp hx0
        subst hxOrigin
        exact hxD origin_mem_right_closed_unit_ball
      simp [indicator_apply, hxC, hxD, hx0]
  · by_cases hxD : x ∈ D
    · have hx0 : x ∉ ({0} : Set ℝ²) := by
        intro hx0
        have hxOrigin : x = 0 := Set.mem_singleton_iff.mp hx0
        subst hxOrigin
        exact hxC origin_mem_left_closed_unit_ball
      simp [indicator_apply, hxC, hxD, hx0]
    · have hx0 : x ∉ ({0} : Set ℝ²) := by
        intro hx0
        have hxOrigin : x = 0 := Set.mem_singleton_iff.mp hx0
        subst hxOrigin
        exact hxC origin_mem_left_closed_unit_ball
      simp [indicator_apply, hxC, hxD, hx0]

-- Proof sketch: at the common boundary point `0`, the pointwise sum `ι[C] + ι[D]` vanishes only
-- at the origin and is `⊤` elsewhere, so its subgradient inequality reduces to the indicator of
-- the singleton `{0}`. The subdifferential of the singleton indicator at `0` is all of `ℝ²`.
/-- The subdifferential of `ι[C] + ι[D]` at the origin is all of `ℝ²`. -/
theorem subdifferential_oppositeClosedBallIndicatorSum_at_origin :
    (∂ (ι[C] + ι[D])) (0 : ℝ²) = (univ : Set ℝ²) := by
  have h0Singleton : (0 : ℝ²) ∈ ({0} : Set ℝ²) := by
    simp
  have hsubd_singleton : ∂ ι[({0} : Set ℝ²)] = N[({0} : Set ℝ²)] :=
    subdifferential_setIndicator_eq_normalCone ({0} : Set ℝ²) ⟨0, h0Singleton⟩
  have hsub_translate :
      (({0} : Set ℝ²) - ({(0 : ℝ²)} : Set ℝ²)) = ({0} : Set ℝ²) := by
    exact sub_singleton_origin_eq_self
  -- Collapse the sum to the singleton indicator, then compute the singleton normal cone.
  calc
    (∂ (ι[C] + ι[D])) (0 : ℝ²) = (∂ ι[({0} : Set ℝ²)]) (0 : ℝ²) := by
      rw [opposite_closed_ball_indicators_add_eq_indicator_singleton_origin]
    _ = N[({0} : Set ℝ²)] (0 : ℝ²) := by
      simpa using congrFun hsubd_singleton (0 : ℝ²)
    _ = (univ : Set ℝ²) := by
      rw [Set.normalCone_eq_polarCone_translate_of_mem h0Singleton, hsub_translate]
      exact Set.polarCone_singleton_zero_eq_univ

/-- Helper for Example 16.51: at the origin, the normal cone of the left closed unit ball is the
nonnegative horizontal ray. -/
private theorem normalCone_left_closed_unit_ball_at_origin_eq_positive_horizontal_ray :
    N[C] (0 : ℝ²) = {u : ℝ² | 0 ≤ u 0 ∧ u 1 = 0} := by
  have h0C : (0 : ℝ²) ∈ C := origin_mem_left_closed_unit_ball
  ext u
  constructor
  · intro hu
    rw [Set.normalCone_eq_polarCone_translate_of_mem h0C,
      sub_singleton_origin_eq_self,
      Set.mem_polarCone_iff_forall_inner_nonpos] at hu
    by_cases hu_zero : u = 0
    · subst hu_zero
      simp
    · -- Test the defining inequality at the extremal boundary point in direction `u`.
      have hy_mem :
          cL + ‖u‖⁻¹ • u ∈ C := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc
          ‖(cL + ‖u‖⁻¹ • u) - cL‖ = ‖‖u‖⁻¹ • u‖ := by simp
          _ = 1 := normalized_norm_eq_one hu_zero
          _ ≤ 1 := by norm_num
      have htest : ⟪cL + ‖u‖⁻¹ • u, u⟫_ℝ ≤ 0 := hu _ hy_mem
      have hbound : -u 0 + ‖u‖ ≤ 0 := by
        calc
          -u 0 + ‖u‖ = ⟪cL, u⟫_ℝ + ⟪‖u‖⁻¹ • u, u⟫_ℝ := by
            rw [left_center_inner, normalized_inner_eq_norm hu_zero]
          _ = ⟪cL + ‖u‖⁻¹ • u, u⟫_ℝ := by rw [inner_add_left]
          _ ≤ 0 := htest
      have hnorm_le : ‖u‖ ≤ u 0 := by
        linarith [hbound]
      have hu0_nonneg : 0 ≤ u 0 := by
        have hnorm_nonneg : 0 ≤ ‖u‖ := norm_nonneg u
        exact le_trans hnorm_nonneg hnorm_le
      have hu1_zero : u 1 = 0 := by
        have hsq_norm : ‖u‖ ^ 2 ≤ (u 0) ^ 2 := by
          have hmul :=
            mul_le_mul hnorm_le hnorm_le (norm_nonneg u) hu0_nonneg
          simpa [pow_two] using hmul
        have hsq :
            (u 0) ^ 2 + (u 1) ^ 2 ≤ (u 0) ^ 2 := by
          calc
            (u 0) ^ 2 + (u 1) ^ 2 = ‖u‖ ^ 2 := by
              rw [← norm_sq_eq_coord_sq_sum u]
            _ ≤ (u 0) ^ 2 := hsq_norm
        have hu1_sq_nonpos : (u 1) ^ 2 ≤ 0 := by
          nlinarith
        have hu1_sq_nonneg : 0 ≤ (u 1) ^ 2 := sq_nonneg (u 1)
        nlinarith
      exact ⟨hu0_nonneg, hu1_zero⟩
  · rintro ⟨hu0, hu1⟩
    rw [Set.normalCone_eq_polarCone_translate_of_mem h0C,
      sub_singleton_origin_eq_self,
      Set.mem_polarCone_iff_forall_inner_nonpos]
    have hnorm_u : ‖u‖ = u 0 :=
      norm_eq_firstCoord_of_second_eq_zero_of_first_nonneg hu0 hu1
    intro y hy
    -- Rewrite `y` relative to the center and estimate the translated term by Cauchy--Schwarz.
    have hy_shift_le : ‖y - cL‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hshift_inner : ⟪y - cL, u⟫_ℝ ≤ ‖u‖ := by
      have hinner_le : ⟪y - cL, u⟫_ℝ ≤ ‖y - cL‖ * ‖u‖ := by
        simpa using real_inner_le_norm (y - cL) u
      have hnorm_nonneg : 0 ≤ ‖u‖ := norm_nonneg u
      nlinarith
    have hy_decomp : y = cL + (y - cL) := by
      abel
    have hy_shift_eq : cL + (y - cL) - cL = y - cL := by
      abel
    have hinner_decomp : ⟪y, u⟫_ℝ = ⟪cL, u⟫_ℝ + ⟪y - cL, u⟫_ℝ := by
      rw [hy_decomp, inner_add_left]
      rw [hy_shift_eq]
    rw [hinner_decomp, left_center_inner]
    have hzero : -u 0 + ‖u‖ = 0 := by
      rw [hnorm_u]
      ring
    linarith

/-- Helper for Example 16.51: at the origin, the normal cone of the right closed unit ball is the
nonpositive horizontal ray. -/
private theorem normalCone_right_closed_unit_ball_at_origin_eq_negative_horizontal_ray :
    N[D] (0 : ℝ²) = {u : ℝ² | u 0 ≤ 0 ∧ u 1 = 0} := by
  have h0D : (0 : ℝ²) ∈ D := origin_mem_right_closed_unit_ball
  ext u
  constructor
  · intro hu
    rw [Set.normalCone_eq_polarCone_translate_of_mem h0D,
      sub_singleton_origin_eq_self,
      Set.mem_polarCone_iff_forall_inner_nonpos] at hu
    by_cases hu_zero : u = 0
    · subst hu_zero
      simp
    · -- Test the defining inequality at the extremal boundary point in direction `u`.
      have hy_mem :
          cR + ‖u‖⁻¹ • u ∈ D := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc
          ‖(cR + ‖u‖⁻¹ • u) - cR‖ = ‖‖u‖⁻¹ • u‖ := by simp
          _ = 1 := normalized_norm_eq_one hu_zero
          _ ≤ 1 := by norm_num
      have htest : ⟪cR + ‖u‖⁻¹ • u, u⟫_ℝ ≤ 0 := hu _ hy_mem
      have hbound : u 0 + ‖u‖ ≤ 0 := by
        calc
          u 0 + ‖u‖ = ⟪cR, u⟫_ℝ + ⟪‖u‖⁻¹ • u, u⟫_ℝ := by
            rw [right_center_inner, normalized_inner_eq_norm hu_zero]
          _ = ⟪cR + ‖u‖⁻¹ • u, u⟫_ℝ := by rw [inner_add_left]
          _ ≤ 0 := htest
      have hnorm_le : ‖u‖ ≤ -u 0 := by
        linarith [hbound]
      have hu0_nonpos : u 0 ≤ 0 := by
        have hnorm_nonneg : 0 ≤ ‖u‖ := norm_nonneg u
        linarith
      have hu1_zero : u 1 = 0 := by
        have hu0_neg_nonneg : 0 ≤ -u 0 := by
          linarith
        have hsq_norm : ‖u‖ ^ 2 ≤ (-u 0) ^ 2 := by
          have hmul :=
            mul_le_mul hnorm_le hnorm_le (norm_nonneg u) hu0_neg_nonneg
          simpa [pow_two] using hmul
        have hsq :
            (u 0) ^ 2 + (u 1) ^ 2 ≤ (u 0) ^ 2 := by
          calc
            (u 0) ^ 2 + (u 1) ^ 2 = ‖u‖ ^ 2 := by
              rw [← norm_sq_eq_coord_sq_sum u]
            _ ≤ (-u 0) ^ 2 := hsq_norm
            _ = (u 0) ^ 2 := by ring
        have hu1_sq_nonpos : (u 1) ^ 2 ≤ 0 := by
          nlinarith
        have hu1_sq_nonneg : 0 ≤ (u 1) ^ 2 := sq_nonneg (u 1)
        nlinarith
      exact ⟨hu0_nonpos, hu1_zero⟩
  · rintro ⟨hu0, hu1⟩
    rw [Set.normalCone_eq_polarCone_translate_of_mem h0D,
      sub_singleton_origin_eq_self,
      Set.mem_polarCone_iff_forall_inner_nonpos]
    have hnorm_u : ‖u‖ = -u 0 :=
      norm_eq_neg_firstCoord_of_second_eq_zero_of_first_nonpos hu0 hu1
    intro y hy
    -- Rewrite `y` relative to the center and estimate the translated term by Cauchy--Schwarz.
    have hy_shift_le : ‖y - cR‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hshift_inner : ⟪y - cR, u⟫_ℝ ≤ ‖u‖ := by
      have hinner_le : ⟪y - cR, u⟫_ℝ ≤ ‖y - cR‖ * ‖u‖ := by
        simpa using real_inner_le_norm (y - cR) u
      have hnorm_nonneg : 0 ≤ ‖u‖ := norm_nonneg u
      nlinarith
    have hy_decomp : y = cR + (y - cR) := by
      abel
    have hy_shift_eq : cR + (y - cR) - cR = y - cR := by
      abel
    have hinner_decomp : ⟪y, u⟫_ℝ = ⟪cR, u⟫_ℝ + ⟪y - cR, u⟫_ℝ := by
      rw [hy_decomp, inner_add_left]
      rw [hy_shift_eq]
    rw [hinner_decomp, right_center_inner]
    have hzero : u 0 + ‖u‖ = 0 := by
      rw [hnorm_u]
      ring
    linarith

-- Proof sketch: the canonical bridge `subdifferential_setIndicator_eq_normalCone` identifies each
-- indicator subdifferential with the corresponding normal cone. At the origin, the left and right
-- closed balls have outward normals on the positive and negative horizontal rays, whose pointwise
-- sum is exactly the horizontal axis.
/-- The sum of the two indicator subdifferentials at the origin is the horizontal axis. -/
theorem sum_subdifferential_closedBallIndicators_at_origin :
    (∂ ι[C]) (0 : ℝ²) + (∂ ι[D]) (0 : ℝ²) = {u : ℝ² | u 1 = 0} := by
  have hsubdC : ∂ ι[C] = N[C] :=
    subdifferential_setIndicator_eq_normalCone C ⟨0, origin_mem_left_closed_unit_ball⟩
  have hsubdD : ∂ ι[D] = N[D] :=
    subdifferential_setIndicator_eq_normalCone D ⟨0, origin_mem_right_closed_unit_ball⟩
  -- Rewrite both subdifferentials as the explicit normal rays and sum them coordinatewise.
  calc
    (∂ ι[C]) (0 : ℝ²) + (∂ ι[D]) (0 : ℝ²) = N[C] (0 : ℝ²) + N[D] (0 : ℝ²) := by
      rw [congrFun hsubdC (0 : ℝ²), congrFun hsubdD (0 : ℝ²)]
    _ = {u : ℝ² | u 1 = 0} := by
      rw [normalCone_left_closed_unit_ball_at_origin_eq_positive_horizontal_ray,
        normalCone_right_closed_unit_ball_at_origin_eq_negative_horizontal_ray]
      ext u
      constructor
      · rintro ⟨uL, huL, uR, huR, rfl⟩
        rcases huL with ⟨huL0, huL1⟩
        rcases huR with ⟨huR0, huR1⟩
        simp [huL1, huR1]
      · intro hu
        by_cases hu0 : 0 ≤ u 0
        · refine ⟨u, ?_, 0, ?_, ?_⟩
          · exact ⟨hu0, hu⟩
          · simp
          · simp
        · have hu0' : u 0 ≤ 0 := by
            linarith
          refine ⟨0, ?_, u, ?_, ?_⟩
          · simp
          · exact ⟨hu0', hu⟩
          · simp

-- Proof sketch: use the two explicit descriptions above: the left-hand side is `univ`,
-- whereas the right-hand side is `{u | u 1 = 0}`, a proper subset of `ℝ²`.
/-- Example 16 51: for the closed unit balls centered at `(-1,0)` and `(1,0)` in `ℝ²`, the
subdifferential of `ι[C] + ι[D]` at the origin is not the sum of the subdifferentials of `ι[C]`
and `ι[D]`. -/
theorem subdifferential_oppositeClosedBallIndicatorSum_at_origin_ne_sum_subdifferentials :
    (∂ (ι[C] + ι[D])) (0 : ℝ²) ≠
      (∂ ι[C]) (0 : ℝ²) + (∂ ι[D]) (0 : ℝ²) := by
  -- The witness `(0,1)` belongs to `univ` but not to the horizontal axis.
  rw [subdifferential_oppositeClosedBallIndicatorSum_at_origin,
    sum_subdifferential_closedBallIndicators_at_origin]
  intro hEq
  have hwitness_mem_univ : (!₂[(0 : ℝ), 1] : ℝ²) ∈ (univ : Set ℝ²) := by
    simp
  have hmem :
      (!₂[(0 : ℝ), 1] : ℝ²) ∈ ({u : ℝ² | u 1 = 0} : Set ℝ²) := by
    have hEq_mem := congrArg (fun S : Set ℝ² ↦ (!₂[(0 : ℝ), 1] : ℝ²) ∈ S) hEq
    simpa using hEq_mem.mp hwitness_mem_univ
  simp at hmem

end

end ERealFunction
