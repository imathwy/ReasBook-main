import BauschkeLean.Chap22.Definition_22_1
import Mathlib.Analysis.Convex.Segment

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic recall: `lean_leansearch` only surfaced generic segment/convex API, not a canonical
-- monotone-operator theorem for this item. Local Chapter 22 precedent fixes the owners
-- `SetValuedOperator.IsMonotone` and `SetValuedOperator.IsParamonotone`, so the source statement is
-- recorded directly with `openSegment ℝ x y` for the textbook notation `|x, y|`.

/-- Helper for Proposition 22.10: swapping the order of the second difference negates the
corresponding pairing. -/
private theorem inner_sub_swap (x y u v : H) :
    ⟪x - y, u - v⟫_ℝ = -⟪x - y, v - u⟫_ℝ := by
  -- Expand both differences in the right slot and collect the resulting real terms.
  rw [inner_sub_right, inner_sub_right]
  ring

/-- Helper for Proposition 22.10: the pairing vanishes exactly when the swapped pairing vanishes.
-/
private theorem inner_sub_swap_eq_zero_iff (x y u v : H) :
    ⟪x - y, u - v⟫_ℝ = 0 ↔ ⟪x - y, v - u⟫_ℝ = 0 := by
  constructor
  · intro hzero
    -- The sign-change formula reduces the swapped pairing to the same zero scalar.
    have hswap := inner_sub_swap x y u v
    nlinarith
  · intro hzero
    -- Reuse the same sign-change formula with the swapped arguments.
    have hswap := inner_sub_swap x y v u
    nlinarith

/-- Helper for Proposition 22.10: orthogonality to `x - y` transfers to the left segment
displacement `x - lineMap x y t`. -/
private theorem inner_eq_zero_left_vsub_lineMap
    {x y d : H} {t : ℝ} (h : ⟪x - y, d⟫_ℝ = 0) :
    ⟪x - AffineMap.lineMap x y t, d⟫_ℝ = 0 := by
  -- Normalize the segment displacement to a scalar multiple of `x - y`.
  calc
    ⟪x - AffineMap.lineMap x y t, d⟫_ℝ = ⟪t • (x - y), d⟫_ℝ := by
      rw [show x - AffineMap.lineMap x y t = t • (x - y) by
        simpa using (AffineMap.left_vsub_lineMap x y t : x - AffineMap.lineMap x y t = _)]
    _ = t * ⟪x - y, d⟫_ℝ := by rw [real_inner_smul_left]
    _ = 0 := by simp [h]

/-- Helper for Proposition 22.10: orthogonality to `x - y` transfers to the right segment
displacement `lineMap x y t - y`. -/
private theorem inner_eq_zero_lineMap_vsub_right
    {x y d : H} {t : ℝ} (h : ⟪x - y, d⟫_ℝ = 0) :
    ⟪AffineMap.lineMap x y t - y, d⟫_ℝ = 0 := by
  -- Normalize the segment displacement to a scalar multiple of `x - y`.
  calc
    ⟪AffineMap.lineMap x y t - y, d⟫_ℝ = ⟪(1 - t) • (x - y), d⟫_ℝ := by
      rw [show AffineMap.lineMap x y t - y = (1 - t) • (x - y) by
        simpa using (AffineMap.lineMap_vsub_right x y t : AffineMap.lineMap x y t - y = _)]
    _ = (1 - t) * ⟪x - y, d⟫_ℝ := by rw [real_inner_smul_left]
    _ = 0 := by simp [h]

/-- Helper for Proposition 22.10: if `A : H → 2^H` is monotone, `u ∈ A x ∩ A y`, and
`z ∈ openSegment ℝ x y`, then every value of `A z` has zero inner product with `x - y` after
subtracting `u`; equivalently, `A z` lies in the affine hyperplane through `u` orthogonal to
`x - y`. The source-side hypotheses `x, y ∈ A.dom`, `z ∈ A.dom`, and `x ≠ y` are redundant for
this subset statement. -/
theorem subset_zeroInner_of_mem_openSegment_of_common_value
    {A : SetValuedOperator H H} (hA : A.IsMonotone)
    {x y z u : H}
    (hu : u ∈ A x ∩ A y) (hzseg : z ∈ openSegment ℝ x y) :
    A z ⊆ {v : H | ⟪x - y, v - u⟫_ℝ = 0} := by
  rw [openSegment_eq_image_lineMap] at hzseg
  rcases hzseg with ⟨t, ht, htz⟩
  subst z
  intro v hv
  have huv_nonneg : 0 ≤ ⟪x - AffineMap.lineMap x y t, u - v⟫_ℝ := hA hu.1 hv
  have hvu_nonneg : 0 ≤ ⟪AffineMap.lineMap x y t - y, v - u⟫_ℝ := hA hv hu.2
  have huv_nonneg' : 0 ≤ t * ⟪x - y, u - v⟫_ℝ := by
    rw [show x - AffineMap.lineMap x y t = t • (x - y) by
      simpa using (AffineMap.left_vsub_lineMap x y t : x - AffineMap.lineMap x y t = _),
      real_inner_smul_left] at huv_nonneg
    exact huv_nonneg
  have hvu_nonneg' : 0 ≤ (1 - t) * ⟪x - y, v - u⟫_ℝ := by
    rw [show AffineMap.lineMap x y t - y = (1 - t) • (x - y) by
      simpa using (AffineMap.lineMap_vsub_right x y t : AffineMap.lineMap x y t - y = _),
      real_inner_smul_left] at hvu_nonneg
    exact hvu_nonneg
  have hnonpos : ⟪x - y, v - u⟫_ℝ ≤ 0 := by
    rw [inner_sub_swap] at huv_nonneg'
    nlinarith [ht.1, huv_nonneg']
  have hnonneg : 0 ≤ ⟪x - y, v - u⟫_ℝ := by
    have h_one_sub_t : 0 < 1 - t := by linarith [ht.2]
    nlinarith [h_one_sub_t, hvu_nonneg']
  exact le_antisymm hnonpos hnonneg

/-- Proposition 22.10 (2): under the hypotheses of Proposition 22.10 (1), if `A` is
paramonotone and the endpoint fibers have a common value, then the fiber at the segment point
equals their intersection: `A z = A x ∩ A y`. Here `z ∈ A.dom` remains essential, while
`x, y ∈ A.dom` and `x ≠ y` are already forced by the remaining assumptions. -/
theorem eq_inter_of_mem_openSegment_of_common_value_of_isParamonotone
    {A : SetValuedOperator H H} (hA : A.IsParamonotone)
    {x y z : H}
    (hz : z ∈ A.dom) (hxy : (A x ∩ A y).Nonempty) (hzseg : z ∈ openSegment ℝ x y) :
    A z = A x ∩ A y := by
  rcases hxy with ⟨u, hu⟩
  rcases (SetValuedOperator.mem_dom_iff A z).mp hz with ⟨w, hw⟩
  rw [openSegment_eq_image_lineMap] at hzseg
  rcases hzseg with ⟨t, ht, htz⟩
  subst z
  have hzseg : AffineMap.lineMap x y t ∈ openSegment ℝ x y :=
    lineMap_mem_openSegment ℝ x y ht
  ext v
  constructor
  · intro hv
    -- Part (i) places every middle value on the affine hyperplane through the common endpoint
    -- value `u`, which is exactly the vanishing pairing needed for the two swap steps.
    have hvu_zero : ⟪x - y, v - u⟫_ℝ = 0 :=
      subset_zeroInner_of_mem_openSegment_of_common_value hA.isMonotone hu hzseg hv
    have huv_zero : ⟪x - y, u - v⟫_ℝ = 0 :=
      (inner_sub_swap_eq_zero_iff x y u v).2 hvu_zero
    have hxz_zero : ⟪x - AffineMap.lineMap x y t, u - v⟫_ℝ = 0 :=
      inner_eq_zero_left_vsub_lineMap huv_zero
    have hzy_zero : ⟪AffineMap.lineMap x y t - y, v - u⟫_ℝ = 0 :=
      inner_eq_zero_lineMap_vsub_right hvu_zero
    constructor
    · exact (hA.swap_mem hu.1 hv hxz_zero).1
    · exact (hA.swap_mem hv hu.2 hzy_zero).2
  · rintro ⟨hvx, hvy⟩
    -- For the reverse inclusion, part (i) is reused with the common endpoint value `v` and an
    -- arbitrary witness `w ∈ A z`.
    have hv : v ∈ A x ∩ A y := ⟨hvx, hvy⟩
    have hwv_zero : ⟪x - y, w - v⟫_ℝ = 0 :=
      subset_zeroInner_of_mem_openSegment_of_common_value hA.isMonotone hv hzseg hw
    have hvw_zero : ⟪x - y, v - w⟫_ℝ = 0 :=
      (inner_sub_swap_eq_zero_iff x y w v).1 hwv_zero
    have hxz_zero : ⟪x - AffineMap.lineMap x y t, v - w⟫_ℝ = 0 :=
      inner_eq_zero_left_vsub_lineMap hvw_zero
    exact (hA.swap_mem hvx hw hxz_zero).2

end SetValuedOperator
