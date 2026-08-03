import BauschkeLean.Chap02.Text_2_0_9
import BauschkeLean.Chap03.Definition_3_8
import BauschkeLean.Chap03.Theorem_3_16_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

-- Semantic recall: `lean_leansearch` only surfaced generic orthogonal-projection owners, while
-- the project-local source-facing API for this item is `innerProductClosedSublevelSet` together
-- with the metric projector `P[C, hC]`, so Example 29.20 is stated directly in that notation.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The closed inner-product halfspace `innerProductClosedSublevelSet u η` is closed. -/
private theorem innerProductClosedSublevelSet_isClosed (u : H) (η : ℝ) :
    IsClosed (innerProductClosedSublevelSet u η) := by
  -- The halfspace is the preimage of the closed ray `(-∞, η]` under the continuous functional
  -- `x ↦ ⟪x, u⟫_ℝ`.
  simpa [innerProductClosedSublevelSet, innerSLFlip_apply_apply] using
    isClosed_Iic.preimage (innerSLFlip ℝ u).continuous

/-- The closed inner-product halfspace `innerProductClosedSublevelSet u η` is convex. -/
private theorem innerProductClosedSublevelSet_convex (u : H) (η : ℝ) :
    Convex ℝ (innerProductClosedSublevelSet u η) := by
  -- Convexity is preserved under linear preimages, and `Set.Iic η` is convex in `ℝ`.
  simpa [innerProductClosedSublevelSet, innerSLFlip_apply_apply] using
    (convex_Iic η).linear_preimage (innerSLFlip ℝ u).toLinearMap

section CompleteSpace

variable [CompleteSpace H]

/-- If `u = 0` and `η ≥ 0`, then the closed inner-product halfspace is Chebyshev because it is the
whole space. -/
theorem innerProductClosedSublevelSet_isChebyshev_of_eq_zero_of_nonneg
    {u : H} {η : ℝ} (hu : u = 0) (hη : 0 ≤ η) :
    IsChebyshev (innerProductClosedSublevelSet u η) := by
  -- In the degenerate nonnegative case the halfspace is all of `H`, so the general closed-convex
  -- projection theorem applies to `Set.univ`.
  have hC_eq : innerProductClosedSublevelSet u η = Set.univ := by
    ext x
    simp [mem_innerProductClosedSublevelSet_iff, hu, hη]
  rw [hC_eq]
  exact isChebyshev_of_nonempty_isClosed_convex ⟨0, Set.mem_univ 0⟩ isClosed_univ convex_univ

/-- If `u ≠ 0`, then the closed inner-product halfspace is Chebyshev as a nonempty closed convex
subset of the real Hilbert space. -/
theorem innerProductClosedSublevelSet_isChebyshev_of_ne_zero
    {u : H} {η : ℝ} (hu : u ≠ 0) :
    IsChebyshev (innerProductClosedSublevelSet u η) := by
  -- The nonzero halfspace has an explicit boundary point, so closedness and convexity are enough.
  have hC_nonempty : (innerProductClosedSublevelSet u η).Nonempty := by
    have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
    refine ⟨((η / ‖u‖ ^ 2) • u), ?_⟩
    rw [mem_innerProductClosedSublevelSet_iff]
    refine le_of_eq ?_
    calc
      ⟪(η / ‖u‖ ^ 2) • u, u⟫_ℝ
          = (η / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ := by
              rw [real_inner_smul_left]
      _ = (η / ‖u‖ ^ 2) * (‖u‖ ^ 2) := by
            rw [real_inner_self_eq_norm_sq]
      _ = η := by
            field_simp [hu_sq]
  exact isChebyshev_of_nonempty_isClosed_convex
    hC_nonempty
    (innerProductClosedSublevelSet_isClosed u η)
    (innerProductClosedSublevelSet_convex u η)

end CompleteSpace

/-- Helper for Example 29.20: if `u = 0` and `η ≥ 0`, then
`C = {x ∈ H | ⟪x, u⟫_ℝ ≤ η} = H`. -/
theorem innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg
    {u : H} {η : ℝ} (hu : u = 0) (hη : 0 ≤ η) :
    innerProductClosedSublevelSet u η = Set.univ := by
  -- When `u = 0`, the membership inequality becomes `0 ≤ η`, which is true by assumption.
  ext x
  simp [mem_innerProductClosedSublevelSet_iff, hu, hη]

/-- Helper for Example 29.20: if `u = 0` and `η < 0`, then
`C = {x ∈ H | ⟪x, u⟫_ℝ ≤ η} = ∅`. -/
theorem innerProductClosedSublevelSet_eq_empty_of_eq_zero_of_neg
    {u : H} {η : ℝ} (hu : u = 0) (hη : η < 0) :
    innerProductClosedSublevelSet u η = ∅ := by
  -- When `u = 0`, the membership inequality becomes `0 ≤ η`, which contradicts `η < 0`.
  ext x
  simp [mem_innerProductClosedSublevelSet_iff, hu, not_le_of_gt hη]

/-- Helper for Example 29.20: if `u ≠ 0`, then the closed halfspace
`C = {x ∈ H | ⟪x, u⟫_ℝ ≤ η}` is nonempty. -/
theorem innerProductClosedSublevelSet_nonempty_of_ne_zero
    {u : H} {η : ℝ} (hu : u ≠ 0) :
    (innerProductClosedSublevelSet u η).Nonempty := by
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  -- The scaled normal vector lies on the boundary `⟪x, u⟫_ℝ = η`.
  refine ⟨((η / ‖u‖ ^ 2) • u), ?_⟩
  rw [mem_innerProductClosedSublevelSet_iff]
  refine le_of_eq ?_
  calc
    ⟪(η / ‖u‖ ^ 2) • u, u⟫_ℝ
        = (η / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ := by
            rw [real_inner_smul_left]
    _ = (η / ‖u‖ ^ 2) * (‖u‖ ^ 2) := by
          rw [real_inner_self_eq_norm_sq]
    _ = η := by
          field_simp [hu_sq]

section EqZeroNonneg

variable {u : H} {η : ℝ} (hu : u = 0) (hη : 0 ≤ η)
variable [CompleteSpace H]

local notation "C" => innerProductClosedSublevelSet u η
local notation "hC_cheb" =>
  innerProductClosedSublevelSet_isChebyshev_of_eq_zero_of_nonneg hu hη
local notation "P_C" => P[C, hC_cheb]

/-- Helper for Example 29.20: if `u = 0` and `η ≥ 0`, then the metric projection onto
`C = {x ∈ H | ⟪x, u⟫_ℝ ≤ η}` is the identity map, i.e. `P_C x = x` for every `x ∈ H`. -/
theorem projectionPoint_innerProductClosedSublevelSet_eq_self_of_eq_zero_of_nonneg
    (x : H) :
    P_C x = x := by
  have hC_eq : C = Set.univ :=
    innerProductClosedSublevelSet_eq_univ_of_eq_zero_of_nonneg hu hη
  have hx_mem : x ∈ C := by
    rw [hC_eq]
    simp
  have hx_best : IsBestApproximation x C x := by
    -- In the whole space, the point itself belongs to the set and already realizes zero distance.
    refine ⟨hx_mem, ?_⟩
    simp [Metric.infDist_zero_of_mem hx_mem]
  -- Uniqueness in the Chebyshev structure identifies the canonical projector with this best
  -- approximation.
  exact (eq_projectionPoint_of_isBestApproximation C hC_cheb hx_best).symm

end EqZeroNonneg

section NeZero

variable {u : H} {η : ℝ} (hu : u ≠ 0)
variable [CompleteSpace H]

local notation "C" => innerProductClosedSublevelSet u η
local notation "hC_cheb" => innerProductClosedSublevelSet_isChebyshev_of_ne_zero hu
local notation "P_C" => P[C, hC_cheb]

/-- Example 29.20 (5): if `u ≠ 0`, then for every `x ∈ H` the metric projection onto
`C = {y ∈ H | ⟪y, u⟫_ℝ ≤ η}` is given by the branch formula (29.18):
it is `x` when `⟪x, u⟫_ℝ ≤ η`, and otherwise it is
`x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u`. -/
theorem projectionPoint_innerProductClosedSublevelSet_eq_piecewise_of_ne_zero
    (x : H) :
    P_C x =
      if ⟪x, u⟫_ℝ ≤ η then
        x
      else
        x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
  have hC_nonempty : Set.Nonempty C := innerProductClosedSublevelSet_nonempty_of_ne_zero hu
  have hC_closed : IsClosed C := innerProductClosedSublevelSet_isClosed u η
  have hC_convex : Convex ℝ C := innerProductClosedSublevelSet_convex u η
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  by_cases hx : ⟪x, u⟫_ℝ ≤ η
  · -- In the feasible branch, `x` already lies in the halfspace, so it satisfies the projector
    -- characterization with zero residual.
    suffices hproj : x = P_C x by
      simpa only [if_pos hx] using hproj.symm
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).2 ?_
    refine ⟨?_, ?_⟩
    · simpa [mem_innerProductClosedSublevelSet_iff] using hx
    · intro y hy
      simp
  · let p : H := x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u
    have hp_eq : ⟪p, u⟫_ℝ = η := by
      -- The correction term is chosen so that the boundary equation holds exactly.
      calc
        ⟪p, u⟫_ℝ
            = ⟪x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u, u⟫_ℝ := by
                rfl
        _ = ⟪x, u⟫_ℝ + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ := by
              rw [inner_add_left, real_inner_smul_left]
        _ = ⟪x, u⟫_ℝ + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) * (‖u‖ ^ 2) := by
              rw [real_inner_self_eq_norm_sq]
        _ = η := by
              field_simp [hu_sq]
              ring
    have hp_mem : p ∈ C := by
      -- The explicit candidate lies on the boundary, hence in the closed halfspace.
      rw [mem_innerProductClosedSublevelSet_iff]
      exact hp_eq.le
    have hxp :
        x - p = ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u := by
      have hscalar :
          -((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) = (⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2 := by
        ring
      -- Rewriting the residual along the normal vector reduces the variational inequality to a
      -- scalar sign check.
      calc
        x - p = -(((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u) := by
          simp [p, sub_eq_add_neg, add_comm]
        _ = (-((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2)) • u := by
              rw [neg_smul]
        _ = ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u := by
              rw [hscalar]
    have hvari : ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
      intro y hy
      have hy_le : ⟪y, u⟫_ℝ ≤ η := by
        simpa [mem_innerProductClosedSublevelSet_iff] using hy
      have hx_lt : η < ⟪x, u⟫_ℝ := lt_of_not_ge hx
      have hcoef_nonneg : 0 ≤ (⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2 := by
        exact div_nonneg (sub_nonneg.mpr hx_lt.le) (sq_nonneg ‖u‖)
      have hyu_nonpos : ⟪y - p, u⟫_ℝ ≤ 0 := by
        calc
          ⟪y - p, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪p, u⟫_ℝ := by
                rw [inner_sub_left]
          _ = ⟪y, u⟫_ℝ - η := by
                rw [hp_eq]
          _ ≤ 0 := by
                linarith
      calc
        ⟪y - p, x - p⟫_ℝ
            = ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * ⟪y - p, u⟫_ℝ := by
                rw [hxp, real_inner_smul_right]
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg hyu_nonpos
    -- The variational inequality characterizes the explicit boundary correction as the projector.
    suffices hproj : p = P_C x by
      simpa only [if_neg hx] using hproj.symm
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).2 ?_
    exact ⟨hp_mem, hvari⟩

end NeZero
