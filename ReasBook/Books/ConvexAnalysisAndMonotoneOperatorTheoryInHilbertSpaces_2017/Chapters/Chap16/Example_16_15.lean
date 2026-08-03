import Mathlib
import BauschkeLean.Chap16.Example_16_14

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

noncomputable section

section RealLine

open scoped InnerProductSpace

/-- Helper for Example 16 15: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  -- Collapse the one-dimensional inner product to the scalar formula on `ℝ`.
  calc
    ⟪x, y⟫_ℝ = (starRingEnd ℝ) x * y := RCLike.inner_apply' x y
    _ = x * y := by simp

-- Proof sketch: the support function of `[-1,1]` is the supremum of `x ↦ ξ x` over that interval,
-- which equals `|ξ|` by checking the sign of `ξ` and evaluating at the appropriate endpoint.
/-- The support function of the interval `[-1,1] ⊆ ℝ` is the absolute value. -/
theorem supportFunction_Icc_neg_one_one_eq_abs :
    σ[Set.Icc (-1 : ℝ) 1] = (fun ξ : ℝ ↦ |ξ|).toEReal.asEReal := by
  funext ξ
  have hIcc : (-1 : ℝ) ≤ 1 := by
    norm_num
  have hnonempty_mem : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    simp
  have hnonempty : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, hnonempty_mem⟩
  have hinner :
      (fun x : ℝ ↦ (⟪x, ξ⟫_ℝ : EReal)) =
        fun x : ℝ ↦ ((x * ξ : ℝ) : EReal) := by
    -- Rewrite the inner product on `ℝ` into plain multiplication before maximizing on the interval.
    funext x
    simp [real_inner_eq_mul]
  by_cases hξ_neg : ξ < 0
  · have hanti :
        AntitoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc (-1 : ℝ) 1) := by
      -- A negative slope makes the affine functional decrease,
      -- so the maximum is at the left endpoint.
      intro x hx y hy hxy
      have hmul : y * ξ ≤ x * ξ := mul_le_mul_of_nonpos_right hxy hξ_neg.le
      simpa using (EReal.coe_le_coe hmul)
    have hsSup :
        sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc (-1 : ℝ) 1) =
          (((-1 : ℝ) * ξ : ℝ) : EReal) :=
      AntitoneOn.sSup_image_Icc hIcc hanti
    rw [supportFunction_eq_sSup_image, hinner, hsSup]
    simp [abs_of_neg hξ_neg]
  · by_cases hξ_zero : ξ = 0
    · -- At the origin the support function of any nonempty set vanishes.
      rw [hξ_zero]
      simpa using supportFunction_zero_eq_zero_of_nonempty (C := Set.Icc (-1 : ℝ) 1) hnonempty
    · have hξ_pos : 0 < ξ := by
        exact lt_of_le_of_ne (le_of_not_gt hξ_neg) (Ne.symm hξ_zero)
      have hmono :
          MonotoneOn (fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) (Set.Icc (-1 : ℝ) 1) := by
        -- A positive slope makes the affine functional increase,
        -- so the maximum is at the right endpoint.
        intro x hx y hy hxy
        have hmul : x * ξ ≤ y * ξ := mul_le_mul_of_nonneg_right hxy hξ_pos.le
        simpa using (EReal.coe_le_coe hmul)
      have hsSup :
          sSup ((fun x : ℝ ↦ ((x * ξ : ℝ) : EReal)) '' Set.Icc (-1 : ℝ) 1) =
            (((1 : ℝ) * ξ : ℝ) : EReal) :=
        MonotoneOn.sSup_image_Icc hIcc hmono
      rw [supportFunction_eq_sSup_image, hinner, hsSup]
      simp [abs_of_pos hξ_pos]

/-- Helper for Example 16 15: the lower-endpoint slice returned by Example 16.14 on `[-1,1]`
is the singleton `{-1}`. -/
private lemma lower_endpoint_slice_Icc_neg_one_one :
    {x : ℝ | (x : EReal) = sInf (Set.Icc (-1 : EReal) 1)} = {(-1 : ℝ)} := by
  have hIccReal : (-1 : ℝ) ≤ 1 := by
    norm_num
  have hIcc : ((-1 : EReal) ≤ (1 : EReal)) := by
    exact EReal.coe_le_coe hIccReal
  -- Evaluate the `EReal` infimum of the interval and identify the resulting singleton slice.
  ext x
  constructor
  · intro hx
    have hx' : (x : EReal) = (-1 : EReal) := by
      simpa [csInf_Icc hIcc] using hx
    exact EReal.coe_eq_coe_iff.mp hx'
  · intro hx
    have hx' : x = -1 := by
      simpa using hx
    rw [hx']
    simp [csInf_Icc hIcc]

/-- Helper for Example 16 15: the upper-endpoint slice returned by Example 16.14 on `[-1,1]`
is the singleton `{1}`. -/
private lemma upper_endpoint_slice_Icc_neg_one_one :
    {x : ℝ | (x : EReal) = sSup (Set.Icc (-1 : EReal) 1)} = {(1 : ℝ)} := by
  have hIccReal : (-1 : ℝ) ≤ 1 := by
    norm_num
  have hIcc : ((-1 : EReal) ≤ (1 : EReal)) := by
    exact EReal.coe_le_coe hIccReal
  -- Evaluate the `EReal` supremum of the interval and identify the resulting singleton slice.
  ext x
  constructor
  · intro hx
    have hx' : (x : EReal) = (1 : EReal) := by
      simpa [csSup_Icc hIcc] using hx
    exact EReal.coe_eq_coe_iff.mp hx'
  · intro hx
    have hx' : x = 1 := by
      simpa using hx
    rw [hx']
    simp [csSup_Icc hIcc]

/-- Helper for Example 16 15: the interval `[-1,1]` is already closed and convex, so its closed
convex hull is itself. -/
private lemma closedConvexHull_Icc_neg_one_one :
    closedConvexHull ℝ (Set.Icc (-1 : ℝ) 1) = Set.Icc (-1 : ℝ) 1 := by
  -- The closed convex hull adds nothing to a closed convex interval.
  rw [closedConvexHull_eq_closure_convexHull, (convex_Icc (-1 : ℝ) 1).convexHull_eq]
  exact isClosed_Icc.closure_eq

-- Proof sketch: identify `|·|` with the support function of `[-1,1]` and apply the three
-- subdifferential formulas from Example 16.14 directly to the canonical owner
-- `(∂ (fun η ↦ |η|).toEReal)`. This yields the endpoints `-1` and `1` away from `0`, and the
-- interval `[-1,1]` at `0`.
/-- Example 16 15: since `|·| = σ[[-1,1]]`, the subdifferential of the absolute value on `ℝ` is
`{-1}` on `(-∞,0)`, `[-1,1]` at `0`, and `{1}` on `(0,+∞)`. -/
theorem subdifferential_abs_eq_piecewise (ξ : ℝ) :
    (∂ (fun η : ℝ ↦ |η|).toEReal) ξ =
      if ξ < 0 then {(-1 : ℝ)}
      else if ξ = 0 then Set.Icc (-1 : ℝ) 1
      else {(1 : ℝ)} := by
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    simp
  have hΩ : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, hzero_mem⟩
  -- Identify `|·|` with the support-function owner before applying Example 16.14 branchwise.
  change (∂ ((fun η : ℝ ↦ |η|).toEReal : ℝ → EReal)) ξ =
    if ξ < 0 then {(-1 : ℝ)}
    else if ξ = 0 then Set.Icc (-1 : ℝ) 1
    else {(1 : ℝ)}
  rw [← supportFunction_Icc_neg_one_one_eq_abs]
  by_cases hξ_neg : ξ < 0
  · -- Negative arguments use the lower-endpoint branch from Example 16.14.
    simpa [hξ_neg, lower_endpoint_slice_Icc_neg_one_one] using
      (subdifferential_supportFunction_eq_lowerEndpoint_of_neg
        (Ω := Set.Icc (-1 : ℝ) 1) hΩ hξ_neg)
  · by_cases hξ_zero : ξ = 0
    · -- The origin uses the closed-convex-hull branch, which collapses back to the interval.
      rw [hξ_zero]
      simpa [closedConvexHull_Icc_neg_one_one] using
        (subdifferential_supportFunction_eq_closedConvexHull_at_zero
          (Ω := Set.Icc (-1 : ℝ) 1) hΩ)
    · have hξ_pos : 0 < ξ := by
        exact lt_of_le_of_ne (le_of_not_gt hξ_neg) (Ne.symm hξ_zero)
      -- Positive arguments use the upper-endpoint branch from Example 16.14.
      simpa [hξ_neg, hξ_zero, upper_endpoint_slice_Icc_neg_one_one] using
        (subdifferential_supportFunction_eq_upperEndpoint_of_pos
          (Ω := Set.Icc (-1 : ℝ) 1) hΩ hξ_pos)

end RealLine

end

end ERealFunction
