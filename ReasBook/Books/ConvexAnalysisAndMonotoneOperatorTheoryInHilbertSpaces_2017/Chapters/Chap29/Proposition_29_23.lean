import BauschkeLean.Chap29.Example_29_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

-- Semantic recall: `lean_leansearch` only surfaced generic orthogonal-projection owners, while
-- the verified Chapter 29 source-facing API for this item is the halfspace owner
-- `innerProductClosedSublevelSet` together with the metric projector notation `P[C, hC]`.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {u₁ u₂ x : H} {η₁ η₂ : ℝ}

local notation "C" =>
  innerProductClosedSublevelSet u₁ η₁ ∩ innerProductClosedSublevelSet u₂ η₂

local notation "gramDet" =>
  ‖u₁‖ ^ 2 * ‖u₂‖ ^ 2 - |⟪u₁, u₂⟫_ℝ| ^ 2

local notation "Case1" =>
  ⟪x, u₁⟫_ℝ ≤ η₁ ∧ ⟪x, u₂⟫_ℝ ≤ η₂

local notation "Case2" =>
  ‖u₂‖ ^ 2 * (⟪x, u₁⟫_ℝ - η₁) >
      ⟪u₁, u₂⟫_ℝ * (⟪x, u₂⟫_ℝ - η₂) ∧
    ‖u₁‖ ^ 2 * (⟪x, u₂⟫_ℝ - η₂) >
      ⟪u₁, u₂⟫_ℝ * (⟪x, u₁⟫_ℝ - η₁)

local notation "Case3" =>
  ⟪x, u₂⟫_ℝ > η₂ ∧
    ‖u₂‖ ^ 2 * (⟪x, u₁⟫_ℝ - η₁) ≤
      ⟪u₁, u₂⟫_ℝ * (⟪x, u₂⟫_ℝ - η₂)

local notation "Case4" =>
  ⟪x, u₁⟫_ℝ > η₁ ∧
    ‖u₁‖ ^ 2 * (⟪x, u₂⟫_ℝ - η₂) ≤
      ⟪u₁, u₂⟫_ℝ * (⟪x, u₁⟫_ℝ - η₁)

local notation "nu1Case2" =>
  (‖u₂‖ ^ 2 * (⟪x, u₁⟫_ℝ - η₁) -
      ⟪u₁, u₂⟫_ℝ * (⟪x, u₂⟫_ℝ - η₂)) / gramDet

local notation "nu2Case2" =>
  (‖u₁‖ ^ 2 * (⟪x, u₂⟫_ℝ - η₂) -
      ⟪u₁, u₂⟫_ℝ * (⟪x, u₁⟫_ℝ - η₁)) / gramDet

local notation "nu2Case3" =>
  (⟪x, u₂⟫_ℝ - η₂) / ‖u₂‖ ^ 2

local notation "nu1Case4" =>
  (⟪x, u₁⟫_ℝ - η₁) / ‖u₁‖ ^ 2

/-- Proposition 29.23 (1): if
`‖u₁‖^2 ‖u₂‖^2 > |⟪u₁, u₂⟫_ℝ|^2`, then
`C = {y | ⟪y, u₁⟫_ℝ ≤ η₁} ∩ {y | ⟪y, u₂⟫_ℝ ≤ η₂}` is nonempty. -/
theorem innerProductClosedSublevelSetInter_nonempty_of_gram_det_pos
    (hdet : 0 < gramDet) :
    Set.Nonempty C := sorry

/-- Proposition 29.23 (2): under the positive Gram determinant hypothesis, exactly one of the
four source case hypotheses `(i)`--`(iv)` occurs for the point `x`. -/
theorem innerProductClosedSublevelSetInter_case_partition_of_gram_det_pos
    (hdet : 0 < gramDet) :
    Xor' Case1 (Xor' Case2 (Xor' Case3 Case4)) := sorry

section CompleteSpace

variable [CompleteSpace H]

/-- The intersection of the two closed inner-product halfspaces is Chebyshev under the positive
Gram determinant hypothesis from Proposition 29.23. -/
theorem innerProductClosedSublevelSetInter_isChebyshev_of_gram_det_pos
    (hdet : 0 < gramDet) :
    IsChebyshev C := sorry

/-- Proposition 29.23 (3): if `x` satisfies both halfspace inequalities, then the metric
projection onto `C` is `x`, i.e. the coefficients `ν₁` and `ν₂` are both zero. -/
theorem projectionPoint_innerProductClosedSublevelSetInter_eq_self_of_le_of_le
    (hdet : 0 < gramDet)
    (hx₁ : ⟪x, u₁⟫_ℝ ≤ η₁)
    (hx₂ : ⟪x, u₂⟫_ℝ ≤ η₂) :
    P[C, innerProductClosedSublevelSetInter_isChebyshev_of_gram_det_pos hdet] x = x := sorry

/-- Proposition 29.23 (4): if both strict cross-inequalities from case `(ii)` hold, then the
metric projection onto `C` is `x - nu1Case2 • u₁ - nu2Case2 • u₂`. -/
theorem projectionPoint_innerProductClosedSublevelSetInter_eq_sub_of_case2
    (hdet : 0 < gramDet)
    (hx₁ :
      ‖u₂‖ ^ 2 * (⟪x, u₁⟫_ℝ - η₁) >
        ⟪u₁, u₂⟫_ℝ * (⟪x, u₂⟫_ℝ - η₂))
    (hx₂ :
      ‖u₁‖ ^ 2 * (⟪x, u₂⟫_ℝ - η₂) >
        ⟪u₁, u₂⟫_ℝ * (⟪x, u₁⟫_ℝ - η₁)) :
    P[C, innerProductClosedSublevelSetInter_isChebyshev_of_gram_det_pos hdet] x =
      x - nu1Case2 • u₁ - nu2Case2 • u₂ := sorry

/-- Under the case `(ii)` hypotheses of Proposition 29.23 (4), the first coefficient
`nu1Case2` is strictly positive. -/
theorem projectionPoint_innerProductClosedSublevelSetInter_nu1_pos_of_case2
    (hdet : 0 < gramDet)
    (hx₁ :
      ‖u₂‖ ^ 2 * (⟪x, u₁⟫_ℝ - η₁) >
        ⟪u₁, u₂⟫_ℝ * (⟪x, u₂⟫_ℝ - η₂))
    (hx₂ :
      ‖u₁‖ ^ 2 * (⟪x, u₂⟫_ℝ - η₂) >
        ⟪u₁, u₂⟫_ℝ * (⟪x, u₁⟫_ℝ - η₁)) :
    0 < nu1Case2 := sorry

/-- Under the case `(ii)` hypotheses of Proposition 29.23 (4), the second coefficient
`nu2Case2` is strictly positive. -/
theorem projectionPoint_innerProductClosedSublevelSetInter_nu2_pos_of_case2
    (hdet : 0 < gramDet)
    (hx₁ :
      ‖u₂‖ ^ 2 * (⟪x, u₁⟫_ℝ - η₁) >
        ⟪u₁, u₂⟫_ℝ * (⟪x, u₂⟫_ℝ - η₂))
    (hx₂ :
      ‖u₁‖ ^ 2 * (⟪x, u₂⟫_ℝ - η₂) >
        ⟪u₁, u₂⟫_ℝ * (⟪x, u₁⟫_ℝ - η₁)) :
    0 < nu2Case2 := sorry

/-- Proposition 29.23 (5): if case `(iii)` holds, then the left coefficient vanishes, the right
coefficient is `(⟪x, u₂⟫_ℝ - η₂) / ‖u₂‖^2`, and the metric projection onto `C` is the
corresponding affine correction along `u₂`. -/
theorem projectionPoint_innerProductClosedSublevelSetInter_eq_sub_right_of_case3
    (hdet : 0 < gramDet)
    (hx₂ : ⟪x, u₂⟫_ℝ > η₂)
    (hcross :
      ‖u₂‖ ^ 2 * (⟪x, u₁⟫_ℝ - η₁) ≤
        ⟪u₁, u₂⟫_ℝ * (⟪x, u₂⟫_ℝ - η₂)) :
    P[C, innerProductClosedSublevelSetInter_isChebyshev_of_gram_det_pos hdet] x =
        x - nu2Case3 • u₂ ∧
      0 < nu2Case3 := sorry

/-- Proposition 29.23 (6): if case `(iv)` holds, then the right coefficient vanishes, the left
coefficient is `(⟪x, u₁⟫_ℝ - η₁) / ‖u₁‖^2`, and the metric projection onto `C` is the
corresponding affine correction along `u₁`. -/
theorem projectionPoint_innerProductClosedSublevelSetInter_eq_sub_left_of_case4
    (hdet : 0 < gramDet)
    (hx₁ : ⟪x, u₁⟫_ℝ > η₁)
    (hcross :
      ‖u₁‖ ^ 2 * (⟪x, u₂⟫_ℝ - η₂) ≤
        ⟪u₁, u₂⟫_ℝ * (⟪x, u₁⟫_ℝ - η₁)) :
    P[C, innerProductClosedSublevelSetInter_isChebyshev_of_gram_det_pos hdet] x =
        x - nu1Case4 • u₁ ∧
      0 < nu1Case4 := sorry

end CompleteSpace

end
