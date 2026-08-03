import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap24.Example_24_34
import BauschkeLean.Chap24.Proposition_24_8
import BauschkeLean.Chap24.Proposition_24_54

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

-- Semantic recall note: `lean_leansearch` only surfaced unrelated `ValueDistribution.proximity`
-- results, so this item follows the verified local Chapter 12/24 owners `{}^[ρ] ι[C]`,
-- `σ[Ω]`, `projIccReal`, `intervalSoftThresholder`, and `Prox[...]`.

/-- The interval `C = [-ρ, ρ]` used in the Berhu example. -/
def berhuInterval (ρ : PosReal) : Set ℝ :=
  Set.Icc (-(ρ : ℝ)) (ρ : ℝ)

/-- The scalar distance term `ψ(ξ) = d(ξ, [-ρ,ρ])^2 / (2ρ)` from the Berhu decomposition. -/
def berhuMoreauPartReal (ρ : PosReal) : ℝ → ℝ :=
  fun ξ ↦ Metric.infDist ξ (berhuInterval ρ) ^ 2 / (2 * (ρ : ℝ))

/-- The extended-real Berhu distance term `ψ = d_C^2 / (2ρ)`. -/
def berhuMoreauPart (ρ : PosReal) : ℝ → Set.Ioi (⊥ : EReal) :=
  (berhuMoreauPartReal ρ).toEReal

/-- The `Γ₀(ℝ)` representative of `σ[[-1,1]]` is `ξ ↦ |ξ|`. -/
theorem supportFunction_Icc_neg_one_one_eq_abs_properIoi :
    properIoi (σ[Set.Icc (-1 : ℝ) 1])
        (isProper_supportFunction_of_nonempty
          (Set.Icc (-1 : ℝ) 1)
          (Set.nonempty_Icc.2 (by norm_num))) =
      (fun ξ : ℝ ↦ |ξ|).toEReal := sorry

/-- The canonical support function `σ[[-1,1]]` belongs to `Γ₀(ℝ)`. -/
theorem supportFunction_Icc_neg_one_one_mem_gammaZero :
    properIoi (σ[Set.Icc (-1 : ℝ) 1])
        (isProper_supportFunction_of_nonempty
          (Set.Icc (-1 : ℝ) 1)
          (Set.nonempty_Icc.2 (by norm_num))) ∈
      Γ₀(ℝ) := by
  simpa using
    example_11_2_2_supportFunction_mem_gammaZero
      (Set.Icc (-1 : ℝ) 1)
      (Set.nonempty_Icc.2 (by norm_num))

/-- The real-valued reverse Huber, or Berhu, function from Example 24.55. -/
def berhuFunctionReal (ρ : PosReal) : ℝ → ℝ :=
  fun ξ ↦
    if (ρ : ℝ) < |ξ| then
      (ξ ^ (2 : ℕ) + (ρ : ℝ) ^ (2 : ℕ)) / (2 * (ρ : ℝ))
    else
      |ξ|

/-- The extended-real Berhu function from Example 24.55. -/
def berhuFunction (ρ : PosReal) : ℝ → Set.Ioi (⊥ : EReal) :=
  (berhuFunctionReal ρ).toEReal

/-- Example 24.55 (1): the Berhu function is `(ξ^2 + ρ^2) / (2ρ)` on `ρ < |ξ|`,
and `|ξ|` on `|ξ| ≤ ρ`, as in `(24.100)`. -/
theorem berhuFunctionReal_eq_piecewise (ρ : PosReal) :
    berhuFunctionReal ρ =
      fun ξ : ℝ ↦
        if (ρ : ℝ) < |ξ| then
          (ξ ^ (2 : ℕ) + (ρ : ℝ) ^ (2 : ℕ)) / (2 * (ρ : ℝ))
        else
          |ξ| := sorry

/-- The interval `[-ρ, ρ]` is nonempty. -/
theorem berhuInterval_nonempty (ρ : PosReal) : Set.Nonempty (berhuInterval ρ) := by
  refine Set.nonempty_Icc.2 ?_
  nlinarith [show (0 : ℝ) < (ρ : ℝ) from ρ.2]

/-- The scalar projector `P_[-ρ,ρ]` appearing in formula `(24.101)`. -/
def berhuIntervalProjection (ρ : PosReal) : ℝ → ℝ :=
  projIccReal (show -(ρ : ℝ) ≤ (ρ : ℝ) by
    nlinarith [show (0 : ℝ) < (ρ : ℝ) from ρ.2])

/-- The distance term `ψ` is the `ρ`-Moreau envelope of the indicator of `[-ρ,ρ]`. -/
theorem berhuMoreauPart_eq_indicatorMoreauEnvelope (ρ : PosReal) :
    berhuMoreauPart ρ = {}^[ρ] ι[berhuInterval ρ] := sorry

/-- The Berhu distance term belongs to `Γ₀(ℝ)`. -/
theorem berhuMoreauPart_mem_gammaZero (ρ : PosReal) :
    berhuMoreauPart ρ ∈ Γ₀(ℝ) := sorry

/-- The finite representative of `berhuMoreauPart ρ` is finite on a neighborhood of `0`. -/
theorem zero_mem_interior_effectiveDomain_berhuMoreauPart (ρ : PosReal) :
    0 ∈ interior (effectiveDomain (berhuMoreauPart ρ)) := sorry

/-- The finite representative of `berhuMoreauPart ρ` has derivative `0` at the origin. -/
theorem hasDerivAt_berhuMoreauPart_zero (ρ : PosReal) :
    HasDerivAt (fun y ↦ (berhuMoreauPart ρ y : EReal).toReal) 0 0 := sorry

/-- The Berhu function is the sum of its distance term and `σ[[-1,1]]`. -/
theorem berhuFunction_eq_add_berhuMoreauPart_and_supportFunction (ρ : PosReal) :
    (berhuFunction ρ).asEReal =
      (berhuMoreauPart ρ).asEReal + σ[Set.Icc (-1 : ℝ) 1] := sorry

/-- The `Γ₀(ℝ)` representative of the Berhu decomposition uses `properIoi σ[[-1,1]]`. -/
theorem berhuFunction_eq_add_berhuMoreauPart_and_supportFunction_properIoi (ρ : PosReal) :
    berhuFunction ρ =
      berhuMoreauPart ρ +
        properIoi (σ[Set.Icc (-1 : ℝ) 1])
          (isProper_supportFunction_of_nonempty
            (Set.Icc (-1 : ℝ) 1)
            (Set.nonempty_Icc.2 (by norm_num))) := sorry

/-- The Berhu function belongs to `Γ₀(ℝ)`. -/
theorem berhuFunction_mem_gammaZero (ρ : PosReal) :
    berhuFunction ρ ∈ Γ₀(ℝ) := sorry

/-- The Berhu proximal map factors as `Prox_ψ ∘ soft_[-1,1]`. -/
theorem prox_berhuFunction_eq_prox_berhuMoreauPart_comp_intervalSoftThresholder
    (ρ : PosReal) :
    Prox[berhuFunction ρ, berhuFunction_mem_gammaZero ρ] =
      Prox[berhuMoreauPart ρ, berhuMoreauPart_mem_gammaZero ρ] ∘
        intervalSoftThresholder (-1 : ℝ) 1 := sorry

/-- Example 24.55 (2): for `C = [-ρ, ρ]` and `ψ(ξ) = d(ξ, C)^2 / (2ρ)`, the proximity operator
of `ψ` is `Id + (1 / (ρ + 1)) (P_C - Id)` on `ℝ`. -/
theorem prox_berhuMoreauPart_eq_affine_projection (ρ : PosReal) :
    Prox[berhuMoreauPart ρ, berhuMoreauPart_mem_gammaZero ρ] =
      fun ξ : ℝ ↦
        ξ + (((ρ + 1 : PosReal) : ℝ)⁻¹) * (berhuIntervalProjection ρ ξ - ξ) := sorry

/-- Example 24.55 (3): the Berhu proximal map is `ρ ξ / (ρ + 1)` on `ρ + 1 < |ξ|`,
`ξ - sign ξ` on `1 < |ξ| ≤ ρ + 1`, and `0` on `|ξ| ≤ 1`. -/
theorem prox_berhuFunction_eq_piecewise (ρ : PosReal) :
    Prox[berhuFunction ρ, berhuFunction_mem_gammaZero ρ] =
      fun ξ : ℝ ↦
        if (ρ : ℝ) + 1 < |ξ| then
          ((ρ : ℝ) * ξ) / (((ρ + 1 : PosReal) : ℝ))
        else if 1 < |ξ| then
          ξ - Real.sign ξ
        else
          0 := sorry

end

end ERealFunction
