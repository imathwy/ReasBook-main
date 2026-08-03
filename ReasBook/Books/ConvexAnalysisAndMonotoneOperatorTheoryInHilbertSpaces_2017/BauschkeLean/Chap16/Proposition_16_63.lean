import BauschkeLean.Chap13.Proposition_13_50
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [μ.IsComplete] [SigmaFinite μ]

-- Proposition 16.63 (1): the `Γ₀`-membership clause for `integralFunctional μ φ` is already the
-- canonical theorem `integralFunctional_mem_gammaZero`.

/-- Helper for Proposition 16.63: on a nonempty effective domain, subgradient membership implies
Fenchel--Young contact equality and conversely. -/
private theorem mem_subdifferential_iff_fenchel_young_eq_of_nonempty_effectiveDomain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → Set.Ioi (⊥ : EReal)) (x : E) (hdom : (effectiveDomain f).Nonempty) (u : E) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + conjugate f.asEReal u =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  -- TODO: restore the Proposition 16.10 bridge without importing `Chap16/Proposition_16_10`,
  -- whose `GammaZeroConjugate` dependency conflicts with the Chapter 13 owner used here.
  sorry

/-- Helper for Proposition 16.63: a point of the effective domain of `integralFunctional μ φ`
lies in the integral branch of `pointwiseIntegralFunctional φ`. -/
private theorem integralFunctional_branch_of_mem_effectiveDomain
    (φ : H → Set.Ioi (⊥ : EReal)) {x : Ω →₂[μ] H}
    (hx : x ∈ effectiveDomain (integralFunctional μ φ)) :
    Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤ := by
  -- Rewrite the `integralFunctional` effective-domain condition back to the Chapter 8 branch.
  have hx' : x ∈ pointwiseIntegralFunctionalDomain φ := by
    simpa [pointwiseIntegralFunctionalDomain, integralFunctional_coe μ] using hx
  rw [pointwiseIntegralFunctionalDomain_eq] at hx'
  exact hx'

/-- Helper for Proposition 16.63: on the effective domain, `integralFunctional μ φ` is the real
integral of the pointwise `toReal` integrand. -/
private theorem integralFunctional_apply_eq_integral_toReal_of_mem_effectiveDomain
    (φ : H → Set.Ioi (⊥ : EReal)) {x : Ω →₂[μ] H}
    (hx : x ∈ effectiveDomain (integralFunctional μ φ)) :
    (integralFunctional μ φ x : EReal) =
      ((∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) : EReal) := by
  -- The effective-domain hypothesis selects the integral branch in the definition.
  have hbranch := integralFunctional_branch_of_mem_effectiveDomain (μ := μ) φ hx
  rw [integralFunctional_coe μ φ, pointwiseIntegralFunctional, if_pos hbranch]

/-- Helper for Proposition 16.63: almost-everywhere pointwise subgradient membership is equivalent
to almost-everywhere Fenchel--Young equality. -/
private theorem ae_mem_subdifferential_iff_ae_fenchelYoung_eq
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) {x u : Ω →₂[μ] H} :
    (∀ᵐ ω ∂μ, u ω ∈ (∂ φ) (x ω)) ↔
      ∀ᵐ ω ∂μ,
        (φ (x ω) : EReal) + ((gammaZeroConjugate φ hφ) (u ω) : EReal) =
          ((⟪x ω, u ω⟫_ℝ : ℝ) : EReal) := by
  -- TODO: apply the local Fenchel--Young bridge pointwise once the Proposition 16.10 API is
  -- reconstructed in this file.
  sorry

/-- Helper for Proposition 16.63: coercing the packaged conjugate of `integralFunctional μ φ`
to `EReal` recovers the integral functional induced by `gammaZeroConjugate φ hφ`. -/
private theorem integralFunctionalGammaZeroConjugate_asEReal_eq
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ⊤ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    (hF : integralFunctional μ φ ∈ Γ₀(Ω →₂[μ] H)) :
    Function.asEReal ((integralFunctional μ φ)∗[hF]) =
      integralFunctional μ (gammaZeroConjugate φ hφ) := by
  -- The Chapter 13 conjugation theorem is already stated on the `EReal`-valued coercions.
  funext u
  simpa [Function.asEReal] using congrFun
    (conjugate_integralFunctional_eq_integralFunctional_gammaZeroConjugate
      (μ := μ) (φ := φ) (hφ := hφ) hfinite_or_nonneg) u

/-- Helper for Proposition 16.63: the real Fenchel--Young defect is nonnegative whenever both
terms are finite. -/
private theorem fenchelYoungDefect_nonneg
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (x u : H)
    (hx : (φ x : EReal) < ⊤)
    (hu : (((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal) < ⊤) :
    0 ≤ EReal.toReal (φ x) +
      EReal.toReal ((((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal)) -
        ⟪x, u⟫_ℝ := by
  -- TODO: recover this from the pointwise Fenchel--Young inequality after the local bridge above
  -- is repaired.
  sorry

/-- Helper for Proposition 16.63: a zero real Fenchel--Young defect forces pointwise
Fenchel--Young equality once both terms are finite. -/
private theorem fenchelYoung_eq_of_fenchelYoungDefect_eq_zero
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) {x u : H}
    (hx : (φ x : EReal) < ⊤)
    (hu : (((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal) < ⊤)
    (hdefect :
      EReal.toReal (φ x) +
          EReal.toReal ((((gammaZeroConjugate φ hφ) u : Set.Ioi (⊥ : EReal)) : EReal)) -
            ⟪x, u⟫_ℝ =
        0) :
    (φ x : EReal) + ((gammaZeroConjugate φ hφ) u : EReal) =
      ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  -- TODO: combine the nonnegativity helper with vanishing defect to get the pointwise contact
  -- equality.
  sorry

/-- Helper for Proposition 16.63: global subgradient membership puts the dual point inside the
effective domain of the conjugate integral functional. -/
private theorem effectiveDomain_integralFunctional_gammaZeroConjugate_of_mem_subdifferential
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ⊤ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    {x u : Ω →₂[μ] H} (hu : u ∈ (∂ integralFunctional μ φ) x) :
    u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ)) := by
  -- TODO: derive dual effective-domain membership from the global Fenchel--Young contact equality.
  sorry

/-- Helper for Proposition 16.63: global subgradient membership makes the real Fenchel--Young
defect integrate to zero. -/
private theorem integralFenchelYoungDefect_integral_eq_zero_of_mem_subdifferential
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ⊤ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    {x u : Ω →₂[μ] H} (hx : x ∈ effectiveDomain (integralFunctional μ φ))
    (hu_eff : u ∈ effectiveDomain (integralFunctional μ (gammaZeroConjugate φ hφ)))
    (hu : u ∈ (∂ integralFunctional μ φ) x) :
    ∫ ω,
        (EReal.toReal (φ (x ω)) +
            EReal.toReal (((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) -
          ⟪x ω, u ω⟫_ℝ) ∂μ =
      0 := by
  -- TODO: rewrite the global contact equality into the integral of the pointwise defect.
  sorry

/-- Helper for Proposition 16.63: a nonnegative real Fenchel--Young defect with integral `0`
vanishes almost everywhere, hence yields pointwise Fenchel--Young equality almost everywhere. -/
private theorem ae_fenchelYoung_eq_of_integralFenchelYoungDefect_eq_zero
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) {x u : Ω →₂[μ] H}
    (hfinite_x : ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤)
    (hfinite_u :
      ∀ᵐ ω ∂μ,
        ((((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal)) < ⊤)
    (hdefect_int :
      Integrable
        (fun ω ↦
          EReal.toReal (φ (x ω)) +
            EReal.toReal (((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) -
              ⟪x ω, u ω⟫_ℝ) μ)
    (hdefect_nonneg :
      0 ≤ᵐ[μ]
        fun ω ↦
          EReal.toReal (φ (x ω)) +
            EReal.toReal (((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) -
              ⟪x ω, u ω⟫_ℝ)
    (hdefect_zero :
      ∫ ω,
          (EReal.toReal (φ (x ω)) +
              EReal.toReal (((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) -
            ⟪x ω, u ω⟫_ℝ) ∂μ =
        0) :
    ∀ᵐ ω ∂μ,
      (φ (x ω) : EReal) + ((gammaZeroConjugate φ hφ) (u ω) : EReal) =
        ((⟪x ω, u ω⟫_ℝ : ℝ) : EReal) := by
  have hdefect_zero_ae :
      (fun ω ↦
        EReal.toReal (φ (x ω)) +
          EReal.toReal (((gammaZeroConjugate φ hφ) (u ω) : Set.Ioi (⊥ : EReal)) : EReal) -
            ⟪x ω, u ω⟫_ℝ) =ᵐ[μ] 0 := by
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hdefect_nonneg hdefect_int).1
      hdefect_zero
  -- After the defect vanishes almost everywhere, convert the real identity back to `EReal`.
  filter_upwards [hdefect_zero_ae, hfinite_x, hfinite_u] with ω hω hxω huω
  exact fenchelYoung_eq_of_fenchelYoungDefect_eq_zero
    (φ := φ) hφ hxω huω hω

/-- Helper for Proposition 16.63: global subgradient membership for `integralFunctional μ φ`
implies almost-everywhere pointwise subgradient membership for `φ`. -/
private theorem ae_mem_subdifferential_of_mem_subdifferential_integralFunctional
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ⊤ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    {x u : Ω →₂[μ] H} (hx : x ∈ effectiveDomain (integralFunctional μ φ))
    (hu : u ∈ (∂ integralFunctional μ φ) x) :
    ∀ᵐ ω ∂μ, u ω ∈ (∂ φ) (x ω) := by
  -- TODO: combine the dual effective-domain lemma with the zero-defect integral collapse.
  sorry

/-- Helper for Proposition 16.63: almost-everywhere pointwise subgradient membership for `φ`
integrates to global subgradient membership for `integralFunctional μ φ`. -/
private theorem mem_subdifferential_integralFunctional_of_ae_mem_subdifferential
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    {x u : Ω →₂[μ] H} (hx : x ∈ effectiveDomain (integralFunctional μ φ))
    (hu : ∀ᵐ ω ∂μ, u ω ∈ (∂ φ) (x ω)) :
    u ∈ (∂ integralFunctional μ φ) x := by
  -- TODO: integrate the pointwise affine support inequality on the effective-domain branch.
  sorry

/-- Proposition 16.63 (2): let `φ ∈ Γ₀(H)` and assume either `μ Set.univ < ⊤` or
`(φ 0 : EReal) = 0` together with `φ 0 ≤ φ z` for every `z : H`. Then for every
`x ∈ effectiveDomain (integralFunctional μ φ)`, the subdifferential of the integral functional is
exactly the set of `L²` fields whose values belong almost everywhere to the pointwise
subdifferential of `φ`. Proposition 13.50 already supplies the `Γ₀`-membership clause for
`integralFunctional μ φ`. -/
theorem subdifferential_integralFunctional_eq_ae_subdifferential
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ⊤ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    {x : Ω →₂[μ] H} (hx : x ∈ effectiveDomain (integralFunctional μ φ)) :
    (∂ integralFunctional μ φ) x =
      {u : Ω →₂[μ] H | ∀ᵐ ω ∂μ, u ω ∈ (∂ φ) (x ω)} := by
  -- The two directions are proved separately so Lean does not have to elaborate the full
  -- bidirectional Fenchel--Young argument in one declaration.
  ext u
  rw [Set.mem_setOf_eq]
  constructor
  · intro hu
    exact ae_mem_subdifferential_of_mem_subdifferential_integralFunctional
      (μ := μ) (φ := φ) hφ hfinite_or_nonneg hx hu
  · intro hu
    exact mem_subdifferential_integralFunctional_of_ae_mem_subdifferential
      (μ := μ) (φ := φ) hφ hx hu

/-- Membership in the subdifferential of `integralFunctional μ φ` is equivalent to almost
everywhere pointwise membership in the subdifferential of `φ`. -/
theorem mem_subdifferential_integralFunctional_iff_ae_mem_subdifferential
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ⊤ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal)))
    {x u : Ω →₂[μ] H} (hx : x ∈ effectiveDomain (integralFunctional μ φ)) :
    u ∈ (∂ integralFunctional μ φ) x ↔
      ∀ᵐ ω ∂μ, u ω ∈ (∂ φ) (x ω) := by
  -- Evaluate the set equality from Proposition 16.63(2) at the point `u`.
  simpa [subdifferential_integralFunctional_eq_ae_subdifferential
    (μ := μ) (φ := φ) hφ hfinite_or_nonneg hx] using
    (show u ∈ (∂ integralFunctional μ φ) x ↔
      u ∈ {u : Ω →₂[μ] H | ∀ᵐ ω ∂μ, u ω ∈ (∂ φ) (x ω)} from Iff.rfl)

end SubdifferentialCalculus

end

end ERealFunction
