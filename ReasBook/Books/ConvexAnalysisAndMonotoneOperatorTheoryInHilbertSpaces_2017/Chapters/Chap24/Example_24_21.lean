import Mathlib
import BauschkeLean.Chap09.Proposition_9_40
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap24.Example_24_20
import BauschkeLean.Chap24.Proposition_24_13

open MeasureTheory
open scoped ENNReal InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

-- Domain sampling:
-- - `source-facing`: `f = integralFunctional P norm.toEReal`, i.e. `f(X) = 𝔼 |X|`.
-- - `core/canonical`: `integralFunctional P φ` from `Chap09/Proposition_9_40.lean`.
-- - `bridge/view`: the scaled kernel `scaledNormKernelOfPos γ` from `Chap12/Definition_12_16.lean`,
--   the pointwise soft-threshold formula from `Chap24/Example_24_20.lean`, and the `L²` transfer
--   theorem from `Chap24/Proposition_24_13.lean`.
-- The main example is therefore stated on the unscaled owner `f`, with the scaled-integrand form
-- kept only as a companion bridge.

section MeasureSpace

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

private theorem scaledNormKernelOfPos_zero_eq_zero_and_nonneg (γ : PosReal) :
    ((scaledNormKernelOfPos γ (0 : ℝ) : Set.Ioi (⊥ : EReal)) : EReal) = 0 ∧
      ∀ x : ℝ,
        ((scaledNormKernelOfPos γ (0 : ℝ) : Set.Ioi (⊥ : EReal)) : EReal) ≤
          ((scaledNormKernelOfPos γ x : Set.Ioi (⊥ : EReal)) : EReal) := by
  constructor
  · simp
  · intro x
    rw [scaledNormKernelOfPos_apply, scaledNormKernelOfPos_apply]
    exact_mod_cast
      (mul_le_mul_of_nonneg_left (by simp) γ.2.le)

/-- The integral norm functional `X ↦ ∫ |X| dP` belongs to `Γ₀(L²(P))`. -/
theorem integralFunctional_norm_mem_gammaZero :
    integralFunctional P ((norm : ℝ → ℝ).toEReal) ∈ Γ₀(Ω →₂[P] ℝ) := by
  have hnorm :
      scaledNormKernelOfPos (1 : PosReal) = ((norm : ℝ → ℝ).toEReal) := by
    ext x
    rw [scaledNormKernelOfPos_apply]
    simp [Function.toEReal_apply]
  have hscaled :
      ((scaledNormKernelOfPos (1 : PosReal)) : ℝ → Set.Ioi (⊥ : EReal)) ∈ Γ₀(ℝ) := by
    simpa using scaledNormKernelOfPos_mem_gammaZero (1 : PosReal)
  simpa [hnorm] using
    (integralFunctional_mem_gammaZero P
      ((scaledNormKernelOfPos (1 : PosReal)) : ℝ → Set.Ioi (⊥ : EReal))
      hscaled
      (Or.inr (scaledNormKernelOfPos_zero_eq_zero_and_nonneg (1 : PosReal))))

/-- The integral functional induced by the scalar kernel `ξ ↦ γ |ξ|` belongs to
`Γ₀(L²(P))`. -/
theorem integralFunctional_scaledNormKernelOfPos_mem_gammaZero (γ : PosReal) :
    integralFunctional P (scaledNormKernelOfPos γ) ∈ Γ₀(Ω →₂[P] ℝ) := by
  simpa using
    (integralFunctional_mem_gammaZero P (scaledNormKernelOfPos γ)
      (scaledNormKernelOfPos_mem_gammaZero γ)
      (Or.inr (scaledNormKernelOfPos_zero_eq_zero_and_nonneg γ)))

/-- Scaling the integral norm functional by `γ` agrees with integrating the scaled norm kernel
`ξ ↦ γ |ξ|`. -/
theorem posReal_smul_integralFunctional_norm_eq_integralFunctional_scaledNormKernelOfPos
    (γ : PosReal) :
    γ • integralFunctional P ((norm : ℝ → ℝ).toEReal) =
      integralFunctional P (scaledNormKernelOfPos γ) := by
  ext X
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  rw [posReal_smul_apply, integralFunctional_coe, integralFunctional_coe]
  by_cases hX : Integrable (fun ω ↦ |X ω|) P
  · have hX_scaled : Integrable (fun ω ↦ (γ : ℝ) * |X ω|) P := hX.const_mul (γ : ℝ)
    have hbranch_norm :
        Integrable (fun ω ↦ EReal.toReal (((norm : ℝ → ℝ).toEReal) (X ω))) P ∧
          ∀ᵐ ω ∂P, ((((norm : ℝ → ℝ).toEReal) (X ω) : Set.Ioi (⊥ : EReal)) : EReal) < ⊤ := by
      constructor
      · simpa [Function.toEReal_apply, Real.norm_eq_abs] using hX
      · filter_upwards with ω
        simp [Function.toEReal_apply]
    have hbranch_scaled :
        Integrable (fun ω ↦ EReal.toReal (scaledNormKernelOfPos γ (X ω))) P ∧
          ∀ᵐ ω ∂P, ((scaledNormKernelOfPos γ (X ω) : Set.Ioi (⊥ : EReal)) : EReal) < ⊤ := by
      constructor
      · simpa [scaledNormKernelOfPos_apply, Real.norm_eq_abs] using hX_scaled
      · filter_upwards with ω
        exact EReal.coe_lt_top ((γ : ℝ) * |X ω|)
    rw [pointwiseIntegralFunctional, pointwiseIntegralFunctional]
    rw [if_pos hbranch_norm, if_pos hbranch_scaled]
    have hintegral :
        (∫ ω, EReal.toReal (scaledNormKernelOfPos γ (X ω)) ∂P : ℝ) =
          (γ : ℝ) * ∫ ω, EReal.toReal (((norm : ℝ → ℝ).toEReal) (X ω)) ∂P := by
      calc
        (∫ ω, EReal.toReal (scaledNormKernelOfPos γ (X ω)) ∂P : ℝ) =
            ∫ ω, (γ : ℝ) * EReal.toReal (((norm : ℝ → ℝ).toEReal) (X ω)) ∂P := by
              refine integral_congr_ae ?_
              filter_upwards with ω
              rw [scaledNormKernelOfPos_apply, EReal.toReal_coe]
              simp [Function.toEReal_apply, Real.norm_eq_abs]
        _ = (γ : ℝ) * ∫ ω, EReal.toReal (((norm : ℝ → ℝ).toEReal) (X ω)) ∂P := by
              rw [integral_const_mul]
    have hmul :
        ((γ : EReal) *
            ((∫ ω, EReal.toReal (((norm : ℝ → ℝ).toEReal) (X ω)) ∂P : ℝ) : EReal)) =
          ((∫ ω, EReal.toReal (scaledNormKernelOfPos γ (X ω)) ∂P : ℝ) : EReal) := by
      rw [hintegral, ← EReal.coe_mul]
    simpa using hmul
  · have hX_scaled :
        ¬ Integrable (fun ω ↦ (γ : ℝ) * |X ω|) P := by
      intro hX_scaled
      exact hX ((integrable_smul_iff hγ_ne (fun ω ↦ |X ω|)).1 hX_scaled)
    have hbranch_norm :
        ¬ (Integrable (fun ω ↦ EReal.toReal (((norm : ℝ → ℝ).toEReal) (X ω))) P ∧
            ∀ᵐ ω ∂P, ((((norm : ℝ → ℝ).toEReal) (X ω) : Set.Ioi (⊥ : EReal)) : EReal) < ⊤) := by
      intro hbranch
      exact hX (by simpa [Function.toEReal_apply, Real.norm_eq_abs] using hbranch.1)
    have hbranch_scaled :
        ¬ (Integrable (fun ω ↦ EReal.toReal (scaledNormKernelOfPos γ (X ω))) P ∧
            ∀ᵐ ω ∂P, ((scaledNormKernelOfPos γ (X ω) : Set.Ioi (⊥ : EReal)) : EReal) < ⊤) := by
      intro hbranch
      exact hX_scaled (by simpa [scaledNormKernelOfPos_apply, Real.norm_eq_abs] using hbranch.1)
    rw [pointwiseIntegralFunctional, if_neg hbranch_norm]
    rw [pointwiseIntegralFunctional, if_neg hbranch_scaled]
    simpa using EReal.coe_mul_top_of_pos γ.2

/-- Example 24.21: on a complete sigma-finite measure space, let `f(X) = ∫ |X| dP`. If an
`L²(P)` field `p` satisfies `p(ω) = sign(X(ω)) max {|X(ω)| - γ, 0}` for `P`-almost every `ω`,
then `p = Prox[γ, f, hf] X`, i.e. `p = Prox_{γ f}(X)`. -/
theorem example_24_21_eq_scaledProximityOperator_integralFunctional_norm_of_ae_eq_softThreshold
    [SigmaFinite P] [P.IsComplete]
    (X p : Ω →₂[P] ℝ) (γ : PosReal)
    (hp :
      ∀ᵐ ω ∂P, p ω = Real.sign (X ω) * max (|X ω| - (γ : ℝ)) 0) :
    p =
      Prox[
        γ,
        integralFunctional P ((norm : ℝ → ℝ).toEReal),
        integralFunctional_norm_mem_gammaZero] X := by
  have hp_pointwise :
      ∀ᵐ ω ∂P,
        p ω = Prox[scaledNormKernelOfPos γ, scaledNormKernelOfPos_mem_gammaZero γ] (X ω) := by
    simpa [example_24_20_2_proximityOperator_scaledNorm_real_eq_sign_mul_max γ] using hp
  have hscaled :
      p =
        Prox[
          integralFunctional P (scaledNormKernelOfPos γ),
          integralFunctional_scaledNormKernelOfPos_mem_gammaZero γ] X := by
    simpa using
      (eq_proximityOperator_integralFunctional_of_ae_eq_pointwise_proximityOperator
        (scaledNormKernelOfPos γ)
        (scaledNormKernelOfPos_mem_gammaZero γ)
        (Or.inr (scaledNormKernelOfPos_zero_eq_zero_and_nonneg γ))
        X p hp_pointwise)
  simpa [scaledProximityOperator,
    posReal_smul_integralFunctional_norm_eq_integralFunctional_scaledNormKernelOfPos γ] using
    hscaled

/-- Bridge form of Example 24.21: the scaled proximal map of `X ↦ ∫ |X| dP` is equivalently the
ordinary proximity operator of the integral functional induced by `ξ ↦ γ |ξ|`. -/
theorem example_24_21_eq_proximityOperator_integralFunctional_scaledNorm_of_ae_eq_softThreshold
    [SigmaFinite P] [P.IsComplete]
    (X p : Ω →₂[P] ℝ) (γ : PosReal)
    (hp :
      ∀ᵐ ω ∂P, p ω = Real.sign (X ω) * max (|X ω| - (γ : ℝ)) 0) :
    p =
      Prox[
        integralFunctional P (scaledNormKernelOfPos γ),
        integralFunctional_scaledNormKernelOfPos_mem_gammaZero γ] X := by
  simpa [scaledProximityOperator,
    posReal_smul_integralFunctional_norm_eq_integralFunctional_scaledNormKernelOfPos γ] using
    (example_24_21_eq_scaledProximityOperator_integralFunctional_norm_of_ae_eq_softThreshold
      X p γ hp)

end MeasureSpace

end

end ERealFunction
