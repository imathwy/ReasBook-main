import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_21_72 (from Items/Chap21) -/
open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "PathSpace" => C(NNReal, ℝ)

-- Proof sketch: apply the continuous local martingale quadratic-variation theorem to the
-- canonical bracket `⟨X⟩[hX]`. If that bracket vanishes almost
-- surely, then `X ^ 2` is a local martingale, and the positivity of `(X_t - X_0)^2` forces all
-- increments to vanish almost surely, simultaneously in `t`.
/-- Corollary 21.72: if a continuous local martingale has almost surely vanishing canonical
square variation, then it is almost surely constant in time. -/
theorem ae_eq_initial_of_ae_squareVariation_eq_zero
    (ℱ : TimeFiltration) {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hzero : ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = X 0 ω := sorry

/-- If almost every sample path of a continuous local martingale has locally finite variation, then
its canonical bracket vanishes almost surely. This is the `bridge/view` step from the source-facing
dyadic square-variation owner to the canonical bracket owner. -/
theorem ae_continuousSquareVariationProcess_eq_zero_of_ae_locallyFiniteVariation
    (ℱ : TimeFiltration) {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hfv :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ X t ω, hX.continuous ω⟩ : PathSpace) Set.univ) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, (⟨X⟩[hX]) t ω = 0 := by
  filter_upwards
    [ae_hasSquareVariationAlong_continuousSquareVariationProcess hX, hfv]
    with ω hsq hvar
  have hzero_sq :
      HasSquareVariationAlong ⟨fun t ↦ X t ω, hX.continuous ω⟩ 0 :=
    hasSquareVariationAlong_zero_of_locallyFiniteVariation hvar
  have hzero :
      (fun t ↦ (⟨X⟩[hX]) t ω) = 0 :=
    squareVariation_eq_zero_of_locallyFiniteVariation hsq hvar
  intro t
  simpa [Pi.zero_apply] using congrArg (fun f : NNReal → ℝ ↦ f t) hzero

-- Proof sketch: first use the owner bridge
-- `ae_hasSquareVariationAlong_continuousSquareVariationProcess` together with Corollary 21.63 to
-- show that the canonical bracket vanishes almost surely. Then invoke
-- `ae_eq_initial_of_ae_squareVariation_eq_zero`.
/-- If the sample paths of a continuous local martingale have locally finite variation almost
surely, then the martingale is almost surely constant in time. -/
theorem ae_eq_initial_of_ae_locallyFiniteVariation
    (ℱ : TimeFiltration) {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hfv :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ X t ω, hX.continuous ω⟩ : PathSpace) Set.univ) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = X 0 ω :=
  ae_eq_initial_of_ae_squareVariation_eq_zero ℱ hX
    (ae_continuousSquareVariationProcess_eq_zero_of_ae_locallyFiniteVariation ℱ hX hfv)

end ProbabilityTheory
