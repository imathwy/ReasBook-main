import AchimKlenkeLean.Items.Chap12.Definition_12_6
import AchimKlenkeLean.Items.Chap12.Remark_12_2
import AchimKlenkeLean.Items.Chap12.Remark_12_9
import AchimKlenkeLean.Items.Chap07.Definition_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {μ : Measure Ω}

section

variable {k : ℕ} {X : ℕ → Ω → E} {φ : (Fin k → E) → ℝ}

local notation "Xseq" => Function.swap X
local notation "ψ" => (fun x : ℕ → E ↦ φ (fun i ↦ x i))
local notation "Y" => ψ ∘ Xseq
local notation "G" => μ[Y | exchangeableSigmaAlgebra Xseq]

-- Proof sketch: apply Theorem 12.10 to identify each permutation average with the conditional
-- expectation onto the finite exchangeable `σ`-algebra, then use Theorem 12.14 together with the
-- chapter owner notion `TendstoInLp` to obtain almost-sure and `L¹` convergence to the
-- expectation onto the limiting exchangeable `σ`-algebra. The limit is tail-measurable because
-- changing finitely many coordinates has asymptotically negligible effect on the permutation
-- average, so the two conditional expectations agree almost everywhere.
/-- Theorem 12.17: for an exchangeable `E`-valued sequence `X`, the permutation averages attached
to a measurable integrable `k`-variable test function `φ` converge almost surely and in `L¹` to a
common limit, and that limit is both the conditional expectation onto the exchangeable
`σ`-algebra and the conditional expectation onto the tail `σ`-algebra. -/
theorem exchangeableAverage_limit_of_isExchangeable (hX : IsExchangeable X μ)
    (hφ_meas : Measurable φ) (hφ_int : Integrable Y μ) :
    G =ᵐ[μ] μ[Y | tailRandomVariableMeasurableSpace X] ∧
      (∀ᵐ ω ∂μ,
        Tendsto (fun n ↦ exchangeableAverage n ψ (Xseq ω)) atTop
          (nhds (G ω))) ∧
      TendstoInLp 1 μ (fun n ↦ exchangeableAverage n ψ ∘ Xseq) G := sorry

-- Proof sketch: pass from the owner `TendstoInLp` statement to its `eLpNorm` bridge via
-- `TendstoInLp.tendsto_eLpNorm`, then rewrite the standard `p = 1` identity with the integral of
-- the absolute value.
/-- Bridge companion to Theorem 12.17: the canonical `L¹` convergence statement can be rewritten
as convergence of the integral of the absolute difference. -/
theorem exchangeableAverage_tendsto_integral_abs_sub_condexp_exchangeable
    (hX : IsExchangeable X μ) (hφ_meas : Measurable φ) (hφ_int : Integrable Y μ) :
    Tendsto
      (fun n ↦ ∫ ω, |exchangeableAverage n ψ (Xseq ω) - G ω| ∂μ)
      atTop (nhds 0) := sorry

end
