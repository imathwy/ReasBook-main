import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_25_13 (from Items/Chap25) -/
open MeasureTheory
open scoped ENNReal

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

section GlobalItoRealization

variable {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Process}
variable [hIto : BrownianItoIntegral μ ℱ W]
variable {τ : Ω → ENNReal} {H G : Process}

-- Proof sketch: first prove the identity for predictable simple processes from the defining Itô
-- sums, then pass to `MemPredictableStepProcessClosure ℱ μ H` by `L²` approximation and the
-- continuity of the integral map from Theorem 25.11.
/-- Lemma 25.13 (1): for a stopping time `τ` and an integrand `H` in the `L²`-closure of the
predictable simple processes, the stopped canonical Brownian Itô process attached to `H` agrees
almost surely with the terminal Brownian Itô integral of the cutoff integrand
`processBeforeStoppingTime H τ`. -/
theorem stopped_brownianIntegral_ae_eq_integral_stoppedIntegrand
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H) :
    stoppedValue
        (brownianItoIntegralTruncatedProcess W hH.toClosure)
        τ =ᵐ[μ]
      hIto.toContinuousLinearMap
        ((hH.processBeforeStoppingTime hτ).toClosure) := sorry

-- Proof sketch: on the event `{τ ≥ t}`, the cutoff integrand satisfies `H^(τ)_s = H_s` for every
-- `s ≤ t`, so the finite-horizon integral identity follows from part (1) applied to `min τ t`.
/-- Lemma 25.13 (2): for each deterministic time `t`, on the event `{τ ≥ t}` the canonical
Brownian Itô process of `H` agrees almost surely with the canonical Brownian Itô process of the
cutoff integrand `processBeforeStoppingTime H τ`. -/
theorem brownianIntegral_ae_eq_integral_stoppedIntegrand_on_event
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (t : NNReal) :
    brownianItoIntegralTruncatedProcess W
        hH.toClosure t =ᵐ[μ.restrict {ω | (t : ENNReal) ≤ τ ω}]
      brownianItoIntegralTruncatedProcess W
        ((hH.processBeforeStoppingTime hτ).toClosure) t := sorry

-- Proof sketch: if the cutoff integrands agree, apply part (1) to both `H` and `G` and compare
-- the resulting terminal stopped-integrand integrals.
/-- Lemma 25.13 (3): if two admissible integrands have the same cutoff integrand before the
stopping time `τ`, then their Itô integrals up to `τ` are almost surely equal. -/
theorem stopped_brownianIntegral_congr
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (hG : MemPredictableStepProcessClosure ℱ μ G)
    (hcutoff : processBeforeStoppingTime H τ = processBeforeStoppingTime G τ) :
    stoppedValue
        (brownianItoIntegralTruncatedProcess W hH.toClosure)
        τ =ᵐ[μ]
      stoppedValue
        (brownianItoIntegralTruncatedProcess W hG.toClosure)
        τ := sorry

-- Proof sketch: the textbook hypothesis implies equality of the cutoff integrands by
-- `processBeforeStoppingTime_congr`, so the canonical cutoff-based congruence theorem applies.
/- Source-facing form of Lemma 25.13 (3): if two admissible integrands `H` and `G` agree at all
times up to the stopping time `τ`, then their Itô integrals up to `τ` are almost surely equal. -/
theorem stopped_brownianIntegral_congr_of_forall_le
    (hτ : IsStoppingTime ℱ τ)
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    (hG : MemPredictableStepProcessClosure ℱ μ G)
    (hEq : ∀ (t : NNReal) ω, (t : ENNReal) ≤ τ ω → H t ω = G t ω) :
    stoppedValue
        (brownianItoIntegralTruncatedProcess W hH.toClosure)
        τ =ᵐ[μ]
      stoppedValue
        (brownianItoIntegralTruncatedProcess W hG.toClosure)
        τ := sorry

end GlobalItoRealization

end ProbabilityTheory
