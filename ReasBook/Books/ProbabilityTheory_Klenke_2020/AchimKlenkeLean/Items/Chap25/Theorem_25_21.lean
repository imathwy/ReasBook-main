import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.ContinuousLocalMartingaleIto

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

-- Proof sketch: represent the centered martingale `M - M 0` on an extension as a Brownian local
-- Itô integral with coefficient `sqrt (d⟨M⟩ / dt)`, apply the Brownian local Itô construction
-- there to the integrand `H * sqrt (d⟨M⟩ / dt)`, and descend the resulting process back to the
-- original space.
/-- Theorem 25.21 in canonical project-facing form: if `M` is a continuous local martingale and
its canonical square variation is absolutely continuous with density `d⟨M⟩ / dt`, then every
progressively measurable integrand `H` with `∫_0^T H_s^2 (d⟨M⟩_s / ds) ds < ∞` almost surely on
each finite horizon admits an Itô integral process `N_t = ∫_0^t H_s dM_s`, encoded by the
canonical source-facing relation `IsContinuousLocalMartingaleItoIntegral hbr H N`. The owner-level
consequences that `N` is a continuous local martingale and that
`⟨N⟩_t = ∫_0^t H_s^2 d⟨M⟩_s` are recorded separately below as namespace lemmas on that relation.
The source-facing approximation-by-elementary-integrands clause is recorded separately below as
`continuousLocalMartingaleItoIntegral_tendstoInMeasure_of_predictableSimpleApproximation`. -/
theorem exists_continuousLocalMartingaleItoIntegral
    {M H : Process}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2 * (hbr.density s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : Process, IsContinuousLocalMartingaleItoIntegral hbr H N := sorry

-- Proof sketch: represent the centered martingale `M - M 0` on an extension as a Brownian local
-- martingale, apply the Brownian local Itô approximation theorem rowwise to the weighted integrands
-- `H^{n,m} * sqrt (d⟨M⟩ / dt)`, identify the inner limit with the stopped stochastic integral
-- against `M`, and then let the localizing sequence tend to `∞`.
/-- The source-facing convergence clause of Theorem 25.21: if `N_t = ∫_0^t H_s dM_s` is realized
by `IsContinuousLocalMartingaleItoIntegral hbr H N`, then for every localizing sequence
`τₙ ↑ ∞` recorded by `IsItoLocalizingSequence M hbr H τSeq` and every family of predictable simple
integrands `Hⁿᵐ ∈ 𝓔` recorded by
`IsPredictableSimpleItoApproximation M hbr (processBeforeStoppingTime H τₙ) (Hnm n)`, the
canonical elementary Itô integrals `((hHnm n).integralSequence m)` converge
in probability to `N` through the expected iterated `m`-then-`n`
limiting procedure. -/
theorem continuousLocalMartingaleItoIntegral_tendstoInMeasure_of_predictableSimpleApproximation
    {M H N : Process}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (hN : IsContinuousLocalMartingaleItoIntegral hbr H N)
    (τSeq : ℕ → Ω → NNReal)
    (hτSeq : IsItoLocalizingSequence M hbr H τSeq)
    (Hnm : ℕ → ℕ → PredictableSimpleProcess ℱ)
    (hHnm :
      ∀ n : ℕ,
        IsPredictableSimpleItoApproximation M hbr
          (processBeforeStoppingTime H fun ω ↦ (τSeq n ω : ENNReal))
          (Hnm n)) :
    (∀ n : ℕ, ∀ t : NNReal,
      TendstoInMeasure μ
        (fun m : ℕ ↦ (hHnm n).integralSequence m t)
        atTop
        ((stoppedProcess N fun ω ↦ (τSeq n ω : ENNReal)) t)) ∧
      ∀ t : NNReal,
        TendstoInMeasure μ
          (fun n : ℕ ↦ (stoppedProcess N fun ω ↦ (τSeq n ω : ENNReal)) t)
          atTop
          (N t) := sorry

namespace IsContinuousLocalMartingaleItoIntegral

variable {M H N : Process}

-- Proof sketch: unwind the Brownian-extension witness in
-- `IsContinuousLocalMartingaleItoIntegral`, where the centered driver `M - M 0` is realized on an
-- extension, use Corollary 25.19 on the extension to identify the pulled-back process as a
-- continuous local martingale, and descend the statement to the original filtered probability
-- space.
/-- Any process realizing the Itô integral of `H` against a continuous local martingale `M` is
itself a continuous local martingale. -/
theorem isContinuousLocalMartingale
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (hN : IsContinuousLocalMartingaleItoIntegral hbr H N) :
    IsContinuousLocalMartingale ℱ μ N := sorry

-- Proof sketch: after pulling back to the Brownian representation encoded in `hN`, apply the
-- Brownian bracket computation from Corollary 25.19 to the Brownian integrand
-- `H * sqrt (d⟨M⟩ / dt)` and rewrite the result as `∫ H² d⟨M⟩`.
/-- Any process realizing the Itô integral of `H` against `M` has square variation
`bracketDensityIntegralUpTo hbr H`, i.e. `t ↦ ∫_0^t H_s^2 d⟨M⟩_s` in density form. -/
theorem hasSquareVariation
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (hN : IsContinuousLocalMartingaleItoIntegral hbr H N) :
    IsContinuousSquareVariationProcess ℱ μ N (bracketDensityIntegralUpTo hbr H) := sorry

-- Proof sketch: derive continuity of `N` from
-- `hN.isContinuousLocalMartingale`, then apply uniqueness of the continuous square-variation
-- process.
/-- The canonical square-variation process of an Itô integral against `M` is
`bracketDensityIntegralUpTo hbr H`. This is the thin bridge from the source-facing relation
`IsContinuousLocalMartingaleItoIntegral hbr H N` to the canonical bracket object
`continuousSquareVariationProcess`. -/
theorem continuousSquareVariationProcess_eq
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (hN : IsContinuousLocalMartingaleItoIntegral hbr H N) :
    continuousSquareVariationProcess hN.isContinuousLocalMartingale =
      bracketDensityIntegralUpTo hbr H := sorry

end IsContinuousLocalMartingaleItoIntegral

end ProbabilityTheory
