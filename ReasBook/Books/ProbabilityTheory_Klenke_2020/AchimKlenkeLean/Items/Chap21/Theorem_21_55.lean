import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open Set
open scoped ENNReal

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

-- Proof sketch: for a fixed `t > 0`, reduce by Brownian scaling to the unit interval and consider
-- the dyadic partial variations `Yₙ = ∑ᵢ |W_{i 2^{-n}} - W_{(i-1) 2^{-n}}|`. Their expectations
-- grow like `2^(n / 2)` while their variances stay bounded, so Chebyshev plus Borel--Cantelli
-- gives `Yₙ → ∞` almost surely. Since each `Yₙ` is bounded above by the total variation on
-- `[0,t]`, the path variation on `[0,t]` is almost surely infinite.
/-- Theorem 21.55: for a Brownian motion `W`, the total variation of almost every sample path on
each initial interval `[0, t]` with `t > 0` is infinite. -/
theorem ae_infiniteVariationOn_Icc
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {t : NNReal} (ht : 0 < t) :
    ∀ᵐ ω ∂μ, eVariationOn (fun s : NNReal ↦ W s ω) (Icc 0 t) = ∞ := sorry

/-- For Brownian motion, almost every sample path fails the chapter's canonical local-finite-
variation owner property `LocallyBoundedVariationOn ... univ`. This is the owner-level reformulation
of Theorem 21.55 via Definition 21.52. -/
theorem ae_not_locallyBoundedVariationOn_univ
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W) :
    ∀ᵐ ω ∂μ, ¬ LocallyBoundedVariationOn (fun s : NNReal ↦ W s ω) univ := by
  have hunit :
      ∀ᵐ ω ∂μ, eVariationOn (fun s : NNReal ↦ W s ω) (Icc 0 (1 : NNReal)) = ∞ :=
    hW.ae_infiniteVariationOn_Icc zero_lt_one
  filter_upwards [hunit] with ω htop
  intro hloc
  exact (show BoundedVariationOn (fun s : NNReal ↦ W s ω) (Icc 0 1) from by
    simpa using hloc 0 1 (by simp) (by simp)) htop

end IsBrownianMotion

end ProbabilityTheory
