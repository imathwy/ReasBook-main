import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The Brownian scaling transform with factor `K`, given by `t ↦ K⁻¹ B (K² t)`. -/
noncomputable def brownianScaling (B : NNReal → Ω → ℝ) (K : ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ K⁻¹ * B (⟨K ^ 2, sq_nonneg K⟩ * t) ω

namespace IsBrownianMotion

-- Proof sketch: verify the Brownian-motion axioms for the rescaled process. The starting value is
-- preserved because `B 0 = 0`; independent and stationary increments are inherited from `B` after
-- the deterministic time change `t ↦ K^2 t`; the Gaussian marginal rescales by
-- `ProbabilityTheory.gaussianReal_const_mul`; and almost-sure continuity is preserved by
-- composition with the continuous time dilation and scalar multiplication.
/-- Corollary 21.12: scaling property of Brownian motion. If `B` is a Brownian motion and
`K ≠ 0`, then the rescaled process `t ↦ K⁻¹ B (K² t)` is again a Brownian motion. -/
theorem scaling
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {K : ℝ} (hK : K ≠ 0) :
    IsBrownianMotion μ (brownianScaling B K) := sorry

end IsBrownianMotion

end ProbabilityTheory
