import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "halfHolderExponent" => ((1 : ℝ≥0) / 2)

/-- Lévy's modulus of continuity `h(δ) = sqrt(2 δ log (1 / δ))` on positive time scales. -/
def levyModulusOfContinuity (δ : NNReal) : ℝ :=
  Real.sqrt (2 * (δ : ℝ) * Real.log (1 / (δ : ℝ)))

/-- Expanding `levyModulusOfContinuity` gives the formula `sqrt(2 δ log (1 / δ))`. -/
theorem levyModulusOfContinuity_eq (δ : NNReal) :
    levyModulusOfContinuity δ =
      Real.sqrt (2 * (δ : ℝ) * Real.log (1 / (δ : ℝ))) :=
  rfl

namespace IsBrownianMotion

-- Proof sketch: prove Lévy's modulus-of-continuity law by controlling the maximal oscillation on
-- dyadic scales, using Gaussian increment estimates with Borel--Cantelli, and then compare the
-- discrete oscillation bounds with the canonical compact-interval path oscillation on `[0,1]`.
/-- Remark 22.4: for Brownian motion `B`, Lévy's modulus of continuity satisfies
`limsup_{δ ↓ 0} V¹(ω, δ) / h(δ) = 1` almost surely on continuous sample paths `ω(t) = B_t`, where
`V¹` is the compact-interval path oscillation on `[0,1]`. -/
theorem ae_limsup_compactIntervalPathOscillation_div_levyModulus_eq_one
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
      let ω : BrownianPathSpace := ⟨processPath B w, hcont⟩
      limsup
        (fun δ : NNReal ↦
          compactIntervalOscillation 1 ω δ / levyModulusOfContinuity δ)
        (𝓝[>] (0 : NNReal)) = 1 := sorry

-- Proof sketch: if a sample path were locally `1 / 2`-Hölder on `[0,1]`, then compactness of
-- `[0,1]` would yield a uniform local `1 / 2`-Hölder bound on sufficiently short increments. This
-- forces the oscillation ratio against Lévy's modulus to converge to `0`, contradicting the
-- previous almost-sure limsup equality.
/-- Almost surely, a Brownian sample path on `[0,1]` is not locally Hölder continuous with
exponent `1 / 2`. -/
theorem ae_not_locallyHolderContinuous_oneHalf_on_unitInterval
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ w ∂μ,
      ¬ LocallyHolderWith halfHolderExponent
        (fun t : Set.Icc (0 : NNReal) 1 ↦ B t w) := sorry

end IsBrownianMotion

end ProbabilityTheory
