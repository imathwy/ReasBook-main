import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_13

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

section Basic

variable {Ω : Type u}
variable {E : Type u} [AddCommMonoid E] [MeasurableSpace E]

/-- The one-step image of a point process when each particle at `x` receives an independent
increment `Y x ω` and is moved to `x + Y x ω`. -/
def randomWalkPointProcessStep
    (X : Ω → Measure E) (Y : E → Ω → E) : Ω → Measure E :=
  fun ω ↦ (X ω).map (fun x ↦ x + Y x ω)

/-- Evaluating the one-step random-walk point-process map at `ω` pushes `X ω` forward by
`x ↦ x + Y x ω`. -/
theorem randomWalkPointProcessStep_apply
    (X : Ω → Measure E) (Y : E → Ω → E) (ω : Ω) :
    randomWalkPointProcessStep X Y ω = (X ω).map (fun x ↦ x + Y x ω) := rfl

end Basic

section Poisson

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type u} [AddCommMonoid E] [MeasurableSpace E] [PseudoMetricSpace E]
  [BorelSpace E] [MeasurableAdd₂ E] [LocallyCompactSpace E]

-- Proof sketch: first mark each atom `x` of `X` with its independent increment `Y x` and apply
-- the coloring theorem to obtain a Poisson point process on `E × E` with intensity
-- `μ.prod (ν : Measure E)`. Then push this process forward along addition
-- `(x, z) ↦ x + z`; the intensity becomes the additive convolution `μ ∗ (ν : Measure E)`.
/-- A Poisson point process remains Poisson after one independent random-walk step, and the
intensity is updated by additive convolution with the increment law. -/
theorem randomWalkPointProcessStep_isPoissonPointProcess
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {X : Ω → Measure E} (hX : IsPoissonPointProcess μ P X)
    {Y : E → Ω → E} (hY_iid : IsIID Y (P : Measure Ω))
    (hY_law : ∀ x : E, HasLaw (Y x) (ν : Measure E) (P : Measure Ω))
    (hXY_indep : IndepFun X (fun ω ↦ fun x ↦ Y x ω) (P : Measure Ω)) :
    IsPoissonPointProcess (μ ∗ (ν : Measure E)) P (randomWalkPointProcessStep X Y) := sorry

-- Proof sketch: the previous theorem gives
-- `randomWalkPointProcessStep_isPoissonPointProcess` with intensity `μ ∗ (ν : Measure E)`. Hence
-- the one-step image has the same Poisson law as `X` exactly when the intensity measure is fixed by
-- convolution with `ν`.
/-- Example 24.25: for a Poisson point process of particles on an additive state space, moving each
particle by an independent increment with common law `ν` preserves the Poisson law with intensity
`μ` if and only if `μ ∗ ν = μ`. This is the one-step invariant-distribution criterion behind the
PPP random-walk example. -/
theorem poissonPointProcess_randomWalkStep_invariant_iff
    {P : ProbabilityMeasure Ω} {μ : Measure E} [SFinite μ] {ν : ProbabilityMeasure E}
    {X : Ω → Measure E} (hX : IsPoissonPointProcess μ P X)
    {Y : E → Ω → E} (hY_iid : IsIID Y (P : Measure Ω))
    (hY_law : ∀ x : E, HasLaw (Y x) (ν : Measure E) (P : Measure Ω))
    (hXY_indep : IndepFun X (fun ω ↦ fun x ↦ Y x ω) (P : Measure Ω)) :
    IsPoissonPointProcess μ P (randomWalkPointProcessStep X Y) ↔
      μ ∗ (ν : Measure E) = μ := sorry

end Poisson

end ProbabilityTheory
