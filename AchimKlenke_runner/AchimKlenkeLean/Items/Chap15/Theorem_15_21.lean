import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Theorem 15.21: if `ℱ` is a tight family of probability measures on `ℝ^d`, then the set of
their characteristic functions is uniformly equicontinuous on `ℝ^d`. -/
-- Proof sketch: use tightness to choose a common compact cube carrying almost all mass for every
-- `μ ∈ ℱ`; on that compact set the oscillatory kernel `x ↦ exp (⟪x, t⟫ * I)` varies uniformly in
-- `t`, which gives a uniform bound on `|1 - charFun μ (t - s)|`; then combine this with the
-- translation identity from the preceding lemma to deduce a common modulus of continuity.
theorem tight_probabilityMeasureFamily_charFunSet_uniformEquicontinuous
    (ℱ : Set (ProbabilityMeasure E))
    (hℱ : IsTightMeasureSet ((↑) '' ℱ : Set (Measure E))) :
    (charFun '' ((↑) '' ℱ : Set (Measure E))).UniformEquicontinuous := sorry

/-- Every characteristic function of a probability measure on `ℝ^d` is uniformly continuous. -/
-- Proof sketch: apply the uniform equicontinuity theorem to the singleton family `{μ}`; singleton
-- families are tight, and then extract uniform continuity of the unique member from
-- `Set.UniformEquicontinuous.uniformContinuous_of_mem`.
theorem probabilityMeasure_charFun_uniformContinuous (μ : ProbabilityMeasure E) :
    UniformContinuous (charFun (μ : Measure E)) := sorry

end
