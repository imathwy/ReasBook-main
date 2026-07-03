import ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_31

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

namespace ProbabilityTheory

/-- The ambient setup for the normalized jump partition `\widetilde m`, the total mass `M₁`,
and the Poisson--Dirichlet laws appearing in Theorem 24.36. -/
structure PoissonDirichletStableContext (Ω : Type u) [MeasurableSpace Ω] where
  /-- The underlying probability measure `\mathbf P`. -/
  P : ProbabilityMeasure Ω
  /-- The normalized decreasing jump sequence `\widetilde m`. -/
  normalizedJumps : Ω → MassPartition
  /-- The total mass `M₁` used for the negative-moment tilt. -/
  totalMassAtOne : Ω → NNReal
  /-- The Poisson--Dirichlet family `\mathrm{PD}_{\alpha,\theta}` from Definition 24.34. -/
  poissonDirichletDistribution : ℝ → ℝ → ProbabilityMeasure MassPartition

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: this is the identification of the normalized jump partition of the underlying
-- stable subordinator with the `(\alpha,0)` Poisson--Dirichlet law.
/-- Theorem 24.36 (1): for `0 < α < 1`, the normalized jump partition `\widetilde m` has law
`\mathrm{PD}_{\alpha,0}`. -/
theorem normalized_jump_partition_hasLaw_poissonDirichlet_zero
    (ctx : PoissonDirichletStableContext Ω) {α : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    HasLaw ctx.normalizedJumps
      (ctx.poissonDirichletDistribution α 0 : Measure MassPartition) (ctx.P : Measure Ω) := sorry

-- Proof sketch: tilt the base law `\mathbf P` by the weight `M₁^{-θ}`, normalize by its
-- expectation, and push forward along `\widetilde m`; this yields the Radon--Nikodym formula for
-- `\mathrm{PD}_{\alpha,\theta}` with respect to `\mathrm{PD}_{\alpha,0}`.
/-- Theorem 24.36 (2): if `0 < α < 1` and `θ > -α`, then `\mathrm{PD}_{\alpha,\theta}` is
absolutely continuous with respect to the pushforward law `\mathbf P[\widetilde m \in \cdot]`
(hence, by part (1), with respect to `\mathrm{PD}_{\alpha,0}`), and its measurable-set masses are
obtained by the normalized negative-moment tilt by `M₁^{-θ}`. -/
theorem poissonDirichletDistribution_absolutelyContinuous_zero_and_apply_eq_negative_power_tilt
    (ctx : PoissonDirichletStableContext Ω) {α θ : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hθ : -α < θ) :
    (ctx.poissonDirichletDistribution α θ : Measure MassPartition) ≪
      Measure.map ctx.normalizedJumps (ctx.P : Measure Ω) ∧
    ∀ ⦃A : Set MassPartition⦄, MeasurableSet A →
      (ctx.poissonDirichletDistribution α θ : Measure MassPartition) A =
        (∫⁻ ω in ctx.normalizedJumps ⁻¹' A,
            ENNReal.ofReal ((ctx.totalMassAtOne ω : ℝ) ^ (-θ)) ∂(ctx.P : Measure Ω)) /
          ∫⁻ ω, ENNReal.ofReal ((ctx.totalMassAtOne ω : ℝ) ^ (-θ)) ∂(ctx.P : Measure Ω) := sorry

end ProbabilityTheory
