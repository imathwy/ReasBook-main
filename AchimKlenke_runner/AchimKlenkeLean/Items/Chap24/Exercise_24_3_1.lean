import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The two-parameter Dirichlet law on pairs, obtained by normalizing two independent
unit-rate Gamma coordinates with shapes `θ₁` and `θ₂`. -/
def dirichletPairMeasure (θ₁ θ₂ : ℝ) : Measure (Fin 2 → ℝ) :=
  (Measure.pi fun i : Fin 2 ↦ gammaMeasure (![θ₁, θ₂] i) 1).map
    (fun y i ↦ y i / ∑ j, y j)

-- Proof sketch: unfold `dirichletPairMeasure`; it is defined as the pushforward of the product
-- Gamma law under normalization by the total mass.
/-- Unfolding `dirichletPairMeasure θ₁ θ₂` gives the normalized-Gamma pushforward formula for the
two-parameter Dirichlet law. -/
theorem dirichletPairMeasure_def (θ₁ θ₂ : ℝ) :
    dirichletPairMeasure θ₁ θ₂ =
      (Measure.pi fun i : Fin 2 ↦ gammaMeasure (![θ₁, θ₂] i) 1).map
        (fun y i ↦ y i / ∑ j, y j) := sorry

-- Proof sketch: realize the Dirichlet pair by normalized independent Gamma coordinates and
-- identify the first coordinate as the classical Beta-Gamma ratio with parameters `θ₁` and `θ₂`.
/-- Exercise 24.3.1: if the pair `(X, 1 - X)` has the Dirichlet law with positive parameters
`θ₁, θ₂`, interpreted as `dirichletPairMeasure θ₁ θ₂`, then `X` has the Beta law with parameters
`θ₁, θ₂`. -/
theorem hasLaw_beta_of_hasLaw_dirichlet_pair
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hX : HasLaw (fun ω ↦ ![X ω, 1 - X ω]) (dirichletPairMeasure θ₁ θ₂) μ) :
    HasLaw X (betaMeasure θ₁ θ₂) μ := sorry

end ProbabilityTheory
