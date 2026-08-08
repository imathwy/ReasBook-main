import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
variable {d : ℕ}

/-- A process has locally Hölder sample paths of exponent `γ` if every sample path is locally
Hölder of order `γ` on the Euclidean parameter space. -/
def HasLocallyHolderPaths (γ : ℝ≥0) (Y : EuclideanSpace ℝ (Fin d) → Ω → E) : Prop :=
  ∀ ω : Ω, ∀ x : EuclideanSpace ℝ (Fin d),
    ∃ s : Set (EuclideanSpace ℝ (Fin d)), s ∈ 𝓝 x ∧
      ∃ C : ℝ≥0, HolderOnWith C γ (fun t ↦ Y t ω) s

-- Proof sketch: apply the Kolmogorov--Chentsov argument on each cube `[-T,T]^d`, where the
-- increment estimate has exponent `d + β`, to obtain a `γ`-Hölder modification on that cube for
-- every `γ < β / α`. Then use consistency of the cube restrictions together with the modification
-- property to glue these local versions into one process on `ℝ^d` whose sample paths are locally
-- `γ`-Hölder everywhere.
/-- Exercise 21.1.1: under the multidimensional Kolmogorov--Chentsov moment bound from Remark
21.7 on every cube `[-T,T]^d`, a process indexed by `ℝ^d` admits a modification whose sample
paths are locally Hölder-continuous of every order `γ ∈ (0, β / α)`. -/
theorem exists_locallyHolderWith_version_of_euclidean_moment_bound
    (μ : Measure Ω) (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β γ : ℝ≥0}
    (hα : 0 < α) (hβ : 0 < β)
    (hγ₀ : 0 < γ) (hγ : γ < β / α)
    (hMoment :
      ∀ T : ℝ, 0 < T →
        ∃ C : ℝ≥0, ∀ s t : EuclideanSpace ℝ (Fin d),
          (∀ i : Fin d, |s i| ≤ T) →
          (∀ i : Fin d, |t i| ≤ T) →
            ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
              (C : ℝ≥0∞) * (ENNReal.ofReal ‖t - s‖) ^ (((d : ℝ≥0) + β : ℝ))) :
    ∃ Y : EuclideanSpace ℝ (Fin d) → Ω → E,
      (∀ t : EuclideanSpace ℝ (Fin d), X t =ᵐ[μ] Y t) ∧
        HasLocallyHolderPaths γ Y := sorry

end ProbabilityTheory
