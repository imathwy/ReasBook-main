import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_17_56 (from Items/Chap17) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [PolishSpace E]

-- Proof sketch: realize each law `μ` and `μₙ` as the pushforward of a common canonical source
-- space using the standard-Borel representation theorem, then refine the realizations so that the
-- weak convergence hypothesis yields almost-sure convergence on that common space.
/-- Theorem 17.56: if `μₙ` converges weakly to `μ` in the space of probability measures on a Polish
space `E`, then there exists a single probability space carrying random variables `X, X₁, X₂, ...`
whose laws are `μ, μ₁, μ₂, ...`, respectively, and such that `Xₙ → X` almost surely. The law
identities are expressed by the canonical owner predicate `HasLaw`. -/
theorem exists_skorohod_coupling
    (μ : ProbabilityMeasure E) (μn : ℕ → ProbabilityMeasure E)
    (hμn : Tendsto μn atTop (𝓝 μ)) :
    ∃ (Ω : Type v) (_mΩ : MeasurableSpace Ω) (P : ProbabilityMeasure Ω)
      (X : Ω → E) (Xn : ℕ → Ω → E),
      HasLaw X μ P ∧
        (∀ n : ℕ, HasLaw (Xn n) (μn n) P) ∧
        (∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n ↦ Xn n ω) atTop (𝓝 (X ω))) := sorry

end ProbabilityTheory
