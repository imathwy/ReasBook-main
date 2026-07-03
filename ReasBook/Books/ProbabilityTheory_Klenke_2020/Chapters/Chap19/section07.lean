import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_19_7 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
variable {A : Set E}

-- Proof sketch: apply Theorem 19.2 to the difference `f₁ - f₂`, which is harmonic on `Aᶜ` and
-- vanishes on `A`. If the difference were nonzero, choose a positive maximum on the finite set
-- `Aᶜ`; the source-facing irreducibility owner `IsIrreducibleMarkovChain P X` gives positive
-- first-hit probability between off-boundary states, and Theorem 19.6 then forces the maximum
-- point to share its value with some boundary point, contradicting the boundary value `0`.
/-- Theorem 19.7: for an irreducible discrete-time Markov chain realization with transition matrix
`p`, if `A` is nonempty with finite complement and two functions are harmonic on `E \ A` and
agree on `A`, then they agree everywhere. -/
theorem harmonicOn_compl_ext_of_irreducible
    {f₁ f₂ : E → ℝ}
    (hirr : IsIrreducibleMarkovChain P X)
    (hA_nonempty : A.Nonempty) (hA_finite : Aᶜ.Finite)
    (hf₁ : IsHarmonicOutside (discreteMatrixKernel p) A f₁)
    (hf₂ : IsHarmonicOutside (discreteMatrixKernel p) A f₂)
    (h_eq : Set.EqOn f₁ f₂ A) :
    f₁ = f₂ := sorry

-- Proof sketch: each solution of the Dirichlet problem is harmonic on `Aᶜ` and equals the same
-- boundary datum `g` on `A`, so `harmonicOn_compl_ext_of_irreducible` applies directly.
/-- Two solutions of the same Dirichlet problem for `p - I` with the same boundary data coincide
under the irreducible Markov-chain hypotheses of Theorem 19.7. -/
theorem solvesDirichletProblem_unique
    {g f₁ f₂ : E → ℝ}
    (hirr : IsIrreducibleMarkovChain P X)
    (hA_nonempty : A.Nonempty) (hA_finite : Aᶜ.Finite)
    (hf₁ : SolvesDirichletProblem (discreteMatrixKernel p) A g f₁)
    (hf₂ : SolvesDirichletProblem (discreteMatrixKernel p) A g f₂) :
    f₁ = f₂ := sorry

end

end ProbabilityTheory
