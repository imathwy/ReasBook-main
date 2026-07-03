import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_20_14 (from Items/Chap20) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {τ : Ω → Ω} {f : Ω → ℝ}

-- Proof sketch: apply the individual ergodic theorem in the measure-preserving system
-- `(Ω, P, τ)` to the integrable observable `f`. The almost-sure limit is the conditional
-- expectation of `f` onto the invariant σ-algebra `MeasurableSpace.invariants τ`.
/-- Theorem 20.14: for an integrable observable on a probability space with a
measure-preserving transformation `τ`, the Birkhoff averages converge almost surely to the
conditional expectation onto the invariant σ-algebra of `τ`. -/
theorem birkhoffAverage_tendsto_ae_condExp_invariants
    (hτ : MeasurePreserving τ P P) (hf : Integrable f P) :
    ∀ᵐ ω ∂P,
      Tendsto (birkhoffAverage ℝ τ f · ω) atTop
        (nhds ((P[f | MeasurableSpace.invariants τ]) ω)) := sorry

-- Proof sketch: combine the main convergence statement with the characterization of ergodicity by
-- triviality of the invariant σ-algebra, so that `P[f | MeasurableSpace.invariants τ]` is almost
-- surely the constant expectation `P[f]`.
/-- Under ergodicity, the Birkhoff averages converge almost surely to the expectation of the
observable. -/
theorem birkhoffAverage_tendsto_ae_expectation_of_ergodic
    (hτ : Ergodic τ P) (hf : Integrable f P) :
    ∀ᵐ ω ∂P,
      Tendsto (birkhoffAverage ℝ τ f · ω) atTop
        (nhds (P[f])) := sorry
