import ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17
import ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_24
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
variable {Ω : Type v} [MeasurableSpace Ω]

/-- The stationary law `P_π` obtained by mixing the laws `P x` against the initial distribution
`π`. -/
def stationaryLaw (P : E → ProbabilityMeasure Ω) (π : ProbabilityMeasure E) : Measure Ω :=
  (Kernel.ofFunOfCountable fun x ↦ (P x : Measure Ω)) ∘ₘ (π : Measure E)

instance (P : E → ProbabilityMeasure Ω) :
    IsMarkovKernel (Kernel.ofFunOfCountable fun x ↦ (P x : Measure Ω)) := by
  refine ⟨fun x ↦ ?_⟩
  change IsProbabilityMeasure (P x : Measure Ω)
  infer_instance

instance (P : E → ProbabilityMeasure Ω) (π : ProbabilityMeasure E) :
    IsProbabilityMeasure (stationaryLaw P π) := by
  dsimp [stationaryLaw]
  infer_instance

-- Proof sketch: `Kernel.ofFunOfCountable` is the canonical kernel attached to the family
-- `x ↦ P x`, and `Measure.comp_eq_sum_of_countable` expands its composition with `π` into the
-- displayed stationary-law sum.
/-- The stationary law obtained by mixing the laws `P x` against `π` is exactly the weighted sum
`∑ x, π{x} P x`. -/
theorem stationaryLaw_eq_sum
    (P : E → ProbabilityMeasure Ω) (π : ProbabilityMeasure E) :
    stationaryLaw P π =
      Measure.sum fun x ↦ ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω) := by
  simpa [stationaryLaw] using
    (Measure.comp_eq_sum_of_countable :
      ((Kernel.ofFunOfCountable fun x ↦ (P x : Measure Ω)) : Kernel E Ω) ∘ₘ (π : Measure E) =
        Measure.sum fun x ↦ ((π : Measure E) ({x} : Set E)) •
          (Kernel.ofFunOfCountable fun x ↦ (P x : Measure Ω)) x)

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {τ : Ω → Ω}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/- Theorem 20.29 is `source-facing`: the main irreducibility input is the Chapter 17 owner
predicate `IsIrreducibleMarkovChain P X`. Any discrete-kernel irreducibility assumption belongs
only to a bridge that recovers this source-facing hypothesis. -/

-- Proof sketch: combine irreducibility and invariance of `π`; by Theorem 17.51 these already
-- imply positive recurrence. Then show that the stationary mixture law is preserved by the shift
-- and that every shift-invariant measurable set is trivial, exactly as in the standard
-- stationary-chain ergodicity argument.
/-- Theorem 20.29 (1): under the stationary mixture law
`P_π = ∑ x, π{x} P_x` of an irreducible positive recurrent Markov chain, the shift system is
ergodic. -/
theorem stationary_shift_ergodic_of_irreducible_positiveRecurrent
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure)
    (hshift : ∀ n : ℕ, X n = X 0 ∘ τ^[n]) :
    Ergodic τ (stationaryLaw P π) := sorry

-- Proof sketch: use the Chapter 20 owner `IsStronglyMixing` for the stationary law
-- `stationaryLaw P π = P_π`. If the chain is periodic, choose a state `x`
-- with `π{x} > 0`; then the return probabilities `p^n(x,x)` vanish on infinitely many times, so
-- the cylinder event `{X₀ = x}` violates strong mixing. Conversely, if the chain is aperiodic,
-- approximate measurable events by finite-cylinder events and use the Markov property together
-- with convergence of the `n`-step transition probabilities to `π`; positive recurrence is again
-- already forced by `hirr` and `hπ` via Theorem 17.51.
/-- Theorem 20.29 (2): for the stationary shift system of an irreducible positive recurrent
Markov chain, mixing is equivalent to aperiodicity of the transition kernel. -/
theorem stationary_shift_mixing_iff_aperiodic_of_irreducible_positiveRecurrent
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure)
    (hshift : ∀ n : ℕ, X n = X 0 ∘ τ^[n]) :
    (MeasurePreserving τ (stationaryLaw P π) (stationaryLaw P π) ∧
      IsStronglyMixing τ (stationaryLaw P π)) ↔
      IsAperiodic (discreteMatrixKernel p) := sorry

end

end ProbabilityTheory
