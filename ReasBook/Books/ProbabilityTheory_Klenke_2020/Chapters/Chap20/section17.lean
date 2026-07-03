import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_20_17 (from Items/Chap20) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} {Ω : Type v}

section

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
variable [MeasurableSpace Ω]
variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {τ : Ω → Ω}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/- Example 20.17 is `source-facing`: the Chapter 20 owner theorem
`stationary_shift_ergodic_of_irreducible_positiveRecurrent` already takes the Chapter 17
irreducibility predicate `IsIrreducibleMarkovChain P X` as its main input. The occupation-frequency
limit below is a companion consequence obtained from that owner statement via Birkhoff's ergodic
theorem and the Chapter 12 owner `empiricalDistribution`. -/

-- Proof sketch: apply the Chapter 20 owner theorem
-- `stationary_shift_ergodic_of_irreducible_positiveRecurrent` for the stationary shift system
-- under the canonical stationary law `stationaryLaw P π = P_π`. For the source-facing
-- occupation count, use the Chapter 12 owner `empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)
-- ω`; its singleton mass at `x` is exactly the occupation frequency of `x` in the first `n + 1`
-- observations. Then apply Birkhoff's ergodic theorem to the observable
-- `ω ↦ 𝟙_{ {x} } (X 0 ω)` and rewrite along `X n = X 0 ∘ τ^[n]`.
/-- Companion to Example 20.17: under the stationary law `P_π`, the singleton mass of the
empirical distribution of the first `n + 1` observations, equivalently the empirical occupation
frequency of each state, converges almost surely to the invariant mass of that state. -/
theorem occupationFrequency_ae_tendsto_invariantMass_of_irreducibleMarkovChain_positiveRecurrent
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure)
    (hshift : ∀ n : ℕ, X n = X 0 ∘ τ^[n]) (x : E) :
    ∀ᵐ ω ∂stationaryLaw P π,
      Tendsto
        (fun n : ℕ ↦ (empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω) {x})
        atTop
        (nhds (π {x})) := sorry

end

end ProbabilityTheory
