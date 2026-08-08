import Mathlib
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [mE : MeasurableSpace E]

/-- The finite prefix of a discrete-time process up to time `k`. -/
def pastPath (X : ℕ → Ω → E) (k : ℕ) : Ω → Fin (k + 1) → E :=
  fun ω i ↦ X i ω

-- Proof sketch: unfold `futurePath`; it is the shifted coordinate map of the process.
/-- Evaluating the future path at time `n` reads off the coordinate `X (n + k)`. -/
theorem futurePath_apply {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
    (X : ℕ → Ω → E) (k : ℕ) (ω : Ω) (n : ℕ) :
    futurePath X k ω n = X (n + k) ω := rfl

-- Proof sketch: unfold `pastPath`; it packages the coordinates `X 0, ..., X k` into one finite
-- history map.
/-- Evaluating the past path at index `i` reads off the coordinate `X i`. -/
theorem pastPath_apply {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
    (X : ℕ → Ω → E) (k : ℕ) (ω : Ω) (i : Fin (k + 1)) :
    pastPath X k ω i = X i ω := rfl

variable [StandardBorelSpace E] [Nonempty E]

-- Proof sketch: the forward direction upgrades the coordinate-wise Markov property to equality of
-- regular conditional distributions on path space by testing cylinder sets; the converse tests the
-- equality of conditional path laws on one-coordinate cylinders.
/-- Corollary 17.10: under the canonical path-law kernel
`κ x = 𝓛_x[(X_n)_{n \in \mathbb{N}_0}]`, a discrete-time process is a Markov chain if and only if
for every `k` the regular conditional law of its future path `(X_{n+k})_n` given the finite
history `(X_0, \ldots, X_k)` agrees almost surely with the path law started from the present state
`X_k`. -/
theorem isTimeHomogeneousMarkovProcess_iff_condDistrib_futurePath_eq_pathKernel
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω)) :
    IsTimeHomogeneousMarkovProcess X P κ ↔
      ∀ x k,
        (fun ω ↦ condDistrib (futurePath X k) (pastPath X k) (P x : Measure Ω)
          (pastPath X k ω)) =ᵐ[(P x : Measure Ω)] fun ω ↦ κ (X k ω) := sorry

end ProbabilityTheory
