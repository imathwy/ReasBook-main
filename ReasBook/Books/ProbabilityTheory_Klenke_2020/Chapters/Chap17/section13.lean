import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_17_13 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

-- Proof sketch: specialize Definition 17.12 to the `ℕ`-valued stopping time
-- `fun ω ↦ (τ ω : WithTop ℕ)` and use that this stopping time never takes the value `⊤`.
/-- For an `ℕ`-valued stopping time, the canonical future path after stopping from
Definition 17.12 is the explicit shifted path `n ↦ X (τ + n)`. -/
theorem futurePathAfterStoppingTime_coe_apply
    (X : ℕ → Ω → E) (τ : Ω → ℕ) (ω : Ω) (n : ℕ) :
    futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ)) ω n = X (τ ω + n) ω := sorry

-- Proof sketch: as in Corollary 17.10, pass between the stopping-time conditional probabilities
-- of one-coordinate cylinder events and the conditional probabilities of arbitrary measurable path
-- events for the shifted process `(X_{τ+t})_t`.
/-- Remark 17.13: for a discrete-time process, with “almost surely finite” stopping times encoded
by maps `τ : Ω → ℕ`, the strong Markov property is equivalent to saying that for every stopping
time `τ` the conditional law of the post-`τ` path given the stopping-time σ-algebra agrees almost
surely with the path kernel started from the present state `X_τ`. -/
theorem hasStrongMarkovProperty_iff_conditionalFuturePathLaw_eq_pathKernel
    [StandardBorelSpace E] [Nonempty E] (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n))
    (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E)) [IsMarkovKernel κ] :
    HasStrongMarkovProperty P X κ ↔
      ∀ x (τ : Ω → ℕ),
        ∀ (hτ : IsStoppingTime (generatedFiltration X hX) fun ω ↦ (τ ω : WithTop ℕ)),
          ∀ ⦃A : Set (ℕ → E)⦄, MeasurableSet A →
            (P x)⟦futurePathAfterStoppingTime X (fun ω ↦ (τ ω : WithTop ℕ)) ⁻¹' A
              | hτ.measurableSpace⟧ =ᵐ[(P x : Measure Ω)] fun ω ↦ (κ (X (τ ω) ω)).real A := sorry

end ProbabilityTheory
