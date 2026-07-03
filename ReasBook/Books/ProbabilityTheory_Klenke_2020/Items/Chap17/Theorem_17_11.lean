import ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

-- Proof sketch: the kernels `κ₁ ^ n` are stochastic by induction from `IsMarkovKernel κ₁`, the
-- zero-time kernel is `Kernel.id`, and the Chapman--Kolmogorov law is `Kernel.pow_add`.
/-- The powers of a one-step stochastic kernel form the discrete-time Markov semigroup of its
`n`-step transition kernels. -/
instance isMarkovSemigroup_kernelPowers (κ₁ : Kernel E E) [IsMarkovKernel κ₁] :
    IsMarkovSemigroup (fun n : ℕ ↦ κ₁ ^ n) := sorry

/-- Every power of a Markov kernel is again a Markov kernel. -/
instance isMarkovKernel_kernelPow (κ₁ : Kernel E E) [IsMarkovKernel κ₁] (n : ℕ) :
    IsMarkovKernel (κ₁ ^ n) := by
  induction n with
  | zero =>
      simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel E E))
  | succ n ih =>
      simpa [pow_succ] using (inferInstance : IsMarkovKernel ((κ₁ ^ n) ∘ₖ κ₁))

section

variable {Ω : Type v} [MeasurableSpace Ω]

-- Proof sketch: the hypothesis `hstart` supplies the primitive initial-state law required by
-- `IsMarkovProcessRealization`. Iterating the one-step conditional-probability identity through
-- the natural filtration then gives the full Markov property and identifies the time-`n`
-- marginals with the kernel powers `κ₁ ^ n`, so the result lands directly in the owner
-- abstraction `IsMarkovProcessRealization`.
/-- Theorem 17.11: if a discrete-time process started from `x` has one-step conditional law given
by the stochastic kernel `κ₁`, then the Markov property from Definition 17.3(iii) follows, and
the `n`-step transition kernels are the powers `κ₁ ^ n`. -/
theorem isMarkovProcessRealization_of_oneStepKernel
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (hmeas : ∀ n : ℕ, Measurable (X n))
    (hstart : ∀ x : E, (P x : Measure Ω).map (X 0) = Measure.dirac x)
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ s : ℕ,
        (P x)⟦X (s + 1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
          fun ω ↦ (κ₁ (X s ω)).real A) :
    IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) P X := sorry

end

section

variable {Ω : Type v} [MeasurableSpace Ω]
variable {Ω' : Type w} [MeasurableSpace Ω']

-- Proof sketch: this is the owner-level uniqueness statement from Theorem 17.8, specialized to
-- the canonical semigroup `n ↦ κ₁ ^ n` attached to the one-step kernel `κ₁`.
/-- Theorem 17.11: in particular, the one-step kernel `κ₁` determines the finite-dimensional
distributions of any discrete-time Markov-process realization uniquely. Equivalently, two
realizations with the same one-step kernel have the same ordered finite-dimensional distributions.
-/
theorem finiteDimensionalDistribution_eq_of_same_oneStepKernel
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    {P : E → ProbabilityMeasure Ω} {Q : E → ProbabilityMeasure Ω'}
    {X : ℕ → Ω → E} {Y : ℕ → Ω' → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) Q Y]
    (x : E) {n : ℕ} (times : Fin (n + 1) → ℕ)
    (h_zero : times 0 = 0) (htimes : StrictMono times) :
    (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
      (Q x : Measure Ω').map (fun ω i ↦ Y (times i) ω) := sorry

end

end ProbabilityTheory
