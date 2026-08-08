import Mathlib
import ProbabilityTheory_Klenke_2020.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

section

variable (Y : ℕ → Ω → ℝ)

-- Proof sketch: stop the partial-sum process at its first entrance into `[a, ∞)` before time
-- `n`, reflect the future increments using the symmetry in law `Y₀ ≈ -Y₀`, and compare the
-- reflected endpoint distribution with the events `{a ≤ Sₙ}` and `{Sₙ = a}`.
/-- Theorem 17.15 (1): reflection principle. For a `0`-based i.i.d. real increment sequence
`Y 0, Y 1, ...` with symmetric law, the probability that one of the first `n` partial sums reaches
the level `a > 0` is bounded by `2 P[Sₙ ≥ a] - P[Sₙ = a]`, where `Sₙ = partialSum Y n`. This is
the textbook statement for `X₀ = 0` and `X_n = Y₁ + ⋯ + Y_n`, with Lean's `Y 0` representing the
textbook `Y₁`. The i.i.d. hypothesis is expressed via the chapter's canonical owner abstraction
`IsIID`. -/
theorem reflectionPrinciple_partialSum_le
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    (n : ℕ) (a : ℝ) (ha : 0 < a) :
    μ.real (oneSidedHitEvent Y n a) ≤
      2 * μ.real {ω | a ≤ partialSum Y n ω} - μ.real {ω | partialSum Y n ω = a} := sorry

-- Proof sketch: in the nearest-neighbor case `Y_i ∈ {-1, 0, 1}` almost surely, the first hitting
-- time of a positive integer level lands exactly at that level, so the reflected path argument
-- from the inequality case becomes exact and yields equality.
/-- Theorem 17.15 (2): if the common increment law is supported on `{-1, 0, 1}` almost surely,
then the reflection-principle bound is sharp for positive integer levels. -/
theorem reflectionPrinciple_partialSum_eq_of_steps_mem_neg_one_zero_one
    (hY_iid : IsIID Y μ)
    (hY_symm : IdentDistrib (Y 0) (fun ω ↦ -Y 0 ω) μ μ)
    (hY_step_support : ∀ᵐ ω ∂μ, Y 0 ω ∈ ({(-1 : ℝ), 0, 1} : Set ℝ))
    (n : ℕ) (a : ℕ) (ha : 0 < a) :
    μ.real (oneSidedHitEvent Y n a) =
      2 * μ.real {ω | (a : ℝ) ≤ partialSum Y n ω} -
        μ.real {ω | partialSum Y n ω = (a : ℝ)} := sorry

end

end ProbabilityTheory
