import Mathlib
import ProbabilityTheory_Klenke_2020.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u

noncomputable section

-- Proof sketch: take a centered real law in the Gaussian domain of attraction with finite second
-- moment but infinite first absolute moment, realize an independent sequence with this law on an
-- infinite product probability space, and then apply the one-dimensional central limit theorem to
-- the raw `√n`-normalized partial sums built from the chapter owner `partialSum`.
/- Exercise 15.5.1 is `source-facing`: it asks for an independent sequence of measurable real
random variables with infinite first absolute moments whose raw `√n`-normalized partial sums
converge in distribution. The project owner for the finite sums themselves is `partialSum`, so the
statement reuses that owner directly instead of introducing a parallel public wrapper for the same
construction. -/
/-- Exercise 15.5.1: there exists an independent sequence `X₁, X₂, ...` of real random variables
such that every absolute first moment is infinite, but the normalized sums
`(X₁ + ⋯ + X_n) / √n` converge in distribution to the standard Gaussian law. In Lean's `0`-based
indexing, these are the maps `ω ↦ (√n)⁻¹ * partialSum X n ω`. -/
theorem exists_heavyTailStandardCLTExample :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ),
      (∀ n, Measurable (X n)) ∧
        iIndepFun X P ∧
        (∀ n, ∫⁻ ω, ENNReal.ofReal |X n ω| ∂P = ⊤) ∧
        TendstoInDistribution
          (fun (n : ℕ) ω ↦ (Real.sqrt (n : ℝ))⁻¹ * partialSum X n ω)
          atTop id (fun _ ↦ P) (gaussianReal 0 1) := sorry
