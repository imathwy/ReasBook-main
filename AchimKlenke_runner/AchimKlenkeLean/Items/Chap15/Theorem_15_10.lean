import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

/-- The canonical embedding of the lattice `ℤ^d` into the Euclidean space `ℝ^d`. -/
abbrev latticeEmbedding {d : ℕ} (x : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ (x i : ℝ))

/-- The half-open cube `[-π, π)^d` in the coordinate model of `ℝ^d`. -/
abbrev latticeFrequencyCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {t | ∀ i, t i ∈ Set.Ico (-Real.pi) Real.pi}

-- Proof sketch: unfold `latticeFrequencyCube`.
/-- Membership in `latticeFrequencyCube d` means that every coordinate lies in `[-π, π)`. -/
theorem mem_latticeFrequencyCube_iff {d : ℕ} {t : EuclideanSpace ℝ (Fin d)} :
    t ∈ latticeFrequencyCube d ↔
      ∀ i, t i ∈ Set.Ico (-Real.pi) Real.pi := Iff.rfl

-- Proof sketch: view `μ` as a finite measure on `EuclideanSpace ℝ (Fin d)` via
-- `latticeEmbedding`, expand the characteristic function there, and integrate the exponential
-- kernel over the half-open fundamental domain `[-π, π)^d`; the orthogonality of the exponentials
-- kills every lattice point except `x`.
/-- Theorem 15.10: the point mass of a finite measure on `ℤ^d` at `x` is recovered from its
characteristic function by integrating `exp (-i⟪t, x⟫) φ_μ(t)` over `[-π, π)^d`. -/
theorem discreteFourierInversionFormula {d : ℕ} {μ : Measure (Fin d → ℤ)} [IsFiniteMeasure μ]
    (x : Fin d → ℤ) :
    (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) =
      (((2 * Real.pi : ℝ) ^ d)⁻¹ : ℂ) *
        ∫ t in latticeFrequencyCube d,
          Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
            charFun (μ.map latticeEmbedding) t ∂volume := sorry
