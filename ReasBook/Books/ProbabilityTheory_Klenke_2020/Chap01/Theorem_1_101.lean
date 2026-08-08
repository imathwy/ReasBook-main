import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal

/-- Theorem 1.101: continuous-density transformation formula in `ℝⁿ`. If
`volume.withDensity (fun x ↦ ENNReal.ofReal (f x))` is supported on `A` and `φ` is a `C¹`
measurable equivalence sending `A` onto `B`, then the pushforward measure has density
`f (φ⁻¹ y) / |det Dφ (φ⁻¹ y)|` on `B` with respect to Lebesgue measure.

This keeps the theorem centered on the forward map `φ`; the inverse only appears through the
textbook density formula. The continuity of `f` is the source-faithful regularity hypothesis, while
the measurable-support hypothesis is the Lean-friendly expression that the density vanishes off
`A`. -/
theorem transformation_formula_in_euclidean_space {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_cont : Continuous f)
    {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A)
    (hA_null : (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) Aᶜ = 0)
    (φ : EuclideanSpace ℝ (Fin n) ≃ᵐ EuclideanSpace ℝ (Fin n))
    (hφ_image : φ '' A = B)
    (hφ_contdiff : ContDiffOn ℝ 1 φ A) :
    Measure.map φ (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      volume.withDensity
        (fun y ↦
          ENNReal.ofReal
            (B.indicator
              (fun y ↦ f (φ.symm y) / |(fderivWithin ℝ φ A (φ.symm y)).det|) y)) := by
  sorry
