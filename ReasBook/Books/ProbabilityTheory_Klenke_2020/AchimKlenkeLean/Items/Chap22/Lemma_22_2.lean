import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: write `P[X ≥ x]` as the Gaussian tail integral `∫ t in Set.Ioi x, φ t` with
-- `φ(t) = (2π)^(-1/2) exp (-t^2 / 2)`. One integration by parts gives the upper bound
-- `φ(x) / x`, and rearranging the refined identity
-- `P[X ≥ x] ≥ φ(x) / x - P[X ≥ x] / x^2` yields the lower bound
-- `φ(x) / (x + 1 / x)`.
private theorem gaussianReal_standard_tail_bounds {x : ℝ} (hx : 0 < x) :
    gaussianPDFReal 0 1 x / (x + 1 / x) ≤ (gaussianReal 0 1).real (Ici x) ∧
      (gaussianReal 0 1).real (Ici x) ≤ gaussianPDFReal 0 1 x / x := sorry

namespace HasLaw

/-- Lemma 22.2: if `X` has the standard Gaussian law, then for every `x > 0` its upper tail
probability `P[X ≥ x]` is bounded above by the Mills-ratio estimate `φ(x) / x` and below by the
refined bound `φ(x) / (x + 1 / x)`, where `φ = gaussianPDFReal 0 1`. -/
theorem standardNormal_tail_bounds
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) {x : ℝ} (hx : 0 < x) :
    gaussianPDFReal 0 1 x / (x + 1 / x) ≤ P.real (X ⁻¹' Ici x) ∧
      P.real (X ⁻¹' Ici x) ≤ gaussianPDFReal 0 1 x / x := by
  have htail := gaussianReal_standard_tail_bounds hx
  have hIci : P (X ⁻¹' Ici x) = (gaussianReal 0 1) (Ici x) :=
    (hX.identDistrib HasLaw.id).measure_mem_eq measurableSet_Ici
  have hpreimage :
      P.real (X ⁻¹' Ici x) = (gaussianReal 0 1).real (Ici x) := by
    simpa [measureReal_def] using congrArg ENNReal.toReal hIci
  constructor
  · rw [hpreimage]
    exact htail.1
  · rw [hpreimage]
    exact htail.2

end HasLaw

end ProbabilityTheory
