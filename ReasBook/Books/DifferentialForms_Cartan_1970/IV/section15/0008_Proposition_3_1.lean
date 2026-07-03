import Mathlib.Analysis.Complex.Harmonic.MeanValue

-- Declarations for this item will be appended below by the statement pipeline.

open Complex InnerProductSpace Metric Real Set

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was checked against
-- `Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`, especially the owner theorem
-- `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`.

/-- Proposition 3.1. Any complex-valued harmonic function on a subset `D` of the plane, hence in
particular on an open subset, has the mean value property on every closed disc contained in `D`. -/
theorem harmonicOnNhd_circleAverage_eq {D : Set ℂ} {f : ℂ → ℂ} (hf : HarmonicOnNhd f D) {c : ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hdisc : closedBall c R ⊆ D) : circleAverage f c R = f c := by
  have hclosed : closedBall c |R| ⊆ D := by
    simpa [abs_of_nonneg hR] using hdisc
  have h_circle : CircleIntegrable f c R :=
    (hf.continuousOn.mono (sphere_subset_closedBall.trans hdisc)).circleIntegrable hR
  rw [Complex.ext_iff]
  constructor
  · calc
      (circleAverage f c R).re = circleAverage (Complex.re ∘ f) c R := by
        simpa [Function.comp] using (Complex.reCLM.circleAverage_comp_comm h_circle).symm
      _ = (Complex.re ∘ f) c := by
        simpa [Function.comp] using
          HarmonicOnNhd.circleAverage_eq ((hf.comp_CLM Complex.reCLM).mono hclosed)
      _ = (f c).re := rfl
  · calc
      (circleAverage f c R).im = circleAverage (Complex.im ∘ f) c R := by
        simpa [Function.comp] using (Complex.imCLM.circleAverage_comp_comm h_circle).symm
      _ = (Complex.im ∘ f) c := by
        simpa [Function.comp] using
          HarmonicOnNhd.circleAverage_eq ((hf.comp_CLM Complex.imCLM).mono hclosed)
      _ = (f c).im := rfl
