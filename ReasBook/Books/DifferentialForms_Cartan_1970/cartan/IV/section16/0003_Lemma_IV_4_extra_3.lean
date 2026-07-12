import Mathlib.Analysis.Complex.Harmonic.Poisson

open Complex InnerProductSpace Metric Real Set

/--
Lemma IV.4-extra-3. A real-valued function that is harmonic on a disc, continuous on its closure,
and zero on the boundary circle is zero on the whole closed disc.
-/
theorem InnerProductSpace.HarmonicContOnCl.eqOn_zero_closedBall_of_eqOn_zero_sphere
    {f : ℂ → ℝ} {c : ℂ} {R : ℝ} (hf : HarmonicContOnCl f (ball c R))
    (hboundary : EqOn f 0 (sphere c R)) :
    EqOn f 0 (closedBall c R) := by
  by_cases hR : 0 ≤ R
  · intro z hz
    by_cases hzball : z ∈ ball c R
    · have hcircle : Real.circleAverage (poissonKernel c z • f) c R = f z :=
        hf.circleAverage_poissonKernel_smul hzball
      have hzero : Real.circleAverage (poissonKernel c z • f) c R = 0 := by
        have hzeroOnSphere : EqOn (poissonKernel c z • f) (fun _ ↦ 0) (sphere c |R|) := by
          intro w hw
          have hw' : w ∈ sphere c R := by simpa [abs_of_nonneg hR] using hw
          have hfw : f w = 0 := hboundary hw'
          simp [hfw]
        calc
          Real.circleAverage (poissonKernel c z • f) c R =
              Real.circleAverage (fun _ ↦ 0) c R := circleAverage_congr_sphere hzeroOnSphere
          _ = 0 := by simpa using circleAverage_const (0 : ℝ) c R
      rw [hzero] at hcircle
      simpa using hcircle.symm
    · exact hboundary <| by
        rw [mem_sphere]
        exact le_antisymm (by simpa [mem_closedBall] using hz)
          (not_lt.mp <| by simpa [mem_ball] using hzball)
  · simp [closedBall_eq_empty.2 (lt_of_not_ge hR)]
