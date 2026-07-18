import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap04.Theorem_4_23

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoxIntegral

/-- The Dirichlet function on `ℝ`, viewed as the indicator of the rational numbers. -/
noncomputable def klenkeDirichletFunction : ℝ → ℝ :=
  (Set.range ((↑) : ℚ → ℝ)).indicator 1

private theorem klenkeDirichletFunction_ae_eq_zero_on_unitInterval :
    klenkeDirichletFunction =ᵐ[volume.restrict (Set.Icc 0 1)] 0 := by
  have h_countable : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have h_zero :
      (volume.restrict (Set.Icc 0 1)) (Set.range ((↑) : ℚ → ℝ)) = 0 :=
    h_countable.measure_zero _
  simpa [klenkeDirichletFunction] using
    (indicator_meas_zero h_zero :
      klenkeDirichletFunction =ᵐ[volume.restrict (Set.Icc 0 1)] 0)

-- Proof sketch: use that `Set.range ((↑) : ℚ → ℝ)` is countable, hence null for `volume`, so the
-- indicator is integrable on `Set.Icc 0 1` and its set integral vanishes.
/-- Example 4.24: The Dirichlet function on `[0,1]`, equal to `1` on rational points and `0`
elsewhere, is Lebesgue integrable on `[0,1]` and has integral `0`. -/
theorem klenkeDirichletFunction_integrableOn_unitInterval_and_integral_zero :
    IntegrableOn klenkeDirichletFunction (Set.Icc 0 1) volume ∧
      ∫ x in Set.Icc 0 1, klenkeDirichletFunction x ∂volume = 0 := by
  refine ⟨?_, ?_⟩
  · exact integrableOn_zero.congr_fun_ae klenkeDirichletFunction_ae_eq_zero_on_unitInterval.symm
  · calc
      ∫ x in Set.Icc 0 1, klenkeDirichletFunction x ∂volume =
          ∫ x in Set.Icc 0 1, (0 : ℝ) ∂volume :=
        integral_congr_ae klenkeDirichletFunction_ae_eq_zero_on_unitInterval
      _ = 0 := by simp

-- Proof sketch: show that every tagged Riemann partition of the unit box has upper sums `1` and
-- lower sums `0`, using density of rational and irrational points in every subinterval.
/-- The Dirichlet function on `[0,1]` is not Riemann integrable. -/
theorem klenkeDirichletFunction_not_riemannIntegrableOn_unitInterval :
    ¬ RiemannIntegrableOnUnitInterval klenkeDirichletFunction := sorry
