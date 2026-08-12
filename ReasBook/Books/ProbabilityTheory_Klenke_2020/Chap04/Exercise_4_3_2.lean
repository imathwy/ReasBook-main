import ProbabilityTheory_Klenke_2020.Chap04.Theorem_4_23

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

local notation "unitIntervalSet" => Set.Icc (0 : ℝ) 1
local notation "unitIntervalVolume" => volume.restrict unitIntervalSet

-- Proof sketch: apply `integrableOn_Icc_and_integral_eq_of_riemannIntegrable` with `a = 0`,
-- `b = 1` to obtain `IntegrableOn f unitIntervalSet volume`, then use `Integrable.aemeasurable`
-- for the restricted measure.
/-- Exercise 4.3.2: if `f` is Riemann integrable on `[0,1]`, then `f` is Lebesgue measurable on
`[0,1]`. -/
theorem aemeasurable_restrict_unitInterval_of_riemannIntegrable
    {f : ℝ → ℝ}
    (hf : RiemannIntegrableOnUnitInterval f) :
    AEMeasurable f unitIntervalVolume := by
  rcases integrableOn_Icc_and_integral_eq_of_riemannIntegrable zero_lt_one hf with ⟨hf_int, _⟩
  exact hf_int.integrable.aemeasurable

-- Proof sketch: choose a non-Borel subset of a closed null subset of `[0,1]`, take its indicator
-- function, note that it vanishes almost everywhere on `[0,1]` and hence is Riemann integrable,
-- but its restriction to `[0,1]` cannot be Borel measurable because the level set `{1}` recovers
-- the chosen non-Borel subset.
/-- There exists a function on `[0,1]` that is Riemann integrable but whose restriction to the
interval subtype is not Borel measurable. -/
theorem exists_riemannIntegrable_unitInterval_not_borelMeasurable :
    ∃ f : ℝ → ℝ,
      RiemannIntegrableOnUnitInterval f ∧
      ¬ Measurable (f ∘ Subtype.val : unitIntervalSet → ℝ) := sorry
