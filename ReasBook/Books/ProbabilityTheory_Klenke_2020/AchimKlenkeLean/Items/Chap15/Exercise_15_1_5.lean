import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Exercise_15_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

section

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y Z : Ω → NNReal}

-- Proof sketch: for measurable nonnegative random variables `X`, `Y`, and `Z`, push forward
-- their laws to finite measures on `[0, ∞)`.
-- The assumptions `IndepFun X Z μ` and `IndepFun Y Z μ` identify the laws of `XZ` and `YZ` with
-- the multiplicative convolutions of the laws of `X` and `Y` with the law of `Z`. The Mellin
-- hypothesis is expressed through the canonical owner `mellinTransform`; by
-- `mellinTransform_map` it is the same as a positive finite Mellin moment of `XZ`.
-- The hypothesis `ℙ[Z > 0] > 0` prevents the Mellin transform of `Z` from vanishing identically,
-- so one cancels it and applies
-- `measure_eq_of_mellinTransform_eq_on_Icc_of_exists_lt_top` to the laws of `X` and `Y`
-- (equivalently, uniqueness of Laplace transforms after taking logarithms).
/-- Exercise 15.1.5: if `X`, `Y`, and `Z` are nonnegative measurable random variables, `Z` is
independent of both `X` and `Y`, `XZ =ᵈ YZ`, `Z` is positive with positive probability, and the
law of `XZ` has a finite Mellin transform at some positive exponent, then `X =ᵈ Y`. -/
theorem identDistrib_of_mul_identDistrib_of_indepFun
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXZ_indep : IndepFun X Z μ)
    (hYZ_indep : IndepFun Y Z μ)
    (hZ_pos : 0 < μ (Z ⁻¹' Set.Ioi 0))
    (h_mellin : ∃ s : ℝ, 0 < s ∧
      mellinTransform (μ.map (X * Z)) s < ∞)
    (h_mul : IdentDistrib (X * Z) (Y * Z) μ μ) :
    IdentDistrib X Y μ μ := sorry

end
