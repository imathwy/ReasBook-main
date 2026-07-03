import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_15_38 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: apply Chebyshev's inequality to each law `ProbabilityMeasure.map ⟨P, inferInstance⟩
-- (hX_aemeasurable n)` at level `K`, use `hX_mean` and `hX_var` to rewrite the second-moment
-- bound as `1 / K^2`, and conclude with the canonical norm-tail tightness criterion
-- `isTightMeasureSet_of_tendsto_measure_norm_gt` on `ℝ`.
/-- Remark 15.38: a sequence of centered real random variables with variance `1` has a tight
family of laws. -/
theorem laws_of_centered_unit_variance_sequence_are_tight
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_aemeasurable : ∀ n, AEMeasurable (X n) P)
    (hX_mean : ∀ n, P[X n] = 0)
    (hX_var : ∀ n, Var[X n; P] = 1) :
    IsTightMeasureSet
      (Set.range fun n : ℕ ↦
        ((ProbabilityMeasure.map ⟨P, inferInstance⟩ (hX_aemeasurable n) : ProbabilityMeasure ℝ) :
          Measure ℝ)) := sorry
