import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Definition_15_39

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

section

variable (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
variable [A.IsCentered P] [A.IsNormed P]

/- Lemma 15.45 is `source-facing`: it still bounds the sum of the entrywise characteristic-function
defects in one row. Its `core/canonical` owner in this chapter is `RealRandomVariableArray Ω`, so
the centeredness and norming hypotheses are taken from the owner API rather than repeated as raw
coordinate data. -/
-- Proof sketch: for each summand, rewrite `1 - φₙ,ᵢ(t)` as the expectation of
-- `1 - exp (it Aₙ,ᵢ)`, insert the centered correction term `it Aₙ,ᵢ`, and use the pointwise
-- estimate `|exp (itx) - 1 - itx| ≤ (t^2 / 2) x^2`; summing over `i` and using the row
-- variance normalization together with centeredness gives the bound.
/-- Lemma 15.45: for a centered normed real random-variable array, the sum of the absolute defects
of the row entry characteristic functions at frequency `t` is bounded by `t^2 / 2`. -/
theorem sum_abs_one_sub_charFun_le_half_sq (n : ℕ) (t : ℝ) :
    ∑ i : Fin (A.rowLength n), ‖1 - charFun (P.map (A n i)) t‖ ≤ t ^ 2 / 2 := by
  sorry

end

end RealRandomVariableArray
