import BauschkeLean.Chap16.Remark_16_28
import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap20.Theorem_20_25

open scoped EuclideanSpace InnerProductSpace SetValuedOperator

namespace SetValuedOperator

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
open ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Remark 21.15 records existence of maximally monotone operators with
  nonconvex domain and nonconvex range.
- `core/canonical`: the owner abstraction is `Maximal IsMonotone A`.
- `bridge/view`: Remark 16.28 supplies the source-facing nonconvex-domain witness, and the
  range statement is its inverse-domain reformulation via `range_inverse` and `Maximal.inverse`.

Primitive data: the Chapter 16 counterexample function `oneSubSqrtAbsMaxCounterexample`.
Derived API: maximality of its subdifferential and the inverse bridge from domain to range. -/

/-- Remark 21.15 (1): there exists a maximally monotone operator whose domain is not convex. A
witness is supplied by Remark 16.28. -/
theorem exists_maximallyMonotone_dom_not_convex :
    ∃ A : SetValuedOperator ℝ² ℝ², Maximal IsMonotone A ∧ ¬ Convex ℝ A.dom := by
  refine ⟨∂ oneSubSqrtAbsMaxCounterexample, ?_, ?_⟩
  · exact
      subdifferential_isMaximallyMonotone_of_mem_gammaZero
        oneSubSqrtAbsMaxCounterexample_mem_gammaZero
  · simpa using subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_not_convex

/-- Remark 21.15 (2): there exists a maximally monotone operator whose range is not convex. A
witness is obtained by applying the inverse bridge to the same Remark 16.28 counterexample. -/
theorem exists_maximallyMonotone_range_not_convex :
    ∃ A : SetValuedOperator ℝ² ℝ², Maximal IsMonotone A ∧ ¬ Convex ℝ A.range := by
  refine ⟨(∂ oneSubSqrtAbsMaxCounterexample)⁻¹, ?_, ?_⟩
  · exact
      Maximal.inverse <|
        subdifferential_isMaximallyMonotone_of_mem_gammaZero
          oneSubSqrtAbsMaxCounterexample_mem_gammaZero
  · have hrange :
        ((∂ oneSubSqrtAbsMaxCounterexample)⁻¹).range =
          (∂ oneSubSqrtAbsMaxCounterexample).dom := by
      simp
    rw [hrange]
    simpa using subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_not_convex

end SetValuedOperator
