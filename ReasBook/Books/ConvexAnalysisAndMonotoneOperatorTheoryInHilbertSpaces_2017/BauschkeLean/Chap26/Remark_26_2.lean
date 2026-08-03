import BauschkeLean.Chap26.Proposition_26_1

open Function
open ERealFunction
open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

/-
Source/core/bridge triage:
- `source-facing`: Remark 26.2 records the unit-step (`γ = 1`) Douglas--Rachford
  fixed-point characterizations of the primal and dual solution sets.
- `core/canonical`: the reusable owners are the Proposition 26.1 fixed-point image theorems for
  general `γ`, together with the Chapter 23 owner `yosidaApproximationMap`.
- `bridge/view`: this file specializes `γ` to `1` and rewrites the unit Yosida map as the
  residual `x ↦ x - resolventMap B hB (1 : PosReal) x`, without introducing a parallel owner.
-/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section DouglasRachford

variable (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)

/-- Remark 26.2 (1): under the Douglas--Rachford hypotheses of Proposition 26.1, the primal
solution set is the `J_B`-image of the fixed-point set of `R_A R_B`, realized here as the
unit-step resolvent map `resolventMap B (1 : PosReal)` applied to the fixed points of
`reflectedResolventComposition A B hA hB (1 : PosReal)`. -/
theorem primal_eq_resolvent_image_fix_reflected_unit :
    primal_inclusion_solution_set A B =
      resolventMap B hB (1 : PosReal) '' fixedPoints
        (reflectedResolventComposition A B hA hB (1 : PosReal)) := by
  simpa using
    primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
      A B hA hB (1 : PosReal)

/-- Remark 26.2 (2): under the same hypotheses, the primal solution set is also the `J_B`-image
of the fixed-point set of the Douglas--Rachford operator `T_{A,B}`, realized here as
the canonical Douglas--Rachford operator built from `J_A` and `J_B`. -/
theorem primal_eq_resolvent_image_fix_douglas_rachford_unit :
    primal_inclusion_solution_set A B =
      resolventMap B hB (1 : PosReal) '' fixedPoints
        (douglasRachfordOperator
          (resolventMap A hA (1 : PosReal)) (resolventMap B hB (1 : PosReal))) := by
  simpa using
    primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_douglasRachford
      A B hA hB (1 : PosReal)

/-- Remark 26.2 (3): under the Douglas--Rachford hypotheses of Proposition 26.1, the dual
solution set is the `(Id - J_B)`-image of the fixed-point set of `R_A R_B`, realized here as the
residual map `fun x ↦ x - resolventMap B (1 : PosReal) x` applied to the fixed points of
`reflectedResolventComposition A B hA hB (1 : PosReal)`. -/
theorem dual_eq_residual_image_fix_reflected_unit :
    dual_inclusion_solution_set A B =
      (fun x : H ↦ x - resolventMap B hB (1 : PosReal) x) '' fixedPoints
        (reflectedResolventComposition A B hA hB (1 : PosReal)) := by
  simpa [yosidaApproximationMap] using
    dual_inclusion_solution_set_eq_image_yosida_fixedPoints_reflectedResolventComposition
      A B hA hB (1 : PosReal)

/-- Remark 26.2 (4): under the same hypotheses, the dual solution set is also the `(Id - J_B)`-
image of the fixed-point set of the Douglas--Rachford operator `T_{A,B}`, realized here as
the canonical Douglas--Rachford operator built from `J_A` and `J_B`. -/
theorem dual_eq_residual_image_fix_douglas_rachford_unit :
    dual_inclusion_solution_set A B =
      (fun x : H ↦ x - resolventMap B hB (1 : PosReal) x) '' fixedPoints
        (douglasRachfordOperator
          (resolventMap A hA (1 : PosReal)) (resolventMap B hB (1 : PosReal))) := by
  simpa [yosidaApproximationMap] using
    dual_inclusion_solution_set_eq_image_yosida_fixedPoints_douglasRachford
      A B hA hB (1 : PosReal)

end DouglasRachford

end SetValuedOperator
