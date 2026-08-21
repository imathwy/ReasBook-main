import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap014.Definition_14_8_extra_2

/-
Domain sampling:
* primary domain: semismoothness of locally Lipschitz maps `F : ℝ^n → ℝ^n`
* inspected project owner: `Definition_14_8_extra_2`
* source/core/bridge triage:
  - source-facing: `LocallyLipschitzAt`, `generalizedJacobian`,
    `hasSemismoothLinearizationLimit`, `semismoothDifferenceQuotient`, `SemismoothAt`
  - bridge/view: `hasSemismoothLinearizationLimit_iff`, `semismoothAt_iff`
  - derived property: `SemismoothAt.existsCommonLimit`
* this exercise introduces no new owner
-/

/- Chapter14 Exercise 14.2 is already owned by the Chapter 14 semismoothness API in
`Definition_14_8_extra_2.lean`. This file therefore stays at the recall layer and reuses those
canonical source-facing declarations directly instead of restating their types through anonymous
function binders. -/

#check LocallyLipschitzAt
#check generalizedJacobian
#check hasSemismoothLinearizationLimit
#check hasSemismoothLinearizationLimit_iff
#check semismoothDifferenceQuotient
#check semismoothDifferenceQuotient_apply
#check SemismoothAt
#check semismoothAt_iff
#check SemismoothAt.existsCommonLimit
