import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap04.Definition_4_10
import BauschkeLean.Chap22.Definition_22_1
import BauschkeLean.Chap22.Example_22_7
import BauschkeLean.Chap22.Proposition_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SetValuedOperator

universe u

namespace SetValuedOperator

-- Domain sampling: the core owner is `SetValuedOperator.IsParamonotone`; strict monotonicity is
-- already an owner-level property, so the canonical step is `IsStrictlyMonotone.isParamonotone`.
-- This file only records the `ofFunction`/`CocoerciveOn` bridge consequences.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Example 22.8 (1): if the singleton-valued operator attached to `A : D → H` is strictly
monotone, then it is paramonotone. The source's nonempty-domain hypothesis is redundant for this
owner-level implication, so it disappears from the refined statement. -/
theorem ofFunction_isParamonotone_of_isStrictlyMonotone
    {D : Set H} {A : D → H}
    (hA : (ofFunction D A).IsStrictlyMonotone) :
    (ofFunction D A).IsParamonotone :=
  hA.isParamonotone

/-- Example 22.8 (2): if the inverse of the singleton-valued operator attached to `A : D → H` is
strictly monotone, then the operator itself is paramonotone. The source's nonempty-domain and
completeness hypotheses are redundant for this bridge. -/
theorem ofFunction_isParamonotone_of_inverse_isStrictlyMonotone
    {D : Set H} {A : D → H}
    (hA : ((ofFunction D A)⁻¹).IsStrictlyMonotone) :
    (ofFunction D A).IsParamonotone := by
  simpa [SetValuedOperator.inverse] using
    (hA.isParamonotone.inverse : ((ofFunction D A)⁻¹)⁻¹.IsParamonotone)

/-- Example 22.8 (3): if `A : D → H` is cocoercive, then the associated singleton-valued operator
is paramonotone. The Chapter 22 bridge runs through the canonical owner chain
`CocoerciveOn → inverse strongly monotone → inverse strictly monotone → inverse paramonotone`. -/
theorem ofFunction_isParamonotone_of_cocoerciveOn
    {β : ℝ} {D : Set H} {A : D → H}
    (hA : CocoerciveOn β D A) :
    (ofFunction D A).IsParamonotone := by
  exact ofFunction_isParamonotone_of_inverse_isStrictlyMonotone
    (CocoerciveOn.inverseOfFunction_isStronglyMonotone hA).isStrictlyMonotone

end SetValuedOperator
