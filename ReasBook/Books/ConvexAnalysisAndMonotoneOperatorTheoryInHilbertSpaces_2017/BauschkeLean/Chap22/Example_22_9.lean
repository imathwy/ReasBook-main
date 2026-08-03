import BauschkeLean.Chap04.Proposition_4_11
import BauschkeLean.Chap22.Example_22_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Semantic recall: `lean_leansearch` only surfaced unrelated closure-operator results, so this
-- item follows the local Chapter 4/22 owners `CocoerciveOn` and `SetValuedOperator.IsParamonotone`.

/-- Example 22.9 (1): if `T : D → H` is nonexpansive and `α ∈ [-1, 1]`, then
`x ↦ x + α • T x` is `1 / 2`-cocoercive on `D`. The source's nonempty-domain hypothesis is
redundant for this canonical residual-map specialization, so it is omitted. -/
theorem cocoerciveOn_half_id_add_smul_of_nonexpansive
    {D : Set H} {T : D → H} (hT : LipschitzWith 1 T) {α : ℝ}
    (hα : α ∈ Set.Icc (-1 : ℝ) 1) :
    CocoerciveOn (1 / 2 : ℝ) D (fun x : D ↦ x + α • T x) := by
  have hα_abs : |α| ≤ 1 := by
    simpa [abs_le] using hα
  have hα_nnnorm : ‖-α‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast (show ‖-α‖ ≤ 1 by simpa using hα_abs)
  have hScaled : LipschitzWith 1 (fun x : D ↦ (-α) • T x) := by
    refine ((lipschitzWith_smul (-α)).comp hT).weaken ?_
    simpa using hα_nnnorm
  have hResidualMap :
      residualMap D (fun x : D ↦ (-α) • T x) = fun x : D ↦ x + α • T x := by
    funext x
    simp [residualMap]
  rw [← hResidualMap]
  exact (lipschitzWith_one_iff_residualMap_cocoerciveOn_half _).mp hScaled

namespace SetValuedOperator

/-- Example 22.9 (2): if `T : D → H` is nonexpansive and `α ∈ [-1, 1]`, then the
singleton-valued operator associated with `x ↦ x + α • T x` is paramonotone. The source's
nonempty-domain hypothesis is redundant for this Chapter 22 bridge, so it is omitted. -/
theorem ofFunction_id_add_smul_isParamonotone_of_nonexpansive
    {D : Set H} {T : D → H} (hT : LipschitzWith 1 T) {α : ℝ}
    (hα : α ∈ Set.Icc (-1 : ℝ) 1) :
    (ofFunction D (fun x : D ↦ x + α • T x)).IsParamonotone := by
  exact ofFunction_isParamonotone_of_cocoerciveOn
    (cocoerciveOn_half_id_add_smul_of_nonexpansive hT hα)

end SetValuedOperator
