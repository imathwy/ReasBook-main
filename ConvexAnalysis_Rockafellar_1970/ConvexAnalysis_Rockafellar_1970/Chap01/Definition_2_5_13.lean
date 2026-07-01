import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11

-- Declarations for this item will be appended below by the statement pipeline.

open ConvexCone
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.5.13 identifies comparison notation `x ≥ x'` with the condition
  that the difference `x - x'` lies in the nonnegative cone.
- `core/canonical`: the primitive owner is the order-theoretic lemma `sub_nonneg` on additive
  ordered groups.
- `bridge/view`: the nonnegative orthant carrier statement is a thin bridge via
  `ConvexCone.mem_positive`, surfaced with chapter notation `orthant[𝕜](M)`.
- `bridge/view`: no coordinate model is introduced here; concrete coordinatewise readings belong
  downstream from the ordered-module statement.
-- Primitive data vs derived API: additive ordered-group comparison data are primitive; the
  orthant-membership statement below is derived bridge API.
- Domain-style sampling: `orthant[𝕜](M)`, `ConvexCone.mem_positive`, and `sub_nonneg`.
- Layer target: `core/canonical`.
-/

/- Definition 2.5.13: after abstracting the ambient coordinate order, the primitive comparison
owner is `sub_nonneg`, with orthant membership as a bridge view. -/
#check sub_nonneg
#check ConvexCone.positive
#check ConvexCone.mem_positive

section OrderedComparison

variable {E : Type*}

/-- Definition 2.5.13 (primitive form): in an ordered additive group, endpoint comparison is
equivalent to nonnegativity of the difference. -/
@[simp] theorem ge_iff_sub_nonneg
    [AddGroup E] [Preorder E] [AddRightMono E]
    {x x' : E} :
    x ≥ x' ↔ 0 ≤ x - x' := by
  exact (sub_nonneg (a := x) (b := x')).symm

/-- Definition 2.5.13 (set-owner primitive form): endpoint comparison is exactly membership of
the difference in `Set.Ici 0`. -/
@[simp] theorem sub_mem_Ici_zero_iff_ge
    [AddGroup E] [Preorder E] [AddRightMono E]
    {x x' : E} :
    x - x' ∈ Set.Ici (0 : E) ↔ x ≥ x' := by
  rw [Set.mem_Ici]
  exact (ge_iff_sub_nonneg (x := x) (x' := x')).symm

end OrderedComparison

section OrthantComparison

variable {R E : Type*}

/-- Definition 2.5.13: in any ordered additive module, membership of a difference in the
nonnegative orthant is equivalent to endpoint comparison. -/
@[simp] theorem sub_mem_orthant_iff
    [Semiring R] [PartialOrder R]
    [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]
    {x x' : E} :
    x - x' ∈ orthant[R](E) ↔ x ≥ x' := by
  rw [orthant_eq_Ici]
  exact sub_mem_Ici_zero_iff_ge (x := x) (x' := x')

/-- Definition 2.5.13: rewriting comparison as orthant membership for a difference
vector. -/
theorem ge_iff_sub_mem_orthant
    [Semiring R] [PartialOrder R]
    [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]
    {x x' : E} :
    x ≥ x' ↔ x - x' ∈ orthant[R](E) := by
  exact (sub_mem_orthant_iff (x := x) (x' := x')).symm

end OrthantComparison
