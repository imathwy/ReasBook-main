import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.11 rewrites the standard-simplex problem from
  Definition 6.28.10 into the scalar coordinate families `f_{0k}` and `f_{1k}`.
- `core/canonical`: the project already owns extension by `+∞` outside a set as
  `Function.toWithBotTopOn`.
- `bridge/view`: the branch formula for `f_{0k}` is exactly the canonical extension of `q k`
  from the nonnegative half-line `Set.Ici 0`, so this file should use that owner directly rather
  than keep a parallel alias. The source-facing family `f_{1k}` is the identity on every
  coordinate except one distinguished index, where the affine shift by `1` appears.

Domain-style sampling used here:
- `Function.toWithBotTopOn` from `Chap01.Remark_4_4_5`;
- `Function.toWithBotTopOn_of_mem`;
- `Function.toWithBotTopOn_of_notMem`;
- `IsStdSimplexSeparableMinimizer.iff_sum` from `Definition_6_28_10`, which already keeps the
  simplex problem itself on the canonical owners `stdSimplex` and `separableCoordinateSum`;
- `Function.separableCoordinateSum` from `Chap03.Text_16_0_4`, which already treats a
  separable optimization problem through a family of scalar coordinate branches.

Primitive data vs derived API:
- primitive source data: an index family `q : ι → α → β`;
- core owner for `f_{0k}`: use the family `fun k ↦ Function.toWithBotTopOn (q k) (Set.Ici 0)`
  directly, with branch formulas inherited from
  `Function.toWithBotTopOn_of_mem` and `Function.toWithBotTopOn_of_notMem`;
- source-facing specialization kept in this file:
  `Function.standardSimplexCoordinateConstraint`;
- derived API local to this file: branch formulas for the distinguished-index family `f_{1k}`.

Layer target:
- the `f_{0k}` clause is `core/canonical` recall of `Function.toWithBotTopOn`;
- the `f_{1k}` clause is `source-facing`, with the branch owner implemented directly via the
  canonical `Set.piecewise` interface.
-/

namespace Function

section Objective

variable {ι : Type*}
variable [Preorder α] [Zero α]

variable (q : ι → α → β)

/- Definition 6.28.11 (`f_{0k}`): the simplex objective branches are the coordinatewise canonical
extension owner `Function.toWithBotTopOn (q k) (Set.Ici 0)`. Use
`Function.toWithBotTopOn_of_mem` and `Function.toWithBotTopOn_of_notMem` for the source branch
formulas on nonnegative and negative inputs. -/
@[simp] theorem toWithBotTopOn_Ici_zero_of_nonneg
    (k : ι) {ξ : α} (hξ : 0 ≤ ξ) :
    Function.toWithBotTopOn (q k) (Set.Ici (0 : α)) ξ = q k ξ := by
  simpa using Function.toWithBotTopOn_of_mem (q k) (Set.Ici (0 : α)) hξ

@[simp] theorem toWithBotTopOn_Ici_zero_of_not_nonneg
    (k : ι) {ξ : α} (hξ : ¬ 0 ≤ ξ) :
    Function.toWithBotTopOn (q k) (Set.Ici (0 : α)) ξ = (⊤ : WithTopBot β) := by
  simpa using Function.toWithBotTopOn_of_notMem (q k) (Set.Ici (0 : α)) hξ

@[simp] theorem toWithBotTopOn_Ici_zero_of_lt_zero
    (k : ι) {ξ : α} (hξ : ξ < 0) :
    Function.toWithBotTopOn (q k) (Set.Ici (0 : α)) ξ = (⊤ : WithTopBot β) := by
  exact toWithBotTopOn_Ici_zero_of_not_nonneg (q := q) (k := k) (ξ := ξ) (not_le_of_gt hξ)

end Objective

section Constraint

variable {ι : Type*}
variable [One α] [Sub α]

/-- The family `f_{1k}` encoding one affine simplex constraint branch:
every coordinate branch is the identity except at a distinguished index `k0`, where `1` is
subtracted. The textbook "last-coordinate" form is recovered by specializing to `ι = Fin n` and
choosing the distinguished terminal coordinate. -/
def standardSimplexCoordinateConstraint (k0 : ι) : ι → α → α :=
  ({k0} : Set ι).piecewise
    (fun _ ξ ↦ ξ - 1)
    (fun _ ↦ id)

/-- Branch formula for `f_{1k}`: `k0` uses `ξ - 1`, all other coordinates use `ξ`. -/
@[simp] theorem standardSimplexCoordinateConstraint_apply
    (k0 k : ι) (ξ : α) :
    standardSimplexCoordinateConstraint k0 k ξ = if k = k0 then ξ - 1 else ξ := by
  by_cases hk : k = k0 <;> simp [standardSimplexCoordinateConstraint, hk]

/-- Away from `k0`, `standardSimplexCoordinateConstraint k0` is the identity map. -/
@[simp] theorem standardSimplexCoordinateConstraint_of_ne
    (k0 k : ι) (ξ : α) (hk : k ≠ k0) :
    standardSimplexCoordinateConstraint k0 k ξ = ξ := by
  simp [standardSimplexCoordinateConstraint, hk]

/-- At `k0`, `standardSimplexCoordinateConstraint k0` is `ξ - 1`. -/
@[simp] theorem standardSimplexCoordinateConstraint_of_eq
    (k0 k : ι) (ξ : α) (hk : k = k0) :
    standardSimplexCoordinateConstraint k0 k ξ = ξ - 1 := by
  simp [standardSimplexCoordinateConstraint, hk]

end Constraint

end Function

end
