import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap23.Example_23_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator
open SetValuedOperator

universe u v

noncomputable section

namespace SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedAddCommGroup K]

/- Source/core/bridge triage:
- `source-facing`: Problem 26.30 introduces the product-space Kuhn--Tucker operator and its zero
  set.
- `core/canonical`: the reusable owners are `Function.toSetValuedOperator`,
  `SetValuedOperator.inverse`, `SetValuedOperator.zeros`, operator sum, and
  `ContinuousLinearMap.skewCouplingMap`.
- `bridge/view`: the explicit coordinate formulas are the companion `*_def`, `*_apply`, and
  `mem_*_iff` lemmas below. -/

/-- Problem 26.30 (1): in the setting of Problem 26.28, the product-space operator `M` sends
`(x, v)` to `(-z + A x) × (r + B⁻¹ v)`, expressed through the canonical singleton-valued constant
operators and the Chapter 1 inverse owner. -/
def composite_kuhn_tucker_operator
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K) :
    SetValuedOperator (H × K) (H × K) :=
  fun xv ↦ ((((fun _ : H ↦ -z).toSetValuedOperator) + A) xv.1) ×ˢ
    ((((fun _ : K ↦ r).toSetValuedOperator) + B⁻¹) xv.2)

/-- `composite_kuhn_tucker_operator` is the product-space operator with the
explicit translated-factor formula `(-z + A x) × (r + B⁻¹ v)`. -/
theorem composite_kuhn_tucker_operator_def
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K) :
    composite_kuhn_tucker_operator z A r B =
      fun xv ↦ (({-z} : Set H) + A xv.1) ×ˢ (({r} : Set K) + (B⁻¹ xv.2)) := by
  funext xv
  simp [composite_kuhn_tucker_operator]

/-- Applying `composite_kuhn_tucker_operator` at `(x, v)` gives the Cartesian product
`(-z + A x) × (r + B⁻¹ v)`. -/
@[simp] theorem composite_kuhn_tucker_operator_apply
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K) (x : H) (v : K) :
    composite_kuhn_tucker_operator z A r B (x, v) =
      (({-z} : Set H) + A x) ×ˢ (({r} : Set K) + (B⁻¹ v)) := by
  simp [composite_kuhn_tucker_operator]

/-- A pair `(y, w)` belongs to `composite_kuhn_tucker_operator z A r B (x, v)` exactly when
its components belong to the translated factors `-z + A x` and `r + B⁻¹ v`. -/
@[simp] theorem mem_composite_kuhn_tucker_operator_iff
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (x : H) (v : K) (y : H) (w : K) :
    (y, w) ∈ composite_kuhn_tucker_operator z A r B (x, v) ↔
      y ∈ ({-z} : Set H) + A x ∧ w ∈ ({r} : Set K) + (B⁻¹ v) := by
  simp [composite_kuhn_tucker_operator]

variable [InnerProductSpace ℝ H] [CompleteSpace H]
variable [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Problem 26.30 (2): the Kuhn--Tucker points associated with Problem 26.28 form the zero set
of the sum of the product-space operator `M` above and the source's skew term
`S(x, v) = (L^* v, -L x)`, realized canonically as `ContinuousLinearMap.skewCouplingMap L`. -/
def composite_kuhn_tucker_points
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) : Set (H × K) :=
  (composite_kuhn_tucker_operator z A r B +
      (ContinuousLinearMap.skewCouplingMap L).toSetValuedOperator).zeros

/-- Problem 26.30 (3): membership in `composite_kuhn_tucker_points` is exactly the coupled
inclusion system `z - L^* v ∈ A x` and `L x - r ∈ B⁻¹ v`. -/
theorem mem_composite_kuhn_tucker_points_iff
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (x : H) (v : K) :
    (x, v) ∈ composite_kuhn_tucker_points z A r B L ↔
      z - L.adjoint v ∈ A x ∧ L x - r ∈ B⁻¹ v := by
  simp [composite_kuhn_tucker_points, composite_kuhn_tucker_operator, sub_eq_add_neg, add_comm]

end SetValuedOperator
