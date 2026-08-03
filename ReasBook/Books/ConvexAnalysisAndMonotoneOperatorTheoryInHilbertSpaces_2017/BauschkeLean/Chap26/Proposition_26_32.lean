import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap26.Problem_26_30

-- Semantic recall note: `lean_leansearch` surfaced only generic adjoint/resolvent infrastructure
-- for this item, so the owner/API choices below were verified locally against
-- `Chap26/Problem_26_30.lean` for `M`, `Chap23/Example_23_5.lean` for `S`, and
-- `Chap23/Definition_23_1.lean` for the canonical set-valued resolvent surface `J[...]`.

open scoped InnerProductSpace Pointwise SetValuedOperator
open ContinuousLinearMap
open ERealFunction
open SetValuedOperator

universe u v

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/- Source/core/bridge triage:
- `source-facing`: Proposition 26.32 records the maximal-monotonicity and resolvent facts for the
  composite Kuhn--Tucker operator from Problems 26.28 and 26.30.
- `core/canonical`: the owner abstractions are `composite_kuhn_tucker_operator`,
  `skewCouplingMap`, `Maximal IsMonotone`, and the Chapter 23 resolvent surface `J[...]`.
- `bridge/view`: this file should state properties of those existing owners directly, rather than
  introducing new product-space wrapper operators or duplicate linear-map owners. -/

namespace SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Proposition 26.32 (1): in the setting of Problems 26.28 and 26.30, if `A` and `B` are
maximally monotone, then the Kuhn--Tucker product-space operator
`composite_kuhn_tucker_operator z A r B` is maximally monotone. -/
theorem composite_kuhn_tucker_operator_maximal
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Maximal IsMonotone (composite_kuhn_tucker_operator z A r B) := sorry

end SetValuedOperator

namespace ContinuousLinearMap

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Proposition 26.32 (2): for the skew coupling operator
`skewCouplingMap L : H × K →L[ℝ] H × K`, the source identity `S^* = -S` holds. The source's
boundedness assertion is realized by the owner type `H × K →L[ℝ] H × K`. -/
theorem skewCouplingMap_adjoint_eq_neg
    (L : H →L[ℝ] K) :
    (skewCouplingMap L).adjoint = -(skewCouplingMap L) := sorry

/-- Proposition 26.32 (3): for the skew coupling operator from Problems 26.28 and 26.30, the
operator norm satisfies `‖skewCouplingMap L‖ = ‖L‖`. -/
theorem norm_skewCouplingMap
    (L : H →L[ℝ] K) :
    ‖skewCouplingMap L‖ = ‖L‖ := sorry

end ContinuousLinearMap

namespace SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Proposition 26.32 (4): in the setting of Problems 26.28 and 26.30, if `A` and `B` are
maximally monotone, then the Kuhn--Tucker operator sum
`composite_kuhn_tucker_operator z A r B + (skewCouplingMap L).toSetValuedOperator`
is maximally monotone. -/
theorem composite_kuhn_tucker_operator_add_skewCouplingMap_maximal
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) :
    Maximal IsMonotone
      (composite_kuhn_tucker_operator z A r B +
        (skewCouplingMap L).toSetValuedOperator) := sorry

/-- Proposition 26.32 (5): in the setting of Problems 26.28 and 26.30, for `γ ∈ ℝ_{++}` and
`(x, v) ∈ H × K`, the resolvent of
`M = composite_kuhn_tucker_operator z A r B` is given by the source formula
`J_{γM}(x, v) = (J_{γA}(x + γ z), v - γ (r + J_{γ⁻¹ B}(γ⁻¹ v - r)))`, realized on the canonical
set-valued surface `J[...]`. -/
theorem resolvent_composite_kuhn_tucker_operator_eq
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (γ : PosReal) (x : H) (v : K) :
    J[((γ : ℝ) • composite_kuhn_tucker_operator z A r B)] (x, v) =
      J[((γ : ℝ) • A)] (x + (γ : ℝ) • z) ×ˢ
        (({v} : Set K) -
          (γ : ℝ) •
            (({r} : Set K) +
              J[(((γ : ℝ)⁻¹) • B)] (((γ : ℝ)⁻¹) • v - r))) := sorry

end SetValuedOperator
