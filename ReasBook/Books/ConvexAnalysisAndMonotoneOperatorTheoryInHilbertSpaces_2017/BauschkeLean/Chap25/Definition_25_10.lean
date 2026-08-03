import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Definition 25.10 introduces Chapter 25's `3*`-monotonicity predicate on a
  set-valued operator.
- `core/canonical`: the Fitzpatrick function owner is the Chapter 20 definition `F[A]`.
- `bridge/view`: the companion theorems below expose the source predicate directly as the
  Fitzpatrick-domain inclusion used by downstream Chapter 25 statements. -/

/-- Definition 25.10: for a monotone set-valued operator `A`, `3*` monotonicity means
`dom A × range A` is contained in the effective domain of the Fitzpatrick function `F[A]`. -/
def IsThreeStarMonotone (A : SetValuedOperator H H) : Prop :=
  A.dom ×ˢ A.range ⊆ ERealFunction.dom (F[A])

/-- A `3*`-monotone operator satisfies the Fitzpatrick-domain inclusion
`dom A × range A ⊆ dom (F[A])`. -/
theorem IsThreeStarMonotone.subset_dom_fitzpatrickFunction
    {A : SetValuedOperator H H} (hA : A.IsThreeStarMonotone) :
    A.dom ×ˢ A.range ⊆ ERealFunction.dom (F[A]) :=
  hA

/-- Unfolding `IsThreeStarMonotone` gives the Fitzpatrick-domain characterization
`dom A × range A ⊆ dom (F[A])`. -/
theorem isThreeStarMonotone_iff (A : SetValuedOperator H H) :
    A.IsThreeStarMonotone ↔ A.dom ×ˢ A.range ⊆ ERealFunction.dom (F[A]) :=
  Iff.rfl

end SetValuedOperator
