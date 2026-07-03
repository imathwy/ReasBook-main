

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_16_67 (from Chap16) -/
open scoped InnerProductSpace Pointwise Set

universe u v

namespace SetValuedOperator

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

section

variable {H : Type u} {K : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

/-- Definition 16.67: the coderivative of a set-valued operator `F` at `(x, y)` sends `v` to the
set of all `u` such that `(u, -v)` belongs to the normal cone to `graph F` at `(x, y)`. -/
def coderivative (F : SetValuedOperator H K) (x : H) (y : K) : SetValuedOperator K H :=
  fun v ↦ {u : H | (u, -v) ∈ N[graph F] (x, y)}

scoped prefix:100 "D*" => coderivative

-- Proof sketch: unfold `coderivative`; membership is exactly the defining normal-cone condition on
-- `graph F` at `(x, y)`.
/-- Membership in the coderivative is exactly the normal-cone condition on the graph of `F`. -/
@[simp] theorem mem_coderivative_iff
    (F : SetValuedOperator H K) (x : H) (y : K) (v : K) (u : H) :
    u ∈ (((D* F) x) y v) ↔ (u, -v) ∈ N[graph F] (x, y) :=
  Iff.rfl

end

end

end SetValuedOperator
