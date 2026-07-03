import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_16_69 (from Chap16) -/
open scoped Pointwise
open WithLp

universe u

namespace ERealFunction

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2 prod_normedSpace_l2
  prod_innerProductSpace_l2

section EpigraphicalOperator

variable {H : Type u}

/-- The epigraphical set-valued operator associated with an `]-∞,+∞]`-valued function, sending
`x` to the real heights lying above `f x`. -/
def epigraphicalOperator (f : H → Set.Ioi (⊥ : EReal)) : SetValuedOperator H ℝ :=
  fun x ↦ {y : ℝ | (f x : EReal) ≤ (y : EReal)}

end EpigraphicalOperator

section CoderivativeOfEpigraphicalOperator

open Set
open SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: identify the graph of `epigraphicalOperator f` with the real-height epigraph of
-- `f`, rewrite the left-hand side through the canonical coderivative owner `D*`, and then split on
-- the sign of `v`. The case `v > 0` reduces to the epigraph-normal characterization of the
-- subdifferential from Proposition 16.16, the case `v = 0` is the horizontal slice giving the
-- normal cone to `effectiveDomain f`, and convexity of the epigraph rules out any normal vector
-- with negative scalar component.
/-- Proposition 16.69: if `f` is convex on its effective domain and `x ∈ dom f`, then the
coderivative of the epigraphical operator `x ↦ {y ∈ ℝ | f x ≤ y}` at the graph point
`(x, (f x).toReal)` is `v • ∂ f x` for `v > 0`, the normal cone to `dom f` at `x` for `v = 0`,
and `∅` for `v < 0`. -/
theorem coderivative_epigraphicalOperator_eq_piecewise
    (f : H → Set.Ioi (⊥ : EReal)) (hconvex : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    ((D* (epigraphicalOperator f)) x ((f x : EReal).toReal)) =
      fun v : ℝ ↦
        if 0 < v then
          v • (∂ f) x
        else if v = 0 then
          N[effectiveDomain f] x
        else
          ∅ := sorry

end CoderivativeOfEpigraphicalOperator

end ERealFunction
