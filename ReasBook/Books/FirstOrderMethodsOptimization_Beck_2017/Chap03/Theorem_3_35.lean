import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-
Theorem 3.35 is `source-facing` for composite first-order optimality. Its primitive convex-analysis
notions are already owned upstream by `effective_domain` and `is_convex_function`, while the
source-facing stationarity condition itself is already owned in Definition 3.17 by
`is_stationary_point`. The continuous-dual set `strongDualSubdifferential` is only the
`bridge/view` used inside that owner predicate, so this file states its conclusions in terms of
`is_stationary_point` instead of duplicating the defining condition. For this item, the primitive
source data is the convexity of `g`, the feasibility point `xStar ∈ effective_domain g`, the
chapter differentiability owner `is_differentiable_at f xStar`, and the corresponding local or
global minimality hypothesis for `f + g` on `effective_domain g`. The interior finite-domain data
for `f` is already bundled into `is_differentiable_at`, and any ambient codomain/properness side
conditions needed by proof-level bridge lemmas are treated as derived internal input rather than
primitive public parameters here.
-/
recall effective_domain
recall is_convex_function
recall is_stationary_point

section CompositeContext

variable {f g : E → EReal} {xStar : E}

-- Proof sketch: use local minimality of the composite objective on `effective_domain g` along the
-- segment from `xStar` to an arbitrary `y ∈ effective_domain g`. Convexity of `g` turns the local
-- minimality inequality into a one-sided directional inequality for `f` at `xStar`, and
-- differentiability identifies that directional derivative with evaluation against the gradient.
/-- Theorem 3.35 (1): (a) if `g` is convex, `xStar ∈ dom(g)` is a local minimizer of `f + g`, and
`f` is differentiable at `xStar` in the chapter sense, then `xStar` is stationary for the
composite problem. Unfolding `is_stationary_point f g xStar` recovers the textbook condition
`-∇ f(xStar) ∈ ∂ g(xStar)`. -/
theorem is_stationary_point_of_isLocalMinOn
    (hgconvex : is_convex_function g)
    (hxStar : xStar ∈ effective_domain g)
    (hdiff : is_differentiable_at f xStar)
    (hlocal : IsLocalMinOn (fun x ↦ f x + g x) (effective_domain g) xStar) :
    is_stationary_point f g xStar := sorry

-- Proof sketch: for the forward implication, apply part (1) to a global minimizer. For the
-- converse implication, combine the subgradient inequality for `g` with the first-order convexity
-- inequality for differentiable convex `f`, then add the two inequalities to obtain global
-- minimality of `f + g` on `effective_domain g`.
/-- Theorem 3.35 (2): (b) if `f` is also convex, then for a differentiable feasible point
`xStar ∈ dom(g)`, stationarity for the composite problem is equivalent to `xStar` being a global
minimizer of the composite problem on `dom(g)`. Unfolding `is_stationary_point f g xStar`
recovers the textbook condition `-∇ f(xStar) ∈ ∂ g(xStar)`. -/
theorem isMinOn_iff_is_stationary_point
    (hgconvex : is_convex_function g)
    (hxStar : xStar ∈ effective_domain g)
    (hdiff : is_differentiable_at f xStar)
    (hfconvex : is_convex_function f) :
    IsMinOn (fun x ↦ f x + g x) (effective_domain g) xStar ↔
      is_stationary_point f g xStar := sorry

end CompositeContext

end
