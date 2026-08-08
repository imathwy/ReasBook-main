import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDual)
open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 3.17 is `source-facing`. In this finite-dimensional convex extendedRealSubdifferential domain,
the chapter owner abstractions are `is_differentiable_at` for extended-real differentiability and
`extendedRealSubdifferential` for the nonsmooth term. The vector `-∇ f(x)` enters only through the canonical
Riesz functional `-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x)`, viewed in the owner
`extendedRealSubdifferential g x`; the continuous-dual set `strongDualSubdifferential` is therefore only a
derived `bridge/view`, not primitive public data here. This file keeps only that source-facing
predicate and its atomic owner-style specification theorem, with no parallel wrapper around the
upstream owners. -/
recall is_differentiable_at
recall extendedRealSubdifferential

/-- Definition 3.17: the stationarity condition for the composite objective `f + g` says that
`f` is differentiable at `x` in the sense of Definition 3.10 and the continuous-dual vector
represented by the negative gradient `-∇ f(x)` belongs to the owner extendedRealSubdifferential `∂ g(x)`. In
the textbook setting, `f` is proper, `g` is proper convex, and `dom(g) ⊆ interior (dom(f))`. -/
def is_stationary_point (f g : E → EReal) (x : E) : Prop :=
  is_differentiable_at f x ∧
    (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E) ∈ extendedRealSubdifferential g x

/-- Unfolding `is_stationary_point` gives the chapter differentiability condition for `f` at `x`
together with membership of the negative gradient in the owner extendedRealSubdifferential of `g` at `x`. -/
@[simp] theorem is_stationary_point_iff {f g : E → EReal} {x : E} :
    is_stationary_point f g x ↔
      is_differentiable_at f x ∧
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E) ∈ extendedRealSubdifferential g x :=
  Iff.rfl

end
