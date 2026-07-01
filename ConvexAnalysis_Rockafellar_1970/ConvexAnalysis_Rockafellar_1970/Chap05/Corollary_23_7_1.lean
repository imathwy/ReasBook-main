import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_7

noncomputable section

open scoped Pointwise Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.7.1 rewrites Theorem 23.7 by identifying the closure of the
  generated cone of `∂f(x)` with the nonnegative ray through `∂f(x)` when `x ∈ interior (dom f)`.
- `core/canonical`: the owner abstractions already present upstream are
  `_root_.normalCone_sublevel_eq_closure_cone_subdifferentialAt`,
  `Function.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom`, the generated-cone owner
  `cone[ℝ]`, and the Chapter 1/2 ray description of a generated cone
  `PointedCone.cone_eq_nonnegativeRay_of_convex`.
- `bridge/view`: this file stays on the Euclidean bridge owner `Function.subdifferentialAt`; it
  does not introduce a parallel wrapper around the Chapter 23 intrinsic normal-cone theorem.

Domain-style sampling used here:
- `_root_.normalCone_sublevel_eq_closure_cone_subdifferentialAt` from `Chap05.Theorem_23_7`;
- `Function.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom` from
  `Chap05.Theorem_23_4`;
- `Convex.isBounded_iff_recessionCone_eq_singleton_zero` from `Chap02.Theorem_8_4` together with
  `PointedCone.isClosed_cone_of_recessionCone_eq_singleton_zero` from
  `Chap02.Corollary_9_6_1`;
- `PointedCone.cone_eq_nonnegativeRay_of_convex` from `Chap01.Corollary_2_6_3`.

Primitive data vs derived API:
- primitive inputs: a proper convex function `f`, a base point `x`, interior-domain membership,
  and the nonminimality condition at `x`;
- derived API: the normal-cone equality and its pointwise membership reformulation.

Layer target: `bridge/view`.
-/

variable {f : E → WithBotTop ℝ} {x : E}
variable (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
variable (hx : x ∈ interior (dom(f))) (hnotmin : ¬ IsMinOn f Set.univ x)

-- Proof sketch: Theorem 23.7 identifies the normal cone with the closure of the generated cone of
-- `subdifferentialAt f x`. Interior-domain membership gives that subdifferential as a nonempty
-- bounded set by Theorem 23.4, while the supporting-inequality owner makes it convex and closed.
-- Since `x` is not a minimizer, `0 ∉ subdifferentialAt f x`; Theorem 8.4 turns boundedness into
-- the recession-cone identity, and then the Chapter 2 owner theorem
-- `PointedCone.isClosed_cone_of_recessionCone_eq_singleton_zero` yields closedness of
-- `cone[ℝ] (subdifferentialAt f x)`. Corollary 2.6.3 then rewrites that generated cone as the
-- nonnegative ray `Set.Ici (0 : ℝ) • subdifferentialAt f x`.
/-- Corollary 23.7.1: if `f` is a proper convex function, `x ∈ interior (dom(f))`, and `x` does
not attain the minimum value of `f`, then the normal cone of the sublevel set `{z | f z ≤ f x}`
at `x` is exactly the set of all nonnegative scalar multiples of `subdifferentialAt f x`. -/
theorem normalCone_sublevel_eq_nonneg_smul_subdifferentialAt
    :
    N[ℝ](x | {z : E | f z ≤ f x}) = Set.Ici (0 : ℝ) • subdifferentialAt f x := sorry

-- Proof sketch: rewrite by
-- `normalCone_sublevel_eq_nonneg_smul_subdifferentialAt hf_convex hf_proper hx hnotmin`, then
-- use the generic pointwise-set owner theorem `Set.mem_smul_set`; the nonnegativity condition is
-- exactly membership in `Set.Ici (0 : ℝ)`.
/-- Membership reformulation of the normal-cone description from Corollary 23.7.1. -/
theorem mem_normalCone_sublevel_iff_exists_nonneg_mem_smul_subdifferentialAt
    {xStar : E} :
    xStar ∈ N[ℝ](x | {z : E | f z ≤ f x}) ↔
      ∃ a : ℝ, 0 ≤ a ∧ xStar ∈ a • subdifferentialAt f x := sorry

end Function

end
