import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/-
Theorem 3.1.22 lies in the chapter's support-function intersection domain.

Relevant sampled owner declarations:
- `supportFunction` / `supportFunction_apply` in `Definition_3_9`, the source-facing owner for
  `ξ[Q]`
- `supportFunction_dom_eq_univ_of_nonempty_bounded` in `Proposition_3_11`, the earlier bounded
  support-function finiteness theorem in the same owner language
- `supportFunction_eq_on_common_domain_implies_eq` in `Theorem_3_17`, the chapter comparison
  theorem for support functions of closed convex sets
- downstream recall `Theorem_3_27`, which uses this theorem as the owner declaration for the
  intersection formula

Best owner abstraction:
- this theorem itself, stated directly in the chapter owner language `ξ[Q]`; no smaller upstream
  owner theorem for the support function of an intersection as an attained translated-sum infimum
  was found in the sampled project/mathlib domain

Primitive data:
- the sets `Q₁`, `Q₂`
- boundedness and convexity of each set
- nonempty interior of `Q₁ ∩ Q₂`
- the evaluation point `x`

Derived API:
- the attained-infimum statement that `ξ[Q₁ ∩ Q₂] x` is the least value of
  `y ↦ ξ[Q₁] (x + y) + ξ[Q₂] (-y)`
- the direct recall in `Theorem_3_27`

Source/core/bridge triage:
- source-facing: the textbook support-function formula for intersections
- core/canonical: this theorem, expressed directly with the owner `supportFunction`
- bridge/view: the canonical attained-infimum interface `IsLeast` for the translated-sum value set

The textbook states the result on `ℝⁿ`, but the public owner data here are the support functions of
bounded convex sets together with finite-dimensionality and the nonempty-interior intersection
hypothesis. Closedness is proof-route data rather than owner data, because support functions are
closure-invariant and the common-interior hypothesis identifies the closure of `Q₁ ∩ Q₂` with the
intersection of the closures. The theorem therefore lives at the intrinsic finite-dimensional real
inner-product-space layer, with `ℝⁿ` available as a downstream specialization. -/

/-- Theorem 3.1.22: for bounded convex sets `Q₁` and `Q₂` with nonempty interior intersection in a
finite-dimensional real inner-product space, the support function of `Q₁ ∩ Q₂` at `x` is the
minimum over all `y` of
`ξ_{Q₁}(x + y) + ξ_{Q₂}(-y)`, expressed here as the least element of the translated-sum value set.
-/
-- Proof sketch: first show the translated-sum objective
-- `y ↦ supportFunction Q₁ (x + y) + supportFunction Q₂ (-y)` attains its infimum using
-- boundedness, convexity, and the nonempty interior of `Q₁ ∩ Q₂`, after replacing `Q₁` and `Q₂`
-- by their closures. The inequality
-- `supportFunction (Q₁ ∩ Q₂) x ≤ ...` comes from testing against common points of the
-- intersection, and equality follows from the optimality condition for a minimizer together with
-- the subdifferential sum rule and the support-point characterization of the subdifferential of a
-- support function.
theorem supportFunction_inter_isLeast_add_supportFunction
    [FiniteDimensional ℝ E]
    {Q₁ Q₂ : Set E}
    (hQ₁_bounded : Bornology.IsBounded Q₁) (hQ₁_convex : Convex ℝ Q₁)
    (hQ₂_bounded : Bornology.IsBounded Q₂) (hQ₂_convex : Convex ℝ Q₂)
    (hQ_int : (interior (Q₁ ∩ Q₂)).Nonempty) (x : E) :
    IsLeast
      (Set.range fun y : E ↦ ξ[Q₁] (x + y) + ξ[Q₂] (-y))
      (ξ[Q₁ ∩ Q₂] x) := sorry

end
