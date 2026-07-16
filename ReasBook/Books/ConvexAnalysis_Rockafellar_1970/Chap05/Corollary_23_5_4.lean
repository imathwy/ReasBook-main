import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PolarCone RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

variable {K : Set E} {x xStar : E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.5.4 compares the subdifferential of the indicator of a nonempty
  closed convex cone `K` with the subdifferential of the indicator of its polar cone `Kᵒ`, and
  identifies both with the complementary-slackness conditions `x ∈ K`, `xStar ∈ Kᵒ`,
  `⟪x, xStar⟫ = 0`.
- `core/canonical`: the relevant project owners are the Chapter 23 Euclidean subdifferential
  `Function.subdifferentialAt`, the Chapter 1 indicator notation `δ[ℝ](· | K)`, the Chapter 3
  polar-cone notation `Kᵒ`, and the cone hypothesis owner `Set.IsConvexCone ℝ K`.
- `bridge/view`: the normal-cone identification for indicator subdifferentials from
  `Example_23_0_7` and the polar/normal-cone relation at the origin from Chapter 14 guide the
  intended proof, but the public theorem surface remains directly on the source-facing
  subdifferential owners rather than switching the statement to a normal-cone wrapper.

Domain-style sampling used here:
- `Function.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `Function.subdifferentialAt_indicatorFunction_eq_normalCone` from `Chap05/Example_23_0_7`;
- `polarCone` / `Kᵒ` from `Chap03/Text_14_0_1`;
- `Set.IsConvexCone` from `Chap01/Definition_2_5_10`.

Primitive data vs derived API:
- primitive inputs: the cone `K`, points `x`, `xStar`, and the hypotheses that `K` is nonempty,
  closed, and convex-cone-valued;
- derived API: the mutual equivalence of the primal indicator-subgradient condition, the dual
  indicator-subgradient condition over the polar cone, and the direct complementary-slackness
  conjunction.

Layer target: `source-facing`, using the Chapter 23 indicator-subgradient owner surface and the
project's standard `List.TFAE` shape for multi-clause equivalence statements.
-/

-- Proof sketch: rewrite each indicator-function subdifferential by
-- `subdifferentialAt_indicatorFunction_eq_normalCone`. For a nonempty closed convex cone,
-- Chapter 14 identifies `Kᵒ` with `normalCone K 0` and `normalCone Kᵒ 0` with `K`; transporting
-- the base point from `0` to `x` turns the two normal-cone memberships into the complementary
-- conditions `x ∈ K`, `xStar ∈ Kᵒ`, `⟪x, xStar⟫ = 0`. These three clauses are therefore in one
-- TFAE class.
/-- Corollary 23.5.4: for a nonempty closed convex cone `K`, the following are equivalent:
`xStar ∈ ∂δ(· | K)(x)`, `x ∈ ∂δ(· | Kᵒ)(xStar)`, and the complementary-slackness conditions
`x ∈ K`, `xStar ∈ Kᵒ`, `⟪x, xStar⟫ = 0`. -/
theorem subdifferentialAt_indicatorFunction_polarCone_tfae
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K) (hK : Set.IsConvexCone ℝ K) :
    List.TFAE
      [ xStar ∈ subdifferentialAt (δ[ℝ](· | K)) x,
        x ∈ subdifferentialAt (δ[ℝ](· | ((Kᵒ[ℝ] : PointedCone ℝ E) : Set E))) xStar,
        x ∈ K ∧ xStar ∈ (((Kᵒ[ℝ] : PointedCone ℝ E) : Set E)) ∧ ⟪x, xStar⟫ = (0 : ℝ) ] := sorry

end Function

end
