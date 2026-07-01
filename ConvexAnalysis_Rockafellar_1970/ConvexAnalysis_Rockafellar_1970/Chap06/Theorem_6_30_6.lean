import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Function.IsClosedProperConvex

variable {f : E → WithTopBot 𝕜} {x : E} {xStar : StrongDual 𝕜 E}

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.6 is the Fenchel-conjugate symmetry of the subdifferential
  relation for a closed proper convex function.
- `core/canonical`: the owner-level statement is intrinsically relation-theoretic on
  `_root_.subdifferentialGraph`, namely `subdifferentialGraph_convexConjugate_eq_inv`.
- `bridge/view`: the Euclidean same-carrier statement
  `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff` remains available
  upstream as a Fréchet-Riesz bridge; this file keeps the intrinsic owner surface only.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and `_root_.subdifferentialGraph` from
  `Chap05.Definition_23_0_6` / `Chap05.Definition_5_24_3`;
- `subdifferentialGraph_convexConjugate_eq_inv` from `Chap05.Text_26_0_1`;
- `SetRel.mem_inv` from mathlib `Data.Rel`;
- convex conjugation notation `(·)⋆`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`.

Primitive data vs derived API:
- primitive owner inputs: a function `g : E → WithTopBot 𝕜`, primal point `x : E`,
  dual point `xStar : StrongDual 𝕜 E`, and `g.IsClosedProperConvex`;
- derived bridge API (upstream): the Euclidean same-carrier subgradient equivalence in
  Corollary 23.5.1.

Layer target: expose Theorem 6.30.6 on the intrinsic pairing/graph owner layer.

Scalar/ambient check:
- this declaration no longer uses `InnerProductSpace` or `CompleteSpace`;
- the scalar is generalized from `ℝ` to a conditionally complete ordered normed field `𝕜`,
  matching the primitive owner theorem `subdifferentialGraph_convexConjugate_eq_inv`.
-/

-- Proof sketch: `subdifferentialGraph_convexConjugate_eq_inv` gives graph-level inversion for
-- closed proper convex `f`. Evaluating that relation identity at the pair `(xStar, x)` and
-- rewriting membership in an inverse relation with `SetRel.mem_inv` gives exactly the two
-- owner-level subdifferential membership clauses.
/-- Theorem 6.30.6, intrinsic owner form on the strong-dual bridge: for a closed proper convex
function, subgradient membership for the conjugate at `xStar : StrongDual 𝕜 E` is equivalent to
primal-side subgradient membership at `x`. -/
theorem mem_subdifferentialAt_convexConjugate_iff_strongDual
    (hf : IsClosedProperConvex[𝕜] f) :
    x ∈ (∂[E](f⋆)(xStar)) ↔ xStar ∈ (∂ f at x) := by
  have hgraphEq :
      gph∂[E](f⋆) = (gph∂(f)).inv :=
    _root_.subdifferentialGraph_convexConjugate_eq_inv (f := f) hf
  have hpair :
      (xStar, x) ∈ gph∂[E](f⋆) ↔
        (xStar, x) ∈ (gph∂(f)).inv :=
    Iff.of_eq (congrArg (fun R => (xStar, x) ∈ R) hgraphEq)
  change
      (xStar, x) ∈ gph∂[E](f⋆) ↔
        (x, xStar) ∈ gph∂(f)
  exact hpair.trans (SetRel.mem_inv (R := gph∂(f)) (a := x) (b := xStar))

end Function.IsClosedProperConvex

end
