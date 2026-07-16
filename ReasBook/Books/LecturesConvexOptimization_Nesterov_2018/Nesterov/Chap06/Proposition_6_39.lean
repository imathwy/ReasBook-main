import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Theorem_6_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open ConditionalGradientContraction

/- Proposition 6.39 lies in the convex first-order upper-model / Hölder-gradient domain.

Sampled owner-style declarations:
- chapter `ConditionalGradientContraction.HolderGradientOn` in `Theorem_6_14`, the Chapter 6
  owner predicate for Hölder-continuous chosen within-derivative fields on the feasible set;
- chapter
  `ConditionalGradientContraction.weighted_objective_le_estimatingFunction_add_contractionError`,
  a downstream consumer that already uses that owner directly;
- chapter `HasHolderLowerModelAt` in `Proposition_6_42`, the companion source-facing lower-model
  predicate built from the same Hölder remainder scale;
- mathlib `ConvexOn`, the canonical convexity owner on a feasible set.

Best owner abstraction:
- source-facing: Proposition 6.39's first-order upper model on a convex feasible set;
- core/canonical: `ConditionalGradientContraction.HolderGradientOn`;
- bridge/view: the upper-model consequence below, obtained from the owner plus convexity of the
  feasible set, stated with the same chosen dual field as the owner.

Primitive data:
- the feasible set `Q`, objective `f`, chosen dual field `g`, Hölder exponent `v`, and Hölder
  constant `Gv`;
- convexity of `Q`;
- the owner hypothesis `HolderGradientOn v Gv Q f g`.

Derived API:
- the upper-model inequality below.

The previous file added local projection lemmas for the conjunction-based owner and then exposed
the proposition through a `ConvexOn`-branded theorem surface. This refinement keeps the
source-facing upper-model statement but moves it to the owner namespace, uses only the convexity
of the feasible set needed to keep the segment in `Q`, removes the redundant `v ≤ 1` guard from
the public API, and now matches the repaired owner exactly by expressing both the hypothesis and
the linearization term through the same chosen dual first-order field `g`.
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ConditionalGradientContraction.HolderGradientOn

-- Proof sketch: use convexity of `Q` to keep the segment from `x` to `y` inside `Q`, apply the
-- fundamental theorem of calculus to `t ↦ f (x + t • (y - x))`, estimate the remainder term with
-- the Hölder bound on `g`, and integrate `t^v` over `[0, 1]`.
/-- Proposition 6.39: if a chosen within-derivative field `g` for `f` on a convex feasible set
`Q` is `v`-Hölder continuous with constant `Gv` for some `0 < v`, then `f` satisfies the
first-order upper model
`f y ≤ f x + g x (y - x) + (Gv / (1 + v)) * ‖y - x‖^(1 + v)` on `Q`. -/
theorem upper_model
    {Q : Set E} {f : E → ℝ} {g : E → StrongDual ℝ E} {v Gv : NNReal}
    (hf : HolderGradientOn v Gv Q f g) (hQ_convex : Convex ℝ Q) (hv : 0 < (v : ℝ))
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤
      f x + g x (y - x) +
        ((Gv : ℝ) / (1 + (v : ℝ))) * Real.rpow ‖y - x‖ (1 + (v : ℝ)) := sorry

end ConditionalGradientContraction.HolderGradientOn

end
