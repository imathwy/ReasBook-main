import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-
Proposition 6.40 lies in the second-order Hölder upper-model domain on real normed spaces.

Sampled owner-style declarations:
- mathlib `HolderOnWith`, the canonical on-set owner for Hölder continuity of a map;
- mathlib `DifferentiableOn`, the canonical on-set owner for Fréchet differentiability;
- mathlib `UniqueDiffOn`, the canonical hypothesis ensuring that higher within derivatives are
  intrinsic on a feasible set;
- mathlib `iteratedFDerivWithin`, the canonical higher-order owner for within-set Fréchet
  derivatives;
- Chapter 6 `ConditionalGradientContraction.HolderGradientOn` in `Theorem_6_14`, the first-order
  chapter owner for Hölder regularity of the canonical within derivative on a convex feasible set;
- mathlib `contDiffOn_succ_iff_fderivWithin`, the owner equivalence showing that on a
  `UniqueDiffOn` set the canonical higher differential layer is organized around `fderivWithin`;
- mathlib `iteratedFDerivWithin_two_apply'`, the bridge identifying the second iterated within
  derivative with the nested `fderivWithin` formula on uniquely differentiable sets.

Source/core/bridge triage:
- source-facing: Proposition 6.40's quadratic upper model under Hölder continuity of the second
  derivative;
- core/canonical: `DifferentiableOn ℝ f Q`, `DifferentiableOn ℝ (fderivWithin ℝ f Q) Q`, and
  `HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q`;
- bridge/view: the pointwise quadratic-model inequality below.

Primitive data:
- the feasible set `Q`, objective `f`, Hölder exponent `v`, and Hölder constant `H`;
- convexity of `Q`;
- unique differentiability of `Q`, making the within-derivative layers intrinsic;
- differentiability on `Q` of `f` and of its canonical within derivative;
- Hölder continuity on `Q` of the canonical iterated within second-derivative map.

Derived API:
- the quadratic upper-model inequality below.

The previous file used ambient derivatives `fderiv ℝ f` and `fderiv ℝ (fderiv ℝ f)` on an
arbitrary convex set `Q`, which over-specialized the statement to neighborhood differentiability
at boundary points. This refinement keeps the source-facing proposition but moves its primitive
data to the canonical within-set layer: `fderivWithin` for first-derivative existence and
`iteratedFDerivWithin ℝ 2 f Q` for the public second-derivative owner. Because higher within
derivatives are only intrinsic on uniquely differentiable sets, the public API now records
`UniqueDiffOn ℝ Q` explicitly instead of treating convexity alone as sufficient. The nested
`fderivWithin` formula survives only as an internal bridge via
`iteratedFDerivWithin_two_apply'`. This matches the Chapter 6 owner style on feasible sets while
remaining faithful for lower-dimensional convex sets, and removes the redundant positivity guard
on `v`. -/

/-- Proposition 6.40: if the canonical iterated within second Fréchet derivative of `f` is
`v`-Hölder on the convex set `Q`, then `f` admits the quadratic upper model with Hölder
remainder `H * ‖y - x‖^(2 + v) / ((1 + v) * (2 + v))`. -/
-- Proof sketch: restrict `f` to the line segment `t ↦ x + t • (y - x)`, apply the
-- one-dimensional second-order Taylor formula with integral remainder, and bound the remainder
-- using the Hölder estimate on `iteratedFDerivWithin ℝ 2 f Q`; when one needs the nested
-- derivative formula inside the proof, recover it from `iteratedFDerivWithin_two_apply'`
-- together with `UniqueDiffOn ℝ Q` and convexity of `Q`.
theorem holder_hessian_upper_model
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {f : E → ℝ} {v H : NNReal}
    (hQ_unique : UniqueDiffOn ℝ Q)
    (hf : DifferentiableOn ℝ f Q)
    (hf' : DifferentiableOn ℝ (fderivWithin ℝ f Q) Q)
    (hH : HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤
      f x + fderivWithin ℝ f Q x (y - x) +
        (1 / 2 : ℝ) * iteratedFDerivWithin ℝ 2 f Q x ![y - x, y - x] +
          (H : ℝ) * Real.rpow ‖y - x‖ (2 + (v : ℝ)) /
            ((1 + (v : ℝ)) * (2 + (v : ℝ))) := sorry
