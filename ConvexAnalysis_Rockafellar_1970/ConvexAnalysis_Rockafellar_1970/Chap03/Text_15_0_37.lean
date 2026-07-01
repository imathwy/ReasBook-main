import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise

universe u

section

variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the lemma compares the scaled perspectives `f_λ` and `g_μ`, where `g` is the
  obverse of `f`, under the standing Chapter 15 assumptions on `f`.
- `core/canonical`: the relevant owner declarations are the upstream Section 15 definitions
  `Function.rightScalarMul` and `obverse` from `Text_15_0_31`, together with the standing hypothesis
  package `Function.IsNonnegativeClosedConvexZero`.
- `bridge/view`: the relevant owner bridge is
  `obverse_epigraph_eq_one_sublevel_closedPerspective`, combined with the owner three-branch
  formula `lowerSemicontinuousHull_perspective_apply`, so no parallel wrapper notion is needed
  here.

Domain-style sampling used here:
- `rightScalarMul`;
- `obverse`;
- `lowerSemicontinuousHull_perspective_apply`;
- `obverse_epigraph_eq_one_sublevel_closedPerspective`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`.

Primitive data vs derived API:
- primitive inputs: the upstream Chapter 15 owner declarations `Function.rightScalarMul` and
  `obverse f`, together with the owner hypothesis package
  `f.IsNonnegativeClosedConvexZero`;
- derived API: the single comparison theorem between the `μ`-sublevel condition for `f_λ` and the
  `λ`-sublevel condition for `(obverse f)_μ`.

Layer target: `source-facing`, stated directly using the existing chapter owners.
Ambient minimization: the theorem uses only the Chapter 15 owner layer
`[TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]`; no coordinate model or inner-product
structure is part of the statement itself, and specializing to `EuclideanSpace ℝ (Fin n)` recovers
the textbook `R^n` presentation.
-/

-- Proof sketch: rewrite `(g_μ)(x) ≤ λ` as `g (μ⁻¹ • x) ≤ λ / μ` using the positive-scalar
-- evaluation formula for the positive right scalar multiple. Apply the owner bridge
-- `obverse_epigraph_eq_one_sublevel_closedPerspective` to the positive coordinate
-- `(λ / μ, μ⁻¹ • x)`, use `lowerSemicontinuousHull_perspective_apply` to replace the closed
-- perspective by the scaled perspective `f_(λ / μ) (μ⁻¹ • x)`, and then rewrite that perspective
-- back to
-- `λ * f (λ⁻¹ • x) ≤ μ`, i.e. `f_λ x ≤ μ`.
/-- Text 15.0.37: if `f : E → [0, +∞]` is convex, lower semicontinuous, and satisfies `f 0 = 0`,
then for positive scalars `λ` and `μ`, the inequality `(f_λ)(x) ≤ μ` holds if and only if the
corresponding inequality `(g_μ)(x) ≤ λ` holds for the obverse `g = obverse f`. Specializing
`E` to `EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem perspectiveScale_le_iff_obverse_perspectiveScale_le
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero)
    (lam mu : NNRealˣ) (x : E) :
    ((lam : NNReal) •ʳ f) x ≤ ((mu : ℝ) : EReal) ↔
      ((mu : NNReal) •ʳ obverse f) x ≤ ((lam : ℝ) : EReal) := sorry

end
