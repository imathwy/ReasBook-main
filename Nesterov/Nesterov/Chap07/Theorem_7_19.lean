import Nesterov.Chap02.Definition_2_5
import Nesterov.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 7.19 lies in the chapter's relative-subgradient / dual-seminorm positivity domain.

Sampled owner-style declarations:
- `StrictlyPositiveOn` in `Chap07/Definition_7_81`, the source-facing positivity predicate on a
  feasible set written directly with the canonical whole-space subdifferential owner
  `∂[Set.univ] f(x)`;
- `Seminorm.dualNorm` and `Seminorm.dualNorm_apply` in `Chap02/Definition_2_5`, the project owner
  for the dual norm of a separated seminorm;
- `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Chap03/Theorem_3_44`, the
  chapter owner bridge for real-valued relative subgradients on a feasible set;
- mathlib `ConvexOn.sup`, the canonical convex-max owner for the pointwise maximum of two convex
  functions on the same feasible set.

Best owner abstraction:
- source-facing: Theorem 7.19's strict-positivity claim for the pointwise maximum
  `x ↦ max (φ x) (L * p x)` on `Q`;
- core/canonical: `p : Seminorm ℝ E` together with `[Seminorm.IsNorm p]`, the owner map
  `p.dualNorm`, and the chapter's relative-subdifferential owner `∂[Q] φ(x)`;
- bridge/view: the conclusion `StrictlyPositiveOn Q`, whose defining inequality is phrased with
  whole-space subgradients of the resulting max-function.

Primitive data:
- the feasible set `Q`;
- the convex objective `φ`;
- the separated seminorm `p : Seminorm ℝ E`;
- the scalar bound `L`.

Derived API:
- the dual norm `p.dualNorm`;
- the strict-positivity theorem below for `fun x ↦ max (φ x) (L * p x)`.

The previous version rebuilt a local `VectorNorm` wrapper and a duplicate dual-norm definition with
the exact same mathematical content as the Chapter 2 owner `Seminorm.dualNorm`. This refinement
deletes that duplicate owner, removes the theorem-local max wrapper, and states the subgradient
bound on the canonical relative owner `∂[Q] φ(x)` that matches `ConvexOn ℝ Q φ`.
-/

-- Proof sketch: let `f x = max (φ x) (L * p x)` and verify the defining inequality of
-- `StrictlyPositiveOn`. If `φ x < L * p x`, use a norming functional for `p` at `x` scaled by `L`.
-- If `φ x > L * p x`, use the assumed dual-norm bound on subgradients of `φ` together with the
-- triangle inequality. In the boundary case `φ x = L * p x`, pass to the limit through convex
-- combinations of the first two cases.
/-- Theorem 7.19: if `φ` is convex on `Q` and every subgradient of `φ` on `Q`
has dual norm at most `L`, then the augmented function
`x ↦ max (φ x) (L * p x)` is strictly positive on `Q` in the sense of Definition 7.81. -/
theorem strictlyPositiveOn_max_of_subgradientWithin_dualNorm_le
    (Q : Set E) (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    (φ : E → ℝ) (L : ℝ)
    (hφ_convex : ConvexOn ℝ Q φ) (hL_nonneg : 0 ≤ L)
    (hsubgradient_bound :
      ∀ ⦃x g : E⦄, g ∈ ∂[Q] φ(x) → p.dualNorm g ≤ L) :
    StrictlyPositiveOn Q (fun x ↦ max (φ x) (L * p x)) := sorry
