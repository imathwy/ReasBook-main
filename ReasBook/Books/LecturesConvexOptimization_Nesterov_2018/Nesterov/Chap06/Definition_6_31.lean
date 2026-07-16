import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p]
variable {Q : Set E} {d : E → ℝ}

/- Domain sampling for the prox-function / prox-center item.

Sampled owner declarations:
- mathlib `ContinuousOn`, the canonical owner for continuity on a feasible set;
- project `StrongConvexOnWith`, the source-faithful owner for strong convexity with respect to a
  chosen seminorm;
- mathlib `IsMinOn`, the canonical owner for minimizers on a feasible set;
- project `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem`, the canonical lower-bound
  theorem attached to strong convexity at a feasible minimizer.

Source/core/bridge triage:
- source-facing: the prox-center of `d` on `Q` and its normalized quadratic lower bound;
- core/canonical: `ContinuousOn`, `StrongConvexOnWith`, `IsMinOn`, and the quadratic-growth
  theorem at a feasible minimizer;
- bridge/view: the chapter owners `IsProxFunction` and `IsProxCenter`, which package the
  prox-function hypothesis and the normalized minimizing point used in the lower bound.

Primitive data:
- the norm-like seminorm `p`, feasible set `Q`, prox-function candidate `d`, and candidate
  center `x₀`;
- for `IsProxFunction`, continuity and unit strong convexity on `Q` with respect to `p`;
- for `IsProxCenter`, feasibility, minimization on `Q`, and the normalization `d x₀ = 0`;
- for the quadratic lower bound, a feasible comparison point `x ∈ Q`.

Derived API:
- `IsProxFunction.continuousOn` and `IsProxFunction.strongConvexOnWith`;
- `IsProxCenter.mem`, `IsProxCenter.isMinOn`, and `IsProxCenter.value_eq_zero`.
-/

/-- A prox-function on `Q` with respect to the norm `p` is continuous on `Q` and
`1`-strongly convex on `Q` with respect to `p`. -/
class IsProxFunction (p : Seminorm ℝ E) [Seminorm.IsNorm p] (Q : Set E) (d : E → ℝ) : Prop where
  /-- A prox-function is continuous on the feasible set. -/
  continuousOn : ContinuousOn d Q
  /-- A prox-function is `1`-strongly convex on the feasible set with respect to the chosen norm.
  -/
  strongConvexOnWith : StrongConvexOnWith p 1 Q d

/-- A prox-function hypothesis canonically supplies unit strong convexity on the feasible set
with respect to the chosen norm. -/
instance [hd : IsProxFunction p Q d] : Fact (StrongConvexOnWith p 1 Q d) where
  out := hd.strongConvexOnWith

/-- Definition 6.31 [Chapter6_1.json:68]: a prox-center of `d` on `Q` is a feasible minimizer
`x₀`, together with the standard normalization `d x₀ = 0`. -/
structure IsProxCenter (Q : Set E) (d : E → ℝ) (x₀ : E) : Prop where
  /-- A prox-center belongs to the feasible set. -/
  mem : x₀ ∈ Q
  /-- A prox-center minimizes `d` on the feasible set. -/
  isMinOn : IsMinOn d Q x₀
  /-- The prox-function is normalized to vanish at the prox-center. -/
  value_eq_zero : d x₀ = 0

/-- A prox-center canonically supplies its minimizing property on the feasible set as a `Fact`. -/
instance {Q : Set E} {d : E → ℝ} {x₀ : E} (hx₀ : IsProxCenter Q d x₀) :
    Fact (IsMinOn d Q x₀) where
  out := hx₀.isMinOn

end
