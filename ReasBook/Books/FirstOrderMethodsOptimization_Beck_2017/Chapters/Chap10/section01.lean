import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Assumption_10_1 (from Chap10) -/
/- Assumption 10.1 is recall-only in Chapter 10. Its `source-facing` content is the standing
assumption package for the composite model `min_x {f(x) + g(x)}`, and the exact `core/canonical`
owner already exists as `IsCompositeSmoothMinimizationProblem`; there is no new mathematics here
that would justify a second wrapper, alias, or unpacking theorem. -/

/- Assumption 10.1: the standing hypotheses (A)-(C) for the composite model
`min_x {F(x) = f(x) + g(x)}` are the existing owner class
`IsCompositeSmoothMinimizationProblem`, which packages that `g : E → (-∞, ∞]` is proper, closed,
and convex; that `f : E → (-∞, ∞]` never takes the value `-∞`, is closed, has convex effective
domain, satisfies `effective_domain g ⊆ interior (effective_domain f)`, and has
`(fun x ↦ (f x).toReal)` `L_f`-smooth on `interior (effective_domain f)`; consequently `f` is
proper; and that the optimal set `X^*` is nonempty with optimal value `F_opt`. -/
recall IsCompositeSmoothMinimizationProblem

/-! ### Definition_10_1 (from Chap10) -/
universe u

section

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 10.1 is recall-only. The ambient Euclidean-space owner was already fixed in
Definition 1.14, so the Chapter 10 entry should reuse that same canonical surface rather than
repeat a parallel local wrapper.

Domain sampling in the ambient geometry API gives:
- `source-facing`: the Chapter 10 Euclidean-space recall;
- `core/canonical`: `InnerProductSpace ℝ E`, `FiniteDimensional ℝ E`, and
  `norm_eq_sqrt_real_inner`;
- `bridge/view`: none.

Primitive data are only the real inner-product structure and finite-dimensionality; the norm is
derived API from that owner. -/

/- Definition 10.1: a Euclidean space carries the canonical real inner product structure
`InnerProductSpace ℝ E`. -/
#check InnerProductSpace ℝ E

/- Definition 10.1: finite-dimensionality is the standard predicate `FiniteDimensional ℝ E`. -/
#check FiniteDimensional ℝ E

/- Definition 10.1: the Euclidean norm is the norm induced by the ambient inner product, with
canonical evaluation rule `norm_eq_sqrt_real_inner`. -/
recall norm_eq_sqrt_real_inner

end
