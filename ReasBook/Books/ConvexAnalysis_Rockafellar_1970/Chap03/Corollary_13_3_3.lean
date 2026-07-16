import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Bornology
open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.3.3 characterizes boundedness of `dom f⋆` for a closed proper
  convex function by global finiteness and a norm-Lipschitz bound, and under that boundedness
  hypothesis identifies the least admissible Lipschitz constant.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  the chapter notation `f⋆`, the chapter effective-domain owner `dom(f⋆)`, the chapter owner
  predicate `f.IsClosedProperConvex`, together with `Bornology.IsBounded`, `LipschitzWith`, and
  `IsLeast`.
- `bridge/view`: the textbook absolute-difference inequality
  `|f z - f x| ≤ α ‖z - x‖` is expressed by `LipschitzWith α (fun x ↦ (f x).toReal)`, while
  under the standing closed-proper-convex hypothesis, the textbook finiteness condition on `f`
  is rendered by `∀ x, f x < ⊤`.

Domain-style sampling used here:
- the conjugate owner notation `f⋆` from Chapter 3;
- the support-function owner theorem
  `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from `Theorem_13_3`;
- the chapter effective-domain notation `dom(f)` and its conjugate specialization `dom(f⋆)`;
- the finite-dimensional owner theorem
  `exists_lipschitzWith_of_recessionFunction_finite_everywhere` from `Theorem_10_5`;
- mathlib's canonical boundedness predicate `IsBounded`;
- mathlib's canonical global-Lipschitz owner `LipschitzWith`.
- `IsLeast` for the least admissible Lipschitz constant under the bounded-domain hypothesis.

Primitive data vs derived API:
- primitive input: the function `f : E → EReal`;
- owner hypothesis: `f.IsClosedProperConvex`, packaging the convexity, properness, and lower
  semicontinuity needed by `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction`;
- additional source-facing hypothesis for the least-constant clause: boundedness of `dom(f⋆)`;
- derived API: the Lipschitz characterization of boundedness and the least admissible Lipschitz
  constant, expressed directly as the supremum of the norm image of that effective domain.

Ambient refinement: the supporting owner declarations already live on arbitrary finite-dimensional
real inner-product spaces, so this corollary is stated at that intrinsic level rather than the
coordinate model `EuclideanSpace ℝ (Fin n)`.

Layer target: `source-facing`, stated directly in the canonical conjugate/effective-domain owner
language without introducing a surrogate wrapper for `dom f⋆`.
-/

variable (f : E → EReal)

-- Proof sketch: reduce boundedness of `dom f⋆` to the support-function estimate
-- `supportFunction (dom f⋆) y ≤ α ‖y‖`, use Theorem 13.3 to rewrite that support function as the
-- recession function of `f`, and then apply Corollary 8.5.1 together with the support-function
-- description of the closed unit ball to translate the estimate into the stated global Lipschitz
-- condition on `f`.
/-- Corollary 13.3.3: for a closed proper convex function `f`, the effective domain
`dom f⋆ = dom(f⋆) = {xStar | f⋆ xStar < ⊤}` is bounded if and only if `f` is finite everywhere
and there exists a nonnegative real number `α` such that `|f z - f x| ≤ α ‖z - x‖` for all `x`
and `z`, expressed canonically by `LipschitzWith α (fun x ↦ (f x).toReal)`. -/
theorem bounded_effectiveDomain_convexConjugate_iff_finiteValued_exists_lipschitzWith
    (hf : f.IsClosedProperConvex) :
    IsBounded dom((f⋆ : E → EReal)) ↔
      (∀ x, f x < ⊤) ∧ ∃ α : NNReal, LipschitzWith α (fun x ↦ (f x).toReal) := sorry

-- Proof sketch: by the first theorem, boundedness of `dom f⋆` is equivalent to existence of a
-- global Lipschitz constant. For each such `α`, Corollary 13.1.1 identifies the domination
-- `supportFunction (dom f⋆) ≤ supportFunction (α • B)` with inclusion `dom f⋆ ⊆ α • B`, so the
-- admissible constants are exactly the upper bounds for the norms of points in `dom f⋆`. Their
-- least element is therefore the supremum of the norm image of `dom f⋆`.
/-- The least nonnegative global Lipschitz bound for `f`, when `dom f⋆` is bounded, is the
supremum of `‖x⋆‖` over all `x⋆ ∈ dom f⋆`. -/
theorem isLeast_lipschitzWith_sSup_norm_image_effectiveDomain_convexConjugate
    (hf : f.IsClosedProperConvex) (hdom_bounded : IsBounded dom((f⋆ : E → EReal))) :
    IsLeast {α : NNReal | LipschitzWith α (fun x ↦ (f x).toReal)}
      (sSup ((‖·‖₊) '' dom((f⋆ : E → EReal)))) := sorry

end
