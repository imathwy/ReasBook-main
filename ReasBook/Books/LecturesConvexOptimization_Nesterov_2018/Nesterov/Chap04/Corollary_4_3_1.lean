import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Assumption_4_3_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Lemma_4_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped CoordinateSubspace

variable {n k t : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Corollary 4.3.1 lies in the Chapter 4 hard-instance / second-order-span / coordinate-subspace
domain.

Sampled owner-style declarations in this domain:
* `IsSecondOrderSpanSequence` together with
  `IsSecondOrderSpanSequence.span_condition` / `IsSecondOrderSpanSequence.sub_mem_span` from
  `Assumption_4_3_1`, the chapter owner for the affine search-space restriction;
* `coordinateSubspace` with notation `ℝ^{k,n}` and `mem_coordinateSubspace_iff` from
  `Chap02/Text_2_13`, the chapter owner/view for prefix-supported vectors;
* `fk_first_second_order_mem_next_coordinate_subspaces` from `Lemma_4_3_1`, the hard-instance
  support-growth theorem for the gradient/Hessian data.

Best owner abstraction:
* source-facing: the corollary that the next iterate of a second-order span sequence for the hard
  instance remains in the next coordinate subspace;
* core/canonical: `IsSecondOrderSpanSequence (fk htn) testPoints` and the owner submodules
  `ℝ^{i,n}`;
* bridge/view: the coordinatewise zero-tail criterion `mem_coordinateSubspace_iff` and the
  hard-instance support-growth theorem from Lemma 4.3.1.

Primitive data:
* the hard-instance objective `fk htn`;
* the test-point sequence `testPoints`;
* the prefix support hypothesis `testPoints i ∈ ℝ^{i,n}` for `i < k + 1`.

Derived API:
* the support conclusion `testPoints (k + 1) ∈ ℝ^{k + 1,n}`.

This file stays source-facing. The corollary should reuse the existing span-sequence owner and the
hard-instance support-growth theorem directly, rather than introducing a parallel wrapper for the
coordinate-support argument.
-/

-- Proof sketch: apply `IsSecondOrderSpanSequence.sub_mem_span` at step `k + 1` for the hard
-- instance `fk htn`, use `testPoints 0 ∈ ℝ^{0,n}` to identify the basepoint with `0`, and feed
-- the earlier support hypotheses through `fk_first_second_order_mem_next_coordinate_subspaces`
-- and the owner search-space condition from `Assumption_4_3_1` to place the next iterate in
-- `ℝ^{k+1,n}`.
/-- Corollary 4.3.1: if the iterates `x_i`, `i = 0, ..., k`, lie in the coordinate subspaces
`ℝ^{i,n}` and the full sequence satisfies Assumption 4.3.1 for the hard-instance objective `f_t`,
with `k + 1 ≤ t ≤ n`, then the next iterate `x_{k+1}` belongs to `ℝ^{k+1,n}`. -/
theorem fk_spanSequence_next_iterate_mem_coordinateSubspace
    (hkt : k + 1 ≤ t) (htn : t ≤ n)
    {testPoints : ℕ → E}
    (hspan : IsSecondOrderSpanSequence (fk htn) testPoints)
    (htestPoints : ∀ i : Fin (k + 1), testPoints i ∈ ℝ^{i,n}) :
    testPoints (k + 1) ∈ ℝ^{k + 1,n} := sorry
