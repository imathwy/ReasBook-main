import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_10_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient EuclideanOrthant

universe u

variable {E : Type u}
variable {m : ℕ}

/- Theorem 3.1.26 lies in the convex inequality-constrained first-order optimality domain.

Sampled owner-style declarations:
- `LagrangianProblem.feasibleSet` and `LagrangianProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_10_2`, the project owner for finite families of `≤ 0` constraints on a
  feasible subtype;
- `problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible` and
  `LagrangianProblem.slaterCondition_iff` in `Chap01/Definition_1_10_9`, the canonical owner and
  bridge for strict feasibility;
- `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the owner for nonnegative
  multiplier vectors in `ℝ^m`;
- `gradient` / `∇` and `DifferentiableAt.hasGradientAt` in `Chap01/Definition_1_4_7`, the
  canonical owner and bridge for gradients of differentiable real-valued functions on a real
  inner-product space;
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Chap02/Theorem_2_29`, the
  chapter owner for constrained first-order optimality from explicit `HasGradientAt` data on a
  convex set.

Best owner abstraction:
- source-facing: the KKT optimality theorem below, because the textbook item is stated on an
  ambient set `Q ⊆ E` rather than on a pre-packaged problem structure;
- core/canonical: `LagrangianProblem`,
  `problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible`,
  `nonnegativeOrthant m`, `gradient`, `DifferentiableAt`, `HasGradientAt`, and
  `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt`;
- bridge/view: the ambient feasible-set predicate `inequalityConstrainedFeasibleSet`.

Primitive data:
- the ambient feasible set `Q`;
- the objective `f0`;
- the finite inequality family `fi`;
- the candidate point `xStar`;
- the multiplier vector `lam : Λ`;
- the strict-feasibility certificate `∃ x ∈ Q, ∀ i : Fin m, fi i x < 0`;
- differentiability of `f0` and the constraint family `fi` at `xStar`.

Derived API:
- `inequalityConstrainedFeasibleSet`;
- `mem_inequalityConstrainedFeasibleSet_iff`;
- the KKT optimality equivalence.

The earlier version fixed the ambient space to `EuclideanSpace ℝ (Fin n)` even though the public
surface only uses real inner-product-space structure. The refined file keeps the source-facing KKT
surface, reuses the Chapter 1 orthant owner for multiplier nonnegativity, and lowers the ambient
space to the weakest canonical layer used by the statements. The theorem now takes the
source-faithful strict-feasibility hypothesis directly instead of exporting a parallel set-based
Slater wrapper, and the main theorem exposes the KKT certificate directly through the canonical
gradients `∇ f0 xStar` and `∇ (fi i) xStar` instead of a one-off certificate wrapper. -/

/-- The feasible set of the inequality-constrained problem on the ambient set `Q` consists of the
points of `Q` satisfying every scalar constraint `fᵢ(x) ≤ 0`. -/
def inequalityConstrainedFeasibleSet
    (Q : Set E) (fi : Fin m → E → ℝ) : Set E :=
  {x | x ∈ Q ∧ ∀ i : Fin m, fi i x ≤ 0}

/-- Membership in `inequalityConstrainedFeasibleSet Q fi` means belonging to `Q` and satisfying
all scalar inequality constraints. -/
-- Proof sketch: unfold `inequalityConstrainedFeasibleSet`; membership in the set-builder is
-- definitionally the conjunction of `x ∈ Q` and `fi i x ≤ 0` for every constraint index `i`.
theorem mem_inequalityConstrainedFeasibleSet_iff
    {Q : Set E} {fi : Fin m → E → ℝ} {x : E} :
    x ∈ inequalityConstrainedFeasibleSet Q fi ↔
      x ∈ Q ∧ ∀ i : Fin m, fi i x ≤ 0 :=
  Iff.rfl

section

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- Theorem 3.1.26: (Karush--Kuhn--Tucker) under convexity, pointwise differentiability at
`xStar`, and a strict-feasibility point for the constraints, a point `xStar` is an optimal
solution of the
inequality-constrained problem `min {f₀(x) | x ∈ Q, fᵢ(x) ≤ 0 for all i}` if and only if there is
a nonnegative multiplier vector such that `xStar` is primal feasible, the canonical gradients
`∇ f0 xStar` and `∇ (fi i) xStar` yield the Lagrangian variational inequality on `Q`, and the
coordinates obey complementary slackness at `xStar`. -/
-- Proof sketch: rewrite the problem as minimizing `f₀` on
-- `inequalityConstrainedFeasibleSet Q fi`. The forward direction comes from the convex
-- first-order optimality condition together with the max/subdifferential description of the active
-- inequality constraints under the Chapter 1 Slater condition for the restricted subtype problem,
-- which yields a multiplier vector. For the reverse direction, use the `ConvexOn` hypotheses on
-- `f₀` and `fᵢ`, the variational inequality, and
-- complementary slackness to recover the optimality inequality against every feasible point.
theorem isMinOn_iff_exists_karush_kuhn_tucker_multiplier
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    {xStar : E}
    (hf0_diff : DifferentiableAt ℝ f0 xStar)
    (hfi_diff : ∀ i : Fin m, DifferentiableAt ℝ (fi i) xStar)
    (hSlater : ∃ x ∈ Q, ∀ i : Fin m, fi i x < 0) :
    IsMinOn f0 (inequalityConstrainedFeasibleSet Q fi) xStar ↔
      ∃ lam : Λ,
        xStar ∈ inequalityConstrainedFeasibleSet Q fi ∧
          lam ∈ ℝ₊^m ∧
            (∀ x : E, x ∈ Q →
              0 ≤
                inner ℝ
                  (∇ f0 xStar + ∑ i : Fin m, (lam i) • ∇ (fi i) xStar)
                  (x - xStar)) ∧
              ∀ i : Fin m, lam i * fi i xStar = 0 := sorry

end

end
