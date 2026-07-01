import Nesterov.Chap03.Definition_3_1_5
import Nesterov.Chap03.Definition_3_22
import Nesterov.Chap03.LinearEqualityFeasibleSet

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology
open scoped NormalCone
open scoped WithTopConvexAnalysis

universe u v

variable {E : Type u} {Λ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ] [FiniteDimensional ℝ Λ]

/- Theorem 3.1.27 lies in the chapter's equality-constrained extended-valued convex-optimality
domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on finite-dimensional real inner-product spaces
  with linear equality constraints.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite-value representative;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients;
- `normalCone`, the notation `N[Q] x`, and `mem_normalCone_iff` in `Definition_3_22`, the chapter
  owner API for textbook normal cones;
- `constrainedSublevelSet` in `Definition_3_3`, the chapter owner for constrained sublevel sets;
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the chapter owner for the feasible
  set cut out by `x ∈ Q` and `A x = b`.

Best owner abstraction:
- the source-facing theorem stated directly on the chapter owners
  `ConvexOn ℝ (dom f) (withTopRealPart f)`, `∂ f(xStar)`, `N[Q] xStar`,
  `constrainedSublevelSet`, and `linearEqualityFeasibleSet`.

Primitive data:
- a closed convex feasible set `Q`;
- an extended-real-valued objective `f`;
- a linear map `A` and right-hand side `b`;
- a Slater point `xBar` with a feasible ball `Metric.ball xBar ε ⊆ Q`.

Derived API:
- the feasibility conclusion `A xStar = b`;
- an owner-level subgradient witness `gStar ∈ ∂ f(xStar)`;
- the owner-level normal-cone condition `gStar - A.adjoint yStar ∈ N[Q] xStar`;
- the quantitative Slater-radius bound on `‖A.adjoint yStar‖`.

Source/core/bridge triage:
- source-facing: the quantitative equality-constrained optimality theorem;
- core/canonical: `dom`, `withTopRealPart`, `∂`, `N[Q] xStar`,
  `constrainedSublevelSet`, and `linearEqualityFeasibleSet`;
- bridge/view: matrix / transpose and relative-subgradient reformulations in downstream files.

The previous version rebuilt local copies of the effective domain, finite real part, convexity
predicate, subgradient predicate, subdifferential, and constrained sublevel set, then repackaged
the resulting theorem witnesses in a one-off certificate structure. Those notions are already
owned earlier in the chapter, so this refinement deletes the duplicate wheel layer and the local
wrapper, and states the theorem directly on the canonical chapter surface. The normal-cone
component is kept on the owner abstraction `N[Q] xStar`, with the raw pairing inequality treated
as the companion view supplied by `mem_normalCone_iff` rather than as the main public statement.
-/

/-- Theorem 3.1.27: for a convex function on a closed convex set
`Q ⊆ interior (dom f)` with bounded constrained sublevel sets, under the equality Slater
condition `A xBar = b` and `Metric.ball xBar ε ⊆ Q`, a point `xStar` minimizes
`withTopRealPart f` over `{x ∈ Q | A x = b}` if and only if
`xStar ∈ linearEqualityFeasibleSet Q A b` and there exist a multiplier `yStar` and a subgradient
`gStar ∈ ∂ f(xStar)` such that `gStar - A.adjoint yStar ∈ N[Q] xStar`; moreover the certificate
can be chosen so that `‖A.adjoint yStar‖ ≤
(sSup (withTopRealPart f '' Metric.ball xBar ε) - sInf (withTopRealPart f '' Q)) / ε`.
-/
-- Proof sketch: for the reverse implication, combine the subgradient inequality for
-- `gStar ∈ ∂ f(xStar)` with the normal-cone inequality supplied by `mem_normalCone_iff`, and use
-- `A x = A xStar = b` on feasible points to cancel the multiplier term. For the forward
-- implication, minimize the penalized function `x ↦ f x + K ‖b - A x‖` on `Q`, apply first-order
-- optimality on `Q`, decompose a subgradient of the penalty through the adjoint `A.adjoint`, and
-- use the Slater ball of radius `ε` to derive the bound on `‖A.adjoint yStar‖` after dividing
-- the value gap by `ε`.
theorem isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    (hlevel_bounded : ∀ α : ℝ, Bornology.IsBounded (constrainedSublevelSet Q f α))
    {A : E →ₗ[ℝ] Λ} {b : Λ} {xBar : E} {ε : ℝ}
    (hbar : A xBar = b) (hε : 0 < ε) (hball : Metric.ball xBar ε ⊆ Q) {xStar : E} :
    IsMinOn (withTopRealPart f) (linearEqualityFeasibleSet Q A b) xStar ↔
      xStar ∈ linearEqualityFeasibleSet Q A b ∧
        ∃ yStar : Λ, ∃ gStar ∈ ∂ f(xStar),
          gStar - A.adjoint yStar ∈ N[Q] xStar ∧
            ‖A.adjoint yStar‖ ≤
              (sSup (withTopRealPart f '' Metric.ball xBar ε) -
                  sInf (withTopRealPart f '' Q)) / ε := sorry

end
