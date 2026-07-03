import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_46 (from Chap03) -/
noncomputable section

open scoped BigOperators

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

open scoped ApproximateLagrangeMultiplierSwitchingNotation

local notation "φ" => problem.toLagrangianProblem.dualFunction

/- Definition 3.46 lies in the chapter's approximate-multiplier primal-dual gap domain.

Sampled owner-style declarations:
- `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintIndices`,
  `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintCount`,
  `ApproximateLagrangeMultiplierSwitchingMethod.inverseSubgradientNormSum`, and
  `ApproximateLagrangeMultiplierSwitchingMethod.approximateDualMultiplier` in `Definition_3_45`,
  the source-facing owners of `A₀(t)`, `N(t)`, `S_t`, and `λ_t`;
- `ProjectedMultipleConstraintFirstOrderProblem.toLagrangianProblem` in `Algorithm_3_4`, the
  canonical bridge from the switching-method problem to the Chapter 1 Lagrangian owner on
  `Q = problem.feasibleSet`;
- `LagrangianProblem.dualFunction` in `Chap01/Definition_1_10_2`, the owner dual value `φ`;
- mathlib `Finset.centerMass`, the canonical normalized finite-average owner used for the primal
  average itself.

Best owner abstraction:
- a run `method : ApproximateLagrangeMultiplierSwitchingMethod problem`, viewed through
  Definition 3.45 for the source data `A₀(t)`, `N(t)`, `S_t`, and `λ_t`, through
  `Finset.centerMass` on `A₀(t)` itself for the normalized primal average, and through the
  feasible-set Lagrangian owner `problem.toLagrangianProblem` for the dual term.

Primitive data:
- the switching-method run `method`;
- the stage index `t`.

Derived API:
- the inactive index set `A₀(t)`;
- the source count `N(t) = |A₀(t)|`;
- the owner reciprocal weights, normalization sum, and multiplier from Definition 3.45;
- the source weighted primal term, obtained canonically as the `centerMass` over `A₀(t)` with
  those owner weights;
- the dual value of the corresponding approximate multiplier.

Source/core/bridge triage:
- source-facing: `primalDualGapQuantity`;
- core/canonical: the run `method` together with the Definition 3.45 owner data and the
  Lagrangian owner `problem.toLagrangianProblem`, plus `Finset.centerMass` for the normalized
  finite average in the primal term;
- bridge/view: the `Finset.centerMass` realization of the weighted primal term and the Chapter 1
  dual-value specialization at the source-facing multiplier `λ_t`.

Unlike the generic Chapter 3 weighted-gap owners, this source item is tied specifically to the
Algorithm 3.4 multiplier `λ_t` from Definition 3.45 and to the Chapter 1 extended-real dual
function. Its primal term is still expressed canonically using `Finset.centerMass`, and the
full denominator regime is inherited directly from Definition 3.45's source-facing owners rather
than through a parallel local copy. -/

/-- Definition 3.46: for the feasible-set Lagrangian bridge attached to a run of Algorithm 3.4,
the primal--dual gap quantity `δ[method](t; hdenom)` is the difference between the owner weighted
primal average over `A₀[method](t)` and the canonical dual value at the approximate multiplier
`λ[method](t; hdenom)`. Under the full denominator regime `hdenom` from Definition 3.45, this is
the textbook quantity
`S_t⁻¹ ∑_{k ∈ A₀[method](t)} f(x_k) / ‖g(x_k)‖ - φ(λ_t)`. The value is taken in `EReal` because
`LagrangianProblem.dualFunction` is extended-real-valued. -/
def primalDualGapQuantity
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hdenom : method.HasApproximateDualMultiplierDenominators t) : EReal :=
  (((A₀[method](t)).centerMass
      (fun k ↦ ‖method.objectiveSubgradient k‖⁻¹)
      (fun k ↦ problem.objective (method k)) : ℝ) : EReal) -
    φ (λ[method](t; hdenom))

/- Source-facing Lean notation for the textbook primal--dual gap quantity `δ_t`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "δ[" method:arg "](" t:arg "; " hdenom:arg ")" =>
  primalDualGapQuantity method t hdenom

end ApproximateLagrangeMultiplierSwitchingNotation

end ApproximateLagrangeMultiplierSwitchingMethod

/-! ### Proposition_3_46 (from Chap03) -/
noncomputable section

universe v

open MeasureTheory

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E]

local notation "dim" => Module.finrank ℝ E

attribute [local instance] Classical.decPred

/- Proposition 3.46 lies in the chapter's selected-feasible best-value domain.

Mandatory domain-style sampling before refinement:
- `Nat.count`, `feasibleSubsequence`, and
  `feasibleSubsequence_count_eq_self_of_feasible` from `Definition_3_53`, the chapter owners for
  the canonical selected feasible index and subsequence;
- `bestFunctionValueUpTo` from `Definition_3_55`, the owner for sampled prefix minima;
- `selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_`
  `le_lipschitz_radius_mul_geometricDecay_volumeRatio` from `Theorem_3_54`, the owner-level
  selected-feasible best-value estimate;
- mathlib `IsMinOn` and `LipschitzOnWith`, the canonical optimization and regularity owners used
  by that estimate.

Best owner abstraction:
- source-facing: the selected-feasible best sampled objective value up to the canonical feasible
  count `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- core/canonical: `bestFunctionValueUpTo` together with the owner theorem from `Theorem_3_54`;
- bridge/view: the specialization obtained by taking the selected sequence to be
  `feasibleSubsequence Q querySeq` and then rewriting the selected term at counted position with
  `feasibleSubsequence_count_eq_self_of_feasible`.

Primitive data:
- the objective `f`, closed-ball minimizer `xStar`, outer ball data `x0`, `R`, Lipschitz constant
  `M`, feasible set `Q`, raw query sequence `querySeq`, and the raw feasible query `querySeq k`;
- the closed-ball membership and distance estimate for that raw feasible query.

Derived API:
- the canonical selected feasible subsequence `feasibleSubsequence Q querySeq`;
- the canonical selected-feasible prefix count `Nat.count (fun j ↦ querySeq j ∈ Q) k`;
- the owner best-value bound on
  `bestFunctionValueUpTo (fun j ↦ f (feasibleSubsequence Q querySeq j))
    (Nat.count (fun j ↦ querySeq j ∈ Q) k)`.

Source/core/bridge triage:
- source-facing: the best feasible sampled-value estimate along the first `k + 1` raw queries;
- core/canonical: `bestFunctionValueUpTo` and the owner theorem from `Theorem_3_54`;
- bridge/view: passage from a raw feasible query `querySeq k` to the selected-feasible owner
  surface via `feasibleSubsequence_count_eq_self_of_feasible`.

The previous version erased this source-facing chapter statement and kept only a generic scalar
monotonicity lemma. That scalar step is not the owner of the mathematics here. This refinement
restores Proposition 3.46 as the thin bridge that the chapter actually uses: a theorem on the
canonical owners `bestFunctionValueUpTo`, `Nat.count`, and `feasibleSubsequence`, proved by direct
reuse of `Theorem_3_54`.
-/

set_option linter.style.longLine false
/-- Proposition 3.46: let `X = feasibleSubsequence Q querySeq` be the canonical selected feasible
subsequence of a raw query sequence `querySeq`, and let
`i(k) = Nat.count (fun j ↦ querySeq j ∈ Q) k` be the corresponding selected-feasible prefix count.
If `querySeq k` is feasible, if `f` is `M`-Lipschitz on `B₂(xStar, R)`, if `xStar` realizes the
infimum of `f` on that ball, and if the raw feasible query `querySeq k` satisfies the standard
distance estimate to `xStar`, then the best sampled objective value among the first `i(k) + 1`
selected feasible points satisfies the same decay estimate relative to
`sInf (f '' Metric.closedBall xStar R)`. -/
theorem selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_le_lipschitz_radius_mul_geometricDecay_volumeRatio_of_feasible
    (μ : Measure E)
    {f : E → ℝ} {Q : Set E} {querySeq : ℕ → E} {xStar x0 : E} {R : ℝ} {M : NNReal}
    (k : ℕ)
    (hf_lipschitz : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hxStar_opt : IsMinOn f (Metric.closedBall xStar R) xStar)
    (hk : querySeq k ∈ Q)
    (hquery_mem : querySeq k ∈ Metric.closedBall xStar R)
    (hquery_dist :
      ‖querySeq k - xStar‖ ≤
        R *
          Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
            Real.rpow
              (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
              (1 / (dim : ℝ))) :
    bestFunctionValueUpTo
        (fun j ↦ f (feasibleSubsequence Q querySeq j))
        (Nat.count (fun j ↦ querySeq j ∈ Q) k) -
        sInf (f '' Metric.closedBall xStar R) ≤
      (M : ℝ) * R *
        Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
          Real.rpow
            (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
            (1 / (dim : ℝ)) := by
  let X : ℕ → E := feasibleSubsequence Q querySeq
  let i : ℕ → ℕ := Nat.count (fun j ↦ querySeq j ∈ Q)
  have hselected_eq :
      X (i k) = querySeq k :=
    feasibleSubsequence_count_eq_self_of_feasible Q querySeq hk
  have hselected_mem :
      X (i k) ∈ Metric.closedBall xStar R := by
    simpa [hselected_eq] using hquery_mem
  have hselected_dist :
      ‖X (i k) - xStar‖ ≤
        R *
          Real.rpow (1 - 1 / (((dim : ℝ) + 1) ^ (2 : ℕ))) ((k : ℝ) / 2) *
            Real.rpow
              (Measure.real μ (Metric.closedBall x0 R) / Measure.real μ Q)
              (1 / (dim : ℝ)) := by
    simpa [hselected_eq] using hquery_dist
  simpa using
    selected_feasible_bestObjectiveValue_sub_sInf_image_closedBall_le_lipschitz_radius_mul_geometricDecay_volumeRatio
      μ
      k
      hf_lipschitz
      hxStar_opt
      hselected_mem
      hselected_dist

end

/-! ### Theorem_3_46 (from Chap03) -/
noncomputable section

universe u

/- Theorem 3.46 lies in the constrained strong-convexity domain on real normed spaces.

Sampled owner-style declarations:
- project `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Theorem_2_30`
- project `StrongConvexOn.eq_of_isMinOn` in `Chap03/Theorem_3_45`
- mathlib `StrongConvexOn`
- mathlib `StrongConvexOn.strictConvexOn`

Best owner abstraction:
- source-facing: the constrained quadratic-growth and uniqueness consequences for a positive
  strongly convex objective on a convex feasible set
- core/canonical: `StrongConvexOn Q μ f`
- bridge/view: passing from strong convexity to strict convexity via
  `StrongConvexOn.strictConvexOn`

Primitive data:
- a feasible set `Q`, an objective `f`, a modulus `μ`, and feasible minimizers of `f` on `Q`

Derived API:
- the constrained quadratic-growth estimate
- uniqueness of feasible minimizers for `μ > 0`

This item is a direct recall of the chapter's owner-level constrained strong-convexity API, so it
keeps the canonical declarations central instead of restating them under parallel local names. -/

namespace StrongConvexOn

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.46 (quadratic-growth part): this is exactly the owner theorem
`StrongConvexOn.quadratic_growth_of_isMinOn_of_mem`. -/
recall StrongConvexOn.quadratic_growth_of_isMinOn_of_mem

/- Theorem 3.46 (uniqueness part): positive strong convexity gives strict convexity, so the
canonical constrained uniqueness theorem is `StrongConvexOn.eq_of_isMinOn`. -/
recall StrongConvexOn.eq_of_isMinOn

end StrongConvexOn

end
