import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_1_30 (from Chap03) -/
noncomputable section

universe u v

variable {E : Type u} {U : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [ProperSpace U]

/-
Theorem 3.1.30 lies in the chapter's bounded-set minimax / saddle-value existence domain on
proper real normed spaces.

Mandatory domain-style sampling:
- `MaxRepresentationPrimalDualProblem` in `Chap03/Definition_3_28`, the chapter owner for the
  primal feasible set, objective, dual set, kernel, slice geometry, and max-representation data;
- `MaxRepresentationPrimalDualProblem.objective_eq_pointwiseSupremumOn` in
  `Chap03/Definition_3_28`, the canonical bridge from the source max-attainment hypothesis to the
  chapter upper-envelope owner;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project
  owner for the primal infimum value;
- `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer` in
  `Chap03/Lemma_3_22`, the nearby attainment owner for a maximizing dual parameter.

Best owner abstraction:
- source-facing: the bounded-set minimax equality `(3.1.79)` and the resulting attained dual
  maximizer / primal minimum statement;
- core/canonical: `MaxRepresentationPrimalDualProblem E U` together with the inherited primal
  owner `SetConstrainedMinimizationProblem` and its `optimalValue`;
- bridge/view: `objective_eq_pointwiseSupremumOn`, relating the source objective to the canonical
  upper-envelope owner already stored by the max-representation problem.

Primitive data:
- the primal objective and feasible set, already owned by
  `problem.toSetConstrainedMinimizationProblem`;
- the dual set `problem.dualSet`;
- the kernel `problem.kernel`;
- the slice closed-convex / closed-concave data and the max-attainment representation, already
  primitive fields of `MaxRepresentationPrimalDualProblem`.

Derived API:
- the source minimax equality
  `sInf (problem '' problem.feasibleSet) = sSup ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) ''
    problem.feasibleSet)) '' problem.dualSet)`;
- the Chapter 1 owner equality for
  `problem.toSetConstrainedMinimizationProblem.optimalValue`;
- the attained dual maximizer and primal least-value witness.

Source/core/bridge triage:
- source-facing: the minimax equality and attainment theorem in this file;
- core/canonical: `MaxRepresentationPrimalDualProblem` and
  `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the owner theorem `objective_eq_pointwiseSupremumOn`.

The previous version duplicated the owner data as a raw tuple `{P, S, Ψ, f}` together with
separate slice hypotheses and an `hf_eq` bridge. This refinement deletes that duplicate wheel and
states Theorem 3.1.30 directly for `problem : MaxRepresentationPrimalDualProblem E U`. The primal
nonemptiness hypothesis remains explicit, while dual nonemptiness is now derived from the owner by
`problem.dualSet_nonempty`. The main theorem is the source minimax equality `(3.1.79)` on the
owner layer; the explicit `uStar` / `IsLeast` conclusion is kept only as a companion.
-/

/-- Theorem 3.1.30: for a bounded max-representation primal-dual problem on proper real normed
spaces, if the primal feasible set is nonempty and both the primal feasible set and dual set are
bounded, then the primal minimum equals the dual maximum:
`min_{x ∈ P} f(x) = max_{u ∈ S} inf_{x ∈ P} Ψ(x, u)`.

Here the data `P`, `S`, `Ψ`, and `f` are carried canonically by
`problem : MaxRepresentationPrimalDualProblem E U`, rather than repeated as separate tuple
arguments. -/
-- Proof sketch: use the owner fields of `problem` to recover the slice closed-convex and
-- closed-concave hypotheses needed in the bounded minimax existence argument. Boundedness and
-- properness give an attained maximizing parameter `uStar` for the lower-value function
-- `u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)`; the Chapter 3 bridge in
-- `Definition_3_28` identifies the primal objective with the canonical upper envelope. The
-- resulting saddle-value identity yields the displayed minimax equality.
theorem minimax_eq_of_bounded_maxRepresentationPrimalDualProblem
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    sInf (problem '' problem.feasibleSet) =
      sSup ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)) ''
        problem.dualSet) := sorry

/-- Owner-value bridge for Theorem 3.1.30: the same minimax equality written with the canonical
Chapter 1 optimal-value owner on the primal side. -/
-- Proof sketch: combine
-- `exists_dual_maximizer_with_primal_minimum_of_bounded_sets` with
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, or equivalently coerce the
-- real-valued equality above to `EReal` after identifying the attained primal minimum.
theorem optimalValue_eq_dualValue_of_bounded_maxRepresentationPrimalDualProblem
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    problem.toSetConstrainedMinimizationProblem.optimalValue =
      (sSup ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)) ''
        problem.dualSet) : EReal) := sorry

/-- Companion attainment form of Theorem 3.1.30: the lower-value function attains a maximizer on
the dual set, and its attained value is the least feasible primal objective value. -/
-- Proof sketch: first obtain the bounded-set minimax equality on the owner layer. The properness
-- hypotheses and the slice geometry built into `problem` yield a maximizing parameter `uStar`.
-- Theorem 3.1.29-style saddle-value consequences then identify the attained dual value with the
-- least element of the primal value image `problem '' problem.feasibleSet`.
theorem exists_dual_maximizer_with_primal_minimum_of_bounded_sets
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    ∃ uStar,
      IsMaxOn (fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet))
        problem.dualSet uStar ∧
        IsLeast (problem '' problem.feasibleSet)
          (sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)) := sorry

end

/-! ### Theorem_3_1_31 (from Chap03) -/
noncomputable section

open scoped BigOperators

local notation:max "∂[" Q "] " f:arg "(" x:arg ")" => subdifferentialWithin Q f x

universe u v w

/- Theorem 3.1.31 lies in the chapter's minimax / active-subgradient domain.

Mandatory domain-style sampling before refinement:
- `pointwiseSupremumOn` in `Chap03/Theorem_3_1_8`, the chapter owner for subset-indexed upper
  envelopes on the `WithTop ℝ` side;
- `activePointwiseSupremumOnIndices` in `Chap03/Lemma_3_1_14`, the canonical active-set owner for
  pointwise suprema;
- the source-facing notation `∂[P] f(x)`, together with the bridge
  `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Chap03/Theorem_3_44`, the
  chapter owner surface for real-valued relative subgradients;
- mathlib `IsMinOn` and `StdSimplex`, the canonical owners for minimizers on a set and simplex
  weights.

Best owner abstraction:
- source-facing: the minimax equality theorem below;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `IsMinOn`,
  `∂[P] f(x)`, and `StdSimplex`;
- bridge/view: the real-valued objective `f` on `P`, together with its equality to the
  `WithTop ℝ` owner `pointwiseSupremumOn`.

Primitive data:
- the primal set `P`, parameter set `S`, and kernel `Ψ`;
- the real-valued primal objective `f`;
- the minimizing primal point `xStar`;
- the active slice parameters `u i` and their relative subgradients `g i`;
- the simplex weights and their barycenter in the parameter space.

Derived API:
- the faithful `WithTop ℝ` upper-envelope owner `pointwiseSupremumOn`;
- the faithful active-set owner `activePointwiseSupremumOnIndices`;
- the minimax theorem phrased on the canonical `IsMinOn` / `∂[P] f(x)` owners, with
  real-valued lower slices exposed only under explicit bounded-below hypotheses.

Source/core/bridge triage:
- source-facing: `minimax_eq_of_activeSubgradientRepresentation_at_minimizer`;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `IsMinOn`,
  `∂[P] f(x)`, `StdSimplex`;
- bridge/view: the objective bridge
  `(f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x`.

The previous version installed new real-valued public owners
`sectionSupremumOn` / `sectionInfimumOn` by unconditional `Real.sSup` / `Real.sInf`. That loses
the mathematical semantics on empty or unbounded slices. This refinement therefore deletes those
duplicate owners, reuses the faithful chapter owner `pointwiseSupremumOn` on the upper side,
reuses `activePointwiseSupremumOnIndices` for activity, and exposes real-valued lower slices only
through theorem hypotheses that guarantee the relevant slice infima are genuine. -/

section Minimax

variable {X : Type u} {U : Type v} {ι : Type w}

variable [Fintype ι]

variable [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [AddCommGroup U] [Module ℝ U]

-- Proof sketch: use the constrained subgradient inequality for `gStar` together with the
-- optimality relation `⟪gStar, x - xStar⟫ = 0` on `P`. Rewrite `gStar` as the simplex-weighted sum
-- of the active section subgradients `g i`, combine their section inequalities, and use the
-- barycenter inequality
-- `∑ i, weights.weights i * Ψ(x, u i) ≤ Ψ(x, (Finset.univ).centerMass weights.weights u)` to show
-- that `f xStar ≤ sInf ((fun x ↦ Ψ x uBar) '' P)` for the barycenter parameter
-- `uBar = (Finset.univ).centerMass weights.weights u`. The faithful upper-owner bridge and weak
-- duality then yield the minimax equality `(3.1.78)`.
/-- Theorem 3.1.31: let `f : X → ℝ` be a real-valued objective on `P` whose `WithTop ℝ` lift
agrees with the faithful upper-envelope owner
`pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ))` on `P`. If `xStar` minimizes `f` on `P`,
if some relative subgradient `gStar ∈ ∂_P f(xStar)` satisfying the first-order optimality
relation `⟪gStar, x - xStar⟫ = 0` on `P` admits a simplex representation by active section
subgradients `g i ∈ ∂_P (Ψ(·, u_i))(xStar)`, and if the real lower slices
`x ↦ Ψ(x, u)` are exposed only under bounded-below hypotheses on `P`, then the minimax relation
`(3.1.78)` holds:
`min_{x ∈ P} f(x) = max_{u ∈ S} inf_{x ∈ P} Ψ(x, u)`. -/
theorem minimax_eq_of_activeSubgradientRepresentation_at_minimizer
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {f : X → ℝ}
    {xStar gStar : X}
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hxStar_min : IsMinOn f P xStar)
    (hgStar_mem : gStar ∈ ∂[P] f(xStar))
    (horth : ∀ ⦃x : X⦄, x ∈ P → inner ℝ gStar (x - xStar) = 0)
    (weights : StdSimplex ℝ ι)
    (u : ι → U) (g : ι → X)
    (hu_active :
      ∀ i : ι,
        u i ∈ activePointwiseSupremumOnIndices S
          (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar)
    (hg_mem :
      ∀ i : ι, g i ∈ ∂[P] (fun x ↦ Ψ x (u i)) (xStar))
    (hgStar_repr : gStar = ∑ i, weights.weights i • g i)
    (hΨ_bddBelow :
      ∀ ⦃u : U⦄, u ∈ S → BddBelow ((fun x ↦ Ψ x u) '' P))
    (hu_bar_mem :
      (Finset.univ).centerMass weights.weights u ∈ S)
    (hbar_domination :
      ∀ ⦃x : X⦄, x ∈ P →
        (∑ i, weights.weights i * Ψ x (u i)) ≤
          Ψ x ((Finset.univ).centerMass weights.weights u)) :
    sInf (f '' P) =
      sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := sorry

end Minimax
