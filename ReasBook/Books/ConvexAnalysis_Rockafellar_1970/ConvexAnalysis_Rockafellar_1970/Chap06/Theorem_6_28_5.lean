import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_28_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_28_2

noncomputable section

open scoped BigOperators Pointwise Rockafellar

universe u v

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.28.5 characterizes the subdifferential of the constrained objective
  from Definition 6.28.8 under the Slater condition, first by nonemptiness exactly on the feasible
  set and then by the usual multiplier formula with complementary slackness.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.toWithTopBotOn` on the finite feasible-set owner for the constrained objective and
  `dom∂(·)` / `Function.subdifferentialAt` for the subdifferential domain and subgradients of the
  resulting `WithTopBot ℝ`-valued function.
- `bridge/view`: Proposition 6.28.1 already identifies the subdifferential of the Definition
  6.28.8 constrained objective with the subdifferential of `f₀` plus the finite sum of the
  individual indicator-sublevel subdifferentials, while Proposition 6.28.2 gives the three
  source-facing cases for each individual indicator term. On the multiplier side, the owner
  abstraction is the canonical nonnegative cone `Set.Ici` on the finite function space
  `{i // i ∈ s} → ℝ`, with complementary slackness kept as the additional source predicate at `x`
  rather than repackaged as a second public subtype owner.

Domain-style sampling used here:
- the Definition 6.28.8 owner surface
  `Function.toWithTopBotOn f₀ (convexInequalitySolutionSetOn s (fun _ ↦ .le) f (fun _ ↦ 0))`;
- `dom∂(·)` and `mem_domSubdifferential` from `Chap05.Definition_5_24_1`;
- Proposition 6.28.1's constrained-subdifferential sum decomposition;
- `Function.subdifferentialAt_indicator_sublevel_eq_nonneg_smul_subdifferentialAt_of_eq_zero`;
- `Function.subdifferentialAt_indicator_sublevel_eq_singleton_zero_of_lt_zero`;
- `OrdinaryConvexProgram.multiplierSet`, whose `Set.Ici` owner is the chapter's canonical surface
  for nonnegative multiplier families.

Primitive data vs derived API:
- primitive source data: the finite-valued convex objective `f₀`, a finite subsystem `s`, the
  convex constraints `f i` on that subsystem, the Chapter 21 finite strict feasible-region owner
  on `s`, and the evaluation point `x`;
- primitive multiplier data for part (2): a family `μ : {i // i ∈ s} → ℝ` on the actual finite
  subsystem, together with nonnegativity from the canonical owner `Set.Ici` and the source
  complementary-slackness equalities;
- derived owner statements: membership in the constrained subdifferential domain `dom∂(·)` and
  the multiplier description of the constrained subdifferential set, both stated directly on the
  existing feasible-set owner rather than through local wrapper names.

Layer target: `source-facing`, stated directly on the existing constrained-objective and
subdifferential owners, with the Slater condition routed through the Chapter 21 owner instead of a
parallel subtype-indexed wrapper.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type v}
variable (f₀ : E → ℝ) (s : Finset ι) (f : ι → E → ℝ)

variable (hf₀_convex : ConvexOn ℝ Set.univ f₀)
variable (hf_convex : ∀ i ∈ s, ConvexOn ℝ Set.univ (f i))
variable
    (hstrict :
      (strictConvexInequalitySolutionSetOn s f).Nonempty)

-- Proof sketch: use Proposition 6.28.1 to rewrite the constrained subdifferential as the sum of
-- the lifted objective subdifferential and the individual indicator-sublevel subdifferentials.
-- If some constraint is violated, Proposition 6.28.2 makes the corresponding indicator term
-- empty, so the whole sum is empty. Conversely, if every constraint is satisfied, each indicator
-- term is nonempty (`{0}` in the strict case and a nonnegative scalar hull in the active case),
-- and the finite-valued convex objective has a nonempty subdifferential at `x`.
/-- Theorem 6.28.5 (1): under the Slater condition, the constrained objective from Definition
6.28.8 lies in the Chapter 5 subdifferential-domain owner `dom∂(·)` exactly when `x` lies in the
Chapter 21 feasible-set owner `convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0`, equivalently
when every inequality constraint is satisfied. -/
theorem mem_domSubdifferential_constrainedObjective_iff_feasible
    (x : E) :
    x ∈ dom∂(toWithTopBotOn f₀ (convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0)) ↔
      x ∈ convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0 := sorry

-- Proof sketch: start from the decomposition in Proposition 6.28.1. For each constraint index
-- `i`, apply the three-case formulas from Proposition 6.28.2: if `f i x < 0`, the indicator
-- subdifferential is `{0}`, and if `f i x = 0`, it is the nonnegative scalar hull of
-- `subdifferentialAt (f i).toWithTopBot x`. Feasibility rules out the empty case `0 < f i x`.
-- Expanding the finite Minkowski sum of those individual hulls yields the union over the
-- canonical nonnegative multiplier owner `Set.Ici (0 : {i // i ∈ s} → ℝ)` cut out by the
-- complementary-slackness equalities at `x`.
/-- Theorem 6.28.5 (2): at a point `x` of the Chapter 21 feasible-set owner
`convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0`, the subdifferential of the constrained
objective is the union of the subdifferential sums obtained from the finite complementary
multiplier families on `s` satisfying `μᵢ * fᵢ(x) = 0`, indexed directly by the canonical
nonnegative owner `Set.Ici (0 : {i // i ∈ s} → ℝ)` cut out by those complementary-slackness
equalities. -/
theorem subdifferentialAt_constrainedObjective_eq_iUnion_multiplier_subdifferentialSums_of_feasible
    {x : E} (hfeasible : x ∈ convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0) :
    subdifferentialAt
        (toWithTopBotOn f₀ (convexInequalitySolutionSetOn s (fun _ ↦ .le) f 0)) x =
      ⋃ μ ∈ Set.Ici (0 : {i // i ∈ s} → ℝ) ∩ { μ | ∀ i, μ i * f i.1 x = 0 },
        (subdifferentialAt f₀.toWithTopBot x +
          s.attach.sum (fun i ↦ μ i • subdifferentialAt (f i.1).toWithTopBot x)) := sorry

end

end Function
