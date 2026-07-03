import Mathlib
import Mathlib.Order.WithBotTop
import Mathlib.Tactic.Recall
import Mathlib.Topology.Semicontinuity.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_29_8 (from Chap06) -/
noncomputable section

open scoped Rockafellar
open Function

universe u v w z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.8 compares the generalized convex program attached to a convex
  bifunction `F` with the one attached to its closure `cl F`, asserting preservation of strong
  consistency, the objective closure formula, equality of optimal values, inclusion of optimal
  solutions, local agreement of perturbation functions near `0`, and equality of Kuhn--Tucker
  vectors.
- `core/canonical`: the chapter owners already present are `Bifunction.IsStronglyConsistent`,
  `Bifunction.closure`, `Bifunction.objective`, `Bifunction.optimalValue`,
  `Bifunction.optimalSolutionSet`, `Bifunction.perturbationFunction`,
  `Bifunction.kuhnTuckerVectorSet`, and `Bifunction.IsKuhnTuckerVector`.
- `bridge/view`: Theorem 6.29.4 supplies the closure comparison on slices and perturbation
  functions, while Theorem 6.29.1 supplies the owner-side Kuhn--Tucker interpretation in terms of
  perturbation functions.

Primary mathematical domain:
- convex analysis of generalized convex programs attached to extended-valued bifunctions.

Domain-style sampling used here:
- `Bifunction.IsStronglyConsistent` from `Definition_6_29_21`;
- `Bifunction.closure`, `Bifunction.closure_slice_eq_lowerSemicontinuousHull_of_mem_ri_dom`, and
  `Bifunction.perturbationFunction_closure_eq_perturbationFunction_of_mem_ri_dom` from
  `Theorem_6_29_4`;
- `Bifunction.objective`, `Bifunction.optimalValue`, and `Bifunction.optimalSolutionSet`;
- `Bifunction.kuhnTuckerVectorSet`, `Bifunction.IsKuhnTuckerVector`, and
  `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite`
  from `Theorem_6_29_1`.

Primitive data vs derived API:
- primitive input data: a convex bifunction `F : U → X → WithBotTop 𝕜`;
- primitive hypotheses: convexity of `Function.uncurry F`, together with strong consistency for
  the clauses centered at the base perturbation `u = 0`;
- derived API: the closure-program consequences listed in the corollary.

Layer target: `source-facing`, split into atomic owner-level consequences rather than packaged
as one conjunction or wrapper structure.
-/

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [FiniteDimensional 𝕜 (U × X)]

variable {F : U → X → WithBotTop 𝕜}

section ClosureProgram

local notation "p" => perturbationFunction F
local notation "pcl" => perturbationFunction (cl F)

-- Proof sketch: combine the slice/domain comparison theorems of Theorem 6.29.4 with the source
-- characterization of strong consistency `0 ∈ ri[𝕜](dom F)` to show that `0` also lies in the
-- relative interior of the domain of `cl F`.
/-- Corollary 6.29.8 (1): if the generalized convex program attached to a convex bifunction `F`
is strongly consistent, then the generalized convex program attached to `cl F` is strongly
consistent as well. -/
theorem isStronglyConsistent_closure_of_isStronglyConsistent
    (hF_convex : convᵇ[𝕜](F)) (hF_strong : IsStronglyConsistent 𝕜 F) :
    IsStronglyConsistent 𝕜 (cl F) := sorry

-- Proof sketch: apply Theorem 6.29.4 to the slice `u = 0`; strong consistency gives
-- `0 ∈ ri[𝕜](dom F)`, so the zero slice of `cl F` is the lower-semicontinuous hull of the zero
-- slice of `F`.
/-- Corollary 6.29.8 (2): the objective function of the generalized convex program attached to
`cl F` is the closure of the objective function of the generalized convex program attached to
`F`. -/
theorem objective_closure_eq_closure_objective_of_isStronglyConsistent
    (hF_convex : convᵇ[𝕜](F)) (hF_strong : IsStronglyConsistent 𝕜 F) :
    (cl F)₀ = cl((F)₀) := sorry

-- Proof sketch: rewrite both optimal values as the infimum of the corresponding zero-slice
-- objectives, then use clause `(2)` to identify the objective of `cl F` with `cl((F)₀)`, whose
-- infimum agrees with the infimum of `(F)₀`.
/-- Corollary 6.29.8 (3): the generalized convex programs attached to `F` and to `cl F` have the
same optimal value. -/
theorem optimalValue_closure_eq_optimalValue_of_isStronglyConsistent
    (hF_convex : convᵇ[𝕜](F)) (hF_strong : IsStronglyConsistent 𝕜 F) :
    optimalValue (cl F) = optimalValue F := sorry

-- Proof sketch: an optimal solution of `F` is feasible and attains `optimalValue F`. Use clause
-- `(2)` for the zero-slice objective, clause `(3)` for the optimal value, and the pointwise
-- inequality `cl F ≤ F` on feasible slices to show that the same point is feasible and optimal
-- for `cl F`.
/-- Corollary 6.29.8 (4): every optimal solution of the generalized convex program attached to
`F` is also an optimal solution of the generalized convex program attached to `cl F`. -/
theorem optimalSolutionSet_subset_optimalSolutionSet_closure_of_isStronglyConsistent
    (hF_convex : convᵇ[𝕜](F)) (hF_strong : IsStronglyConsistent 𝕜 F) :
    optimalSolutionSet F ⊆ optimalSolutionSet (cl F) := sorry

-- Proof sketch: strong consistency is exactly `(0 : U) ∈ ri[𝕜](dom F)`. Theorem 6.29.4 gives
-- pointwise equality of `perturbationFunction (cl F)` and `perturbationFunction F` at every
-- parameter of `ri[𝕜](dom F)`.
/-- Corollary 6.29.8 (5), canonical relative-domain form: for a convex bifunction `F`,
the perturbation functions of the generalized convex programs attached to `F` and `cl F`
agree on the relative interior `ri[𝕜](dom F)`. -/
theorem perturbationFunction_closure_eq_perturbationFunction_on_ri_dom
    (hF_convex : convᵇ[𝕜](F)) :
    Set.EqOn pcl p (ri[𝕜](dom F)) := by
  intro u hu
  exact perturbationFunction_closure_eq_perturbationFunction_of_mem_ri_dom hF_convex hu

-- Proof sketch: specialize the canonical relative-domain equality to the neighborhood filter
-- `nhdsWithin (0 : U) (ri[𝕜](dom F))`.
/-- Corollary 6.29.8 (5), source-facing local form: the perturbation functions of the generalized
convex programs attached to `F` and `cl F` agree locally near the base perturbation `0`,
recorded as eventual equality on `nhdsWithin (0 : U) (ri[𝕜](dom F))`. -/
theorem perturbationFunction_closure_eq_perturbationFunction_near_zero
    (hF_convex : convᵇ[𝕜](F)) :
    pcl =ᶠ[nhdsWithin (0 : U) (ri[𝕜](dom F))] p := by
  exact eventuallyEq_nhdsWithin_of_eqOn
    (perturbationFunction_closure_eq_perturbationFunction_on_ri_dom
      (F := F) hF_convex)

end ClosureProgram

section KuhnTucker

variable {UStar : Type z}
variable [HasPairing U UStar 𝕜]

/-- Corollary 6.29.8 (6), pointwise bridge form: a dual vector is Kuhn--Tucker for `cl F`
exactly when it is Kuhn--Tucker for `F`. -/
theorem isKuhnTuckerVector_closure_iff_of_isStronglyConsistent
    (hF_convex : convᵇ[𝕜](F)) (hF_strong : IsStronglyConsistent 𝕜 F)
    (uStar : UStar) :
    IsKuhnTuckerVector (cl F) uStar ↔ IsKuhnTuckerVector F uStar := by
  sorry

-- Proof sketch: extensionality over the ambient dual space reduces set equality to the
-- pointwise bridge theorem above.
/-- Corollary 6.29.8 (6), canonical owner form: the generalized convex programs attached to `F`
and `cl F` have the same Kuhn--Tucker vector set. -/
theorem kuhnTuckerVectorSet_closure_eq_of_isStronglyConsistent
    (hF_convex : convᵇ[𝕜](F)) (hF_strong : IsStronglyConsistent 𝕜 F) :
    (KT(cl F) : Set UStar) = KT(F) := by
  ext uStar
  simpa [mem_kuhnTuckerVectorSet] using
    (isKuhnTuckerVector_closure_iff_of_isStronglyConsistent
      (F := F) hF_convex hF_strong uStar)

end KuhnTucker

end Bifunction

/-! ### Definition_6_29_8 (from Chap06) -/
universe u v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.8 introduces the effective domain of a bifunction `F` as the
  set of parameters `u` for which the slice `F u` is not identically `⊤`.
- `core/canonical`: the generalized program attached to `F` already owns the perturbation
  function `perturbationFunction F` from Definition 6.29.1, so its parameter domain should bridge
  to the chapter owner `dom(perturbationFunction F)`. At the slice level, Chapter 1 already fixes
  one-variable effective domains through the owner `dom(·)`.
- `bridge/view`: the defining slice condition is the nonemptiness of `dom(F u)`, and on the
  complete-lattice codomain layer this is exactly membership in `dom(perturbationFunction F)`. The
  source phrase “`F u` is not identically `+∞`” is the derived value-level criterion
  `∃ x, F u x < ⊤`.

Domain-style sampling used here:
- `effectiveDomain`, `dom(·)`, and `mem_effectiveDomain` from
  `ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4`;
- `perturbationFunction` and `perturbationFunction_apply` from
  `ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1`;
- mathlib's canonical indexed-infimum bridge `iInf_lt_top`;
- `Set.Nonempty` as the canonical owner for nonempty slice effective domains.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β`;
- source-facing owner introduced here: `Bifunction.dom F`;
- canonical defining owner expression: `{u | (dom(F u)).Nonempty}`;
- core generalized-program owner under `[CompleteLattice β]`:
  `dom(perturbationFunction F)`;
- derived API: the nonempty-slice-domain membership test, the direct owner bridge to
  `dom(perturbationFunction F)`, the corresponding interior / relative-interior transport, and the
  source-facing existence criterion `∃ x, F u x < ⊤`.

Notation decision:
- the source-facing owner is exported through the scoped textbook surface `dom F`, so immediate
  downstream files can use the bifunction-domain notation without relying on namespace-local name
  resolution; the slice domains continue to use the Chapter 1 notation `dom(F u)`.

Layer target: `source-facing`, built directly from the existing one-variable effective-domain owner
and explicitly bridged to the chapter's core generalized-program owner
`dom(perturbationFunction F)`.
-/

/-- Definition 6.29.8: the domain of a bifunction `F` is the set of parameters `u` for which the
slice `F u` has nonempty effective domain, equivalently is not identically `⊤`. -/
def dom (F : U → X → β) : Set U :=
  {u | (dom(F u)).Nonempty}

/- Rockafellar's source-facing notation for the effective domain of a bifunction. -/
scoped[Rockafellar] prefix:max "dom " => Bifunction.dom

/-- A parameter lies in the domain of a bifunction exactly when the effective domain of the
corresponding slice is nonempty. -/
@[simp] theorem mem_dom {F : U → X → β} {u : U} :
    u ∈ dom F ↔ (dom(F u)).Nonempty :=
  Iff.rfl

/-- A parameter lies in the domain of a bifunction exactly when some value of the
corresponding slice is strictly below `⊤`. -/
@[simp] theorem mem_dom_iff_exists {F : U → X → β} {u : U} :
    u ∈ dom F ↔ ∃ x : X, F u x < ⊤ := by
  rw [mem_dom]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩

section

variable [Zero U]
variable {β : Type w} [Top β] [LT β]

/-- The generalized convex program attached to `F` is consistent exactly when the
zero perturbation belongs to the source-facing bifunction domain. -/
@[simp] theorem isConsistent_iff_zero_mem_dom (F : U → X → β) :
    IsConsistent F ↔ (0 : U) ∈ dom F := by
  rw [isConsistent_iff_exists_lt_top, mem_dom_iff_exists]

end

end

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [CompleteLattice β]

/-- A parameter lies in the effective domain of the perturbation function exactly when some slice
value of the bifunction is strictly below `⊤`. -/
@[simp] theorem mem_dom_perturbationFunction_iff_exists {F : U → X → β} {u : U} :
    u ∈ dom(perturbationFunction F) ↔ ∃ x : X, F u x < ⊤ := by
  rw [_root_.mem_effectiveDomain, perturbationFunction_apply]
  exact (iInf_lt_top : (⨅ x : X, F u x) < ⊤ ↔ ∃ x : X, F u x < ⊤)

/-- Membership in the effective domain of the perturbation function is exactly membership in the
source-facing bifunction domain. -/
@[simp] theorem mem_dom_perturbationFunction_iff_mem_dom
    {F : U → X → β} {u : U} :
    u ∈ dom(perturbationFunction F) ↔ u ∈ dom F := by
  rw [mem_dom_perturbationFunction_iff_exists, mem_dom_iff_exists]

/-- The generalized-program domain `dom(perturbationFunction F)` is exactly the source-facing
bifunction domain. -/
@[simp] theorem dom_perturbationFunction_eq_dom (F : U → X → β) :
    dom(perturbationFunction F) = dom F := by
  ext u
  simpa using mem_dom_perturbationFunction_iff_mem_dom

section

variable {𝕜 : Type z} {V : Type*} [Ring 𝕜]
variable [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace U] [AddTorsor V U]

/-- Transporting the source-facing bifunction domain to the chapter's canonical
generalized-program owner commutes with relative interior, on the theorem surface
`ri[𝕜](dom F)`. -/
theorem ri_dom_eq_riDom_perturbationFunction
    (F : U → X → β) :
    ri[𝕜](dom F) = riDom[𝕜](perturbationFunction F) := by
  rw [riDom_eq_intrinsicInterior_dom, dom_perturbationFunction_eq_dom]

/-- Relative-interior membership in the source-facing bifunction domain is exactly
relative-interior membership in the canonical generalized-program domain. -/
theorem mem_ri_dom_iff_mem_riDom_perturbationFunction
    {F : U → X → β} {u : U} :
    u ∈ ri[𝕜](dom F) ↔
      u ∈ riDom[𝕜](perturbationFunction F) := by
  rw [ri_dom_eq_riDom_perturbationFunction]

/-- Canonicalization bridge: relative interior of `dom(perturbationFunction F)` is rewritten to
the source-facing owner `ri[𝕜](dom F)`. -/
@[simp] theorem riDom_perturbationFunction_eq_ri_dom
    (F : U → X → β) :
    riDom[𝕜](perturbationFunction F) = ri[𝕜](dom F) := by
  exact (ri_dom_eq_riDom_perturbationFunction (𝕜 := 𝕜) (F := F)).symm

/-- Canonicalization bridge: relative-interior membership in
`dom(perturbationFunction F)` rewrites to membership in `ri[𝕜](dom F)`. -/
@[simp] theorem mem_riDom_perturbationFunction_iff_mem_ri_dom
    {F : U → X → β} {u : U} :
    u ∈ riDom[𝕜](perturbationFunction F) ↔ u ∈ ri[𝕜](dom F) := by
  rw [riDom_perturbationFunction_eq_ri_dom]

end

section

variable [TopologicalSpace U]

/-- Transporting the source-facing bifunction domain to the chapter's canonical
generalized-program owner commutes with ordinary interior. -/
theorem interior_dom_eq_interior_dom_perturbationFunction
    (F : U → X → β) :
    interior (dom F) = interior (dom(perturbationFunction F)) := by
  rw [dom_perturbationFunction_eq_dom]

/-- Interior membership in the source-facing bifunction domain is exactly interior
membership in the canonical generalized-program domain. -/
theorem mem_interior_dom_iff_mem_interior_dom_perturbationFunction
    {F : U → X → β} {u : U} :
    u ∈ interior (dom F) ↔
      u ∈ interior (dom(perturbationFunction F)) := by
  rw [interior_dom_eq_interior_dom_perturbationFunction]

/-- Canonicalization bridge: interior of `dom(perturbationFunction F)` is rewritten to the
source-facing owner `interior (dom F)`. -/
@[simp] theorem interior_dom_perturbationFunction_eq_interior_dom
    (F : U → X → β) :
    interior (dom(perturbationFunction F)) = interior (dom F) := by
  exact (interior_dom_eq_interior_dom_perturbationFunction (F := F)).symm

/-- Canonicalization bridge: interior membership in `dom(perturbationFunction F)` rewrites to
interior membership in `dom F`. -/
@[simp] theorem mem_interior_dom_perturbationFunction_iff_mem_interior_dom
    {F : U → X → β} {u : U} :
    u ∈ interior (dom(perturbationFunction F)) ↔ u ∈ interior (dom F) := by
  rw [interior_dom_perturbationFunction_eq_interior_dom]

end

end

end Bifunction

/-! ### Lemma_6_29_8 (from Chap06) -/
noncomputable section

universe u v w z

namespace Bifunction

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.8 says that, when the generalized convex program attached to `F`
  is consistent, the ambient set of optimal solutions is exactly the minimum set of `F₀`, and
  this set is a possibly empty convex subset of the feasible set.
- `core/canonical`: the existing owners are `Bifunction.objective`, the Chapter 6 consistency
  owner `Bifunction.IsConsistent`, the Chapter 6 feasible-set owner `Bifunction.feasibleSet`, and
  the Chapter 6 minimum-set owner `minimumSet`.
- `bridge/view`: the source set of optimal solutions is owned here as `optimalSolutionSet F`,
  then related to the canonical owner `minimumSet (F)₀`.

Domain-style sampling used here:
- `Bifunction.objective`;
- `Bifunction.IsConsistent` and `isConsistent_iff_feasibleSet_nonempty`;
- `Bifunction.feasibleSet`;
- `dom(·)` through the feasible-set owner;
- `minimumSet`, `minimumSet_subset_dom_of_nonempty_dom`, and `minimumSet_isConvex`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β`;
- source-facing optimal-solution owner: `optimalSolutionSet F`, expressed intrinsically as
  feasible minimizers of `(F)₀`;
- canonical comparison owner: `minimumSet (F)₀`;
- primitive feasibility hypothesis: `IsConsistent F`, equivalently `(feasibleSet F).Nonempty`;
- derived geometry: convexity of that minimum set and its containment in the feasible set.

Layer target:
- clause `(1)` is `source-facing`, stated as the set equality between `optimalSolutionSet F` and
  the canonical minimum set;
- clauses `(2)` and `(3)` stay on the source-facing owner `optimalSolutionSet F`, proved through
  the canonical bridge to `minimumSet (F)₀`.
-/

section OptimalSolutions

variable {U : Type u} {X : Type v} {β : Type w}
variable [Preorder β] [Top β] [Zero U]

/-- The ambient set of optimal solutions of the generalized convex program attached to `F`. -/
def optimalSolutionSet (F : U → X → β) : Set X :=
  feasibleSet F ∩ minimumSet (F)₀

/-- Membership in `optimalSolutionSet F` is feasible-membership together with minimizer
membership for `F₀`. -/
@[simp] theorem mem_optimalSolutionSet {F : U → X → β} {x : X} :
    x ∈ optimalSolutionSet F ↔ x ∈ feasibleSet F ∧ x ∈ minimumSet (F)₀ :=
  Iff.rfl

/-- If the generalized convex program attached to `F` is inconsistent, then it has no optimal
solutions. -/
theorem optimalSolutionSet_eq_empty_of_not_consistent
    {F : U → X → β}
    (hF_inconsistent : ¬ IsConsistent F) :
    optimalSolutionSet F = ∅ := by
  ext x
  constructor
  · intro hx
    exfalso
    exact hF_inconsistent <| (isConsistent_iff_feasibleSet_nonempty F).2 ⟨x, hx.1⟩
  · intro hx
    cases hx

end OptimalSolutions

section OptimalSolutionsConsistent

variable {U : Type u} {X : Type v} {β : Type w}
variable [Preorder β] [Top β] [Zero U]

-- Proof sketch: by definition `optimalSolutionSet F = feasibleSet F ∩ minimumSet (F)₀`.
-- Under consistency, `feasibleSet F = dom((F)₀)` is nonempty, so every minimizer of `(F)₀` is
-- finite via `minimumSet_subset_dom_of_nonempty_dom`, hence feasible.
/-- Lemma 6.29.8 (1): when the generalized convex program attached to `F` is consistent, the
ambient set of optimal solutions is exactly the minimum set of `F₀`. -/
theorem optimalSolutionSet_eq_minimumSet_of_consistent
    {F : U → X → β}
    (hF_consistent : IsConsistent F) :
    optimalSolutionSet F = minimumSet (F)₀ := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hfeasible_nonempty : (feasibleSet F).Nonempty :=
      (isConsistent_iff_feasibleSet_nonempty F).1 hF_consistent
    have hobjective_dom_nonempty : dom((F)₀).Nonempty := by
      simpa [feasibleSet] using hfeasible_nonempty
    have hx_feasible_dom : x ∈ dom((F)₀) :=
      (minimumSet_subset_dom_of_nonempty_dom (f := (F)₀) hobjective_dom_nonempty) hx
    have hx_feasible : x ∈ feasibleSet F := by
      simpa [feasibleSet] using hx_feasible_dom
    exact ⟨hx_feasible, hx⟩

end OptimalSolutionsConsistent

section Convexity

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMulZeroClass 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [ConditionallyCompleteLattice α]
variable [AddCommMonoid α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

-- Proof sketch: apply the owner method `Function.IsConvex.convex_minimumSet` to the objective
-- function `objective F`. Its convexity is supplied by the existing slice theorem
-- `Function.IsConvex.objective`, which specializes convexity of `Function.uncurry F` to the zero
-- slice `F₀`. If `F` is inconsistent, then `optimalSolutionSet F = ∅`.
/-- Lemma 6.29.8 (2): if the graph function of `F` is convex, then the optimal-solution set is
convex. -/
theorem optimalSolutionSet_isConvex_of_uncurry_isConvex
    {F : U → X → WithBotTop α}
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) :
    Convex 𝕜 (optimalSolutionSet F) := by
  by_cases hF_consistent : IsConsistent F
  · rw [optimalSolutionSet_eq_minimumSet_of_consistent hF_consistent]
    exact hF_convex.objective.convex_minimumSet
  · rw [optimalSolutionSet_eq_empty_of_not_consistent hF_consistent]
    simpa using (convex_empty : Convex 𝕜 (∅ : Set X))

end Convexity

section Feasibility

variable {U : Type u} {X : Type v} {β : Type w}
variable [Preorder β] [Top β] [Zero U]

-- Proof sketch: membership in the source-facing owner `optimalSolutionSet F` already includes
-- feasibility as one of its two defining clauses.
/-- Lemma 6.29.8 (3): every optimal solution is feasible. -/
theorem optimalSolutionSet_subset_feasibleSet
    {F : U → X → β} :
    optimalSolutionSet F ⊆ feasibleSet F := by
  intro x hx
  exact hx.1

end Feasibility

end Bifunction

/-! ### Definition_6_29_9 (from Chap06) -/
noncomputable section

universe u v r

namespace Bifunction

section

variable {𝕜 : Type r} {U : Type u} {X : Type v}
variable [Zero 𝕜]
variable (𝕜)

attribute [local instance] Classical.propDecidable

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.9 attaches to a linear transformation `A` the bifunction whose
  `u`-slice is the indicator of the singleton `{A u}`.
- `core/canonical`: this is the singleton specialization of the Chapter 6 set-valued-map indicator
  owner `δᵇ[𝕜](S)` from Definition 6.29.3, itself built from the Chapter 1 indicator
  `δ[𝕜](x | C)`.
- `bridge/view`: the textbook linear-map case is the specialization `graphIndicator 𝕜 A`, together
  with its pointwise `0`/`+∞` singleton formula.

Domain-style sampling used here:
- `indicator` and the notation `δ[𝕜](x | C)`;
- set-valued-map indicator notation `δᵇ[𝕜](S)`;
- `indicator_def`;
- `indicator_of_mem`;
- `indicator_of_notMem`.

Layer target: `core/canonical`, with `graphIndicator` exposed as the singleton-fiber view of the
existing set-valued-map indicator owner.
-/

/-- Definition 6.29.9, owner form: the singleton-graph indicator attached to a map `T`; its
`u`-slice is the Chapter 1 indicator of the singleton `{T u}`. The source-facing linear-map case
is `graphIndicator 𝕜 A`. -/
def graphIndicator (T : U → X) : U → X → WithBotTop 𝕜 :=
  δᵇ[𝕜](fun u ↦ ({T u} : Set X))

/-- `graphIndicator` is exactly the set-valued-map indicator owner specialized to singleton
fibers. -/
@[simp] theorem graphIndicator_eq_indicatorBifunction_singleton (T : U → X) :
    graphIndicator 𝕜 T = δᵇ[𝕜](fun u ↦ ({T u} : Set X)) :=
  rfl

/-- Sign-dual singleton-graph indicator attached to a map `T`; its `u`-slice is the negative of
the Chapter 1 indicator of the singleton `{T u}`. This is the canonical owner used for the
concave graph-indicator branch in later adjoint formulas. -/
def graphConcaveIndicator [Neg 𝕜] (T : U → X) : U → X → WithBotTop 𝕜 :=
  -graphIndicator 𝕜 T

/-- The concave singleton-graph owner is the pointwise negation of the convex owner. -/
@[simp] theorem graphConcaveIndicator_eq_neg_graphIndicator [Neg 𝕜]
    (T : U → X) :
    graphConcaveIndicator 𝕜 T = -graphIndicator 𝕜 T :=
  rfl

/-- Each slice of the singleton-graph indicator is the Chapter 1 indicator of the singleton image
`{T u}`. -/
theorem graphIndicator_slice
    (T : U → X) (u : U) :
    graphIndicator 𝕜 T u = (δ[𝕜](· | ({T u} : Set X))) := by
  funext x
  simp [graphIndicator]

/-- The singleton-graph indicator takes the value `0` at `T u` and `+∞` away from `T u`. In
particular, for a linear map `A`, this is the pointwise formula for `graphIndicator 𝕜 A`. -/
@[simp] theorem graphIndicator_cases
    (T : U → X) (u : U) (x : X) :
    graphIndicator 𝕜 T u x =
      if x = T u then (0 : WithBotTop 𝕜) else ⊤ := by
  simp [graphIndicator, indicator_def]

/-- Each slice of the singleton-graph concave indicator is the negative of the Chapter 1
indicator of the singleton image `{T u}`. -/
theorem graphConcaveIndicator_slice [Neg 𝕜]
    (T : U → X) (u : U) :
    graphConcaveIndicator 𝕜 T u = (-(δ[𝕜](· | ({T u} : Set X)))) := by
  rfl

/-- Pointwise branch formula for the singleton-graph concave indicator: it is `-0` at `T u` and
`-⊤ = ⊥` away from `T u`. -/
@[simp] theorem graphConcaveIndicator_cases [Neg 𝕜]
    (T : U → X) (u : U) (x : X) :
    graphConcaveIndicator 𝕜 T u x =
      if x = T u then (-(0 : WithBotTop 𝕜)) else ⊥ := by
  by_cases hx : x = T u
  · simp [graphConcaveIndicator, hx]
  · simp [graphConcaveIndicator, hx]

/-- At the singleton image point `T u`, the concave graph indicator equals `-0`. -/
@[simp] theorem graphConcaveIndicator_eq_neg_zero [Neg 𝕜]
    (T : U → X) (u : U) :
    graphConcaveIndicator 𝕜 T u (T u) = (-(0 : WithBotTop 𝕜)) := by
  simp [graphConcaveIndicator_cases]

/-- Away from `T u`, the concave graph indicator equals `⊥`. -/
@[simp] theorem graphConcaveIndicator_eq_bot_of_ne [Neg 𝕜]
    (T : U → X) (u : U) {x : X} (hx : x ≠ T u) :
    graphConcaveIndicator 𝕜 T u x = (⊥ : WithBotTop 𝕜) := by
  simp [graphConcaveIndicator_cases, hx]

end

end Bifunction

/-! ### Lemma_6_29_9 (from Chap06) -/
noncomputable section

universe u v w

open scoped Rockafellar

namespace OrdinaryConvexProgram

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Ring 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup β] [PartialOrder β] [Module 𝕜 β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.9 is the Slater-style characterization of strong consistency for an
  ordinary convex program.
- `core/canonical`: the Chapter 6 owner for strong consistency is
  `Bifunction.IsStronglyConsistent 𝕜`, applied here to the associated perturbation owner
  `P.perturbedProblem`.
- `bridge/view`: the source witness is still a point of `ri[𝕜](P.constraintSet)` with strict
  inequalities and exact equalities, written intrinsically on the program's inequality/equality
  index owners.

Domain-style sampling used here:
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `Bifunction.IsStronglyConsistent` from `Definition_6_29_10`;
- `Bifunction.dom` / `Bifunction.mem_dom_iff_exists` from `Definition_6_29_8`;
- the chapter notation `ri[𝕜](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive source data: the program `P`;
- canonical owner-side predicate: strong consistency of `P.perturbedProblem`;
- source-facing witness owner: `P.HasRiStrictFeasiblePoint`;
- derived bridge view: the corresponding explicit existential witness on `P.constraintSet`.

Layer target: `source-facing`, stated on the existing owners `P.perturbedProblem`, `ri[𝕜](·)`,
and the ordinary-program owner `P.HasRiStrictFeasiblePoint`.
-/

-- Proof sketch: this is the definitional source-facing owner packaging of the relative-interior
-- strict feasible witness.
/-- Source-facing owner for the relative-interior strict-feasibility witness of `P`: a point of
`P.constraintSet` that lies in `ri[𝕜](P.constraintSet)`, satisfies every inequality strictly, and
satisfies every equality exactly. -/
def HasRiStrictFeasiblePoint : Prop :=
  ∃ x : P.constraintSet,
    (x : E) ∈ ri[𝕜](P.constraintSet) ∧
      (∀ i, P.inequality i x < 0) ∧
      (∀ j, P.equality j x = 0)

-- Proof sketch: expand the witness owner definition.
/-- Bridge expansion: `P.HasRiStrictFeasiblePoint` is exactly the explicit relative-interior
strict-feasible witness surface. -/
theorem hasRiStrictFeasiblePoint_iff :
    P.HasRiStrictFeasiblePoint ↔
      ∃ x : P.constraintSet,
        (x : E) ∈ ri[𝕜](P.constraintSet) ∧
          (∀ i, P.inequality i x < 0) ∧
          (∀ j, P.equality j x = 0) :=
  Iff.rfl

-- Proof sketch: unfold `Bifunction.IsStronglyConsistent` for `P.perturbedProblem`. Via
-- `Bifunction.dom` and `P.mem_perturbedFeasibleSet`, a perturbation parameter lies in the domain
-- exactly when some point of `P.constraintSet` satisfies the corresponding inequality and
-- equality bounds. Specializing the relative-interior condition at the zero perturbation yields
-- precisely a point of `P.constraintSet` lying in `ri[𝕜](P.constraintSet)` with strict
-- inequalities and exact equalities.
variable [TopologicalSpace β]

/-- Lemma 6.29.9, owner form: the perturbation problem attached to an ordinary convex program is
strongly consistent exactly when `P` has a relative-interior strict feasible point. -/
theorem stronglyConsistent_iff_hasRiStrictFeasiblePoint :
    Bifunction.IsStronglyConsistent 𝕜 P.perturbedProblem ↔
      P.HasRiStrictFeasiblePoint := by
  -- The source-facing bridge proof is deferred in this canonicalization pass; this item now
  -- exposes the intended owner-level theorem surface directly.
  sorry

-- Proof sketch: unfold `P.HasRiStrictFeasiblePoint`.
/-- Lemma 6.29.9, explicit witness form: strong consistency is equivalent to existence of a
relative-interior strict feasible point of `P.constraintSet`. -/
theorem stronglyConsistent_iff_exists_ri_strict_feasible_point :
    Bifunction.IsStronglyConsistent 𝕜 P.perturbedProblem ↔
      ∃ x : P.constraintSet,
        (x : E) ∈ ri[𝕜](P.constraintSet) ∧
          (∀ i, P.inequality i x < 0) ∧
          (∀ j, P.equality j x = 0) := by
  simpa [HasRiStrictFeasiblePoint] using
    (stronglyConsistent_iff_hasRiStrictFeasiblePoint (𝕜 := 𝕜) (P := P))

end

end OrdinaryConvexProgram

/-! ### Definition_6_29_10 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section

variable {U : Type u} {V : Type*} {X : Type v} {β : Type z} (𝕜 : Type w)
variable [Top β] [LT β]
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Zero U] [TopologicalSpace U] [AddTorsor V U]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.10 introduces the stronger consistency notions for the
  generalized convex program associated with a bifunction `F`, namely strong consistency and
  strict consistency.
- `core/canonical`: the source-facing domain owner `dom F` from Definition 6.29.8 and the
  intrinsic/ambient topological owners `intrinsicInterior`, `interior`, and `nhds`.
- `bridge/view`: on the complete-lattice codomain layer, `dom F = dom(perturbationFunction F)`, so
  strong consistency is equivalent to `0 ∈ riDom[𝕜](perturbationFunction F)` and strict
  consistency is equivalent to `0 ∈ interior (dom(perturbationFunction F))`.

Project sampling used here:
- `Bifunction.dom` from `ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8`;
- `Bifunction.mem_dom_perturbationFunction_iff_mem_dom` and
  `Bifunction.mem_ri_dom_iff_mem_riDom_perturbationFunction` from the same file.

Mathlib sampling used here:
- `intrinsicInterior` from `Mathlib/Analysis/Convex/Intrinsic.lean`;
- `intrinsicInterior_subset` from the same file;
- `interior_subset_intrinsicInterior` from the same file.

- Primitive data vs derived API:
- primitive owner data: the source-facing bifunction domain `dom F`;
- source-facing predicates: `IsStronglyConsistent 𝕜 F` and `IsStrictlyConsistent F`;
- derived API: the bridges to the perturbation-domain formulations, the canonical implication
  `strict ⇒ strong`, the interior/open-set bridge for strict consistency, then the implications to
  ordinary consistency.

Layer target: `source-facing`, built directly on the existing owner `dom F` rather than via the
derived perturbation-function domain.
-/

/-- Definition 6.29.10: a generalized convex program is strongly consistent when the base
perturbation `0` lies in the relative interior of the bifunction domain. -/
def IsStronglyConsistent (F : U → X → β) : Prop :=
  0 ∈ ri[𝕜](dom F)

@[simp] theorem isStronglyConsistent_iff (F : U → X → β) :
    IsStronglyConsistent 𝕜 F ↔ 0 ∈ ri[𝕜](dom F) :=
  Iff.rfl

end

section

variable {U : Type u} {V : Type*} {X : Type v} {β : Type z} (𝕜 : Type w)
variable [Top β] [LT β]
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Zero U] [TopologicalSpace U] [AddTorsor V U]

/-- Strong consistency implies ordinary consistency. -/
theorem IsStronglyConsistent.isConsistent {F : U → X → β}
    (hF : IsStronglyConsistent 𝕜 F) :
    IsConsistent F := by
  exact (isConsistent_iff_zero_mem_dom F).2
    (intrinsicInterior_subset hF)

end

section

variable {U : Type u} {V : Type*} {X : Type v} {β : Type z} (𝕜 : Type w)
variable [CompleteLattice β]
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Zero U] [TopologicalSpace U] [AddTorsor V U]

/-- On the complete-lattice codomain layer, strong consistency is equivalent to membership of
`0` in the relative interior of `dom(perturbationFunction F)`. -/
@[simp] theorem isStronglyConsistent_iff_mem_riDom_perturbationFunction
    (F : U → X → β) :
    IsStronglyConsistent 𝕜 F ↔ 0 ∈ riDom[𝕜](perturbationFunction F) := by
  have hzero :
      (0 : U) ∈ ri[𝕜](dom F) ↔
        0 ∈ riDom[𝕜](perturbationFunction F) :=
    mem_ri_dom_iff_mem_riDom_perturbationFunction
  simpa [isStronglyConsistent_iff] using hzero

end

section

variable {U : Type u} {X : Type v} {β : Type z}
variable [Top β] [LT β]
variable [Zero U] [TopologicalSpace U]

/-- Definition 6.29.10: a generalized convex program is strictly consistent when `0` admits an
open neighborhood contained in the bifunction domain, equivalently when `0` lies in the interior
of that domain. The canonical owner is neighborhood-membership of `dom F` at `0`, with interior
membership as a bridge theorem. -/
def IsStrictlyConsistent (F : U → X → β) : Prop :=
  dom F ∈ nhds (0 : U)

/-- Strict consistency is exactly neighborhood-membership of the bifunction domain at `0`. -/
theorem isStrictlyConsistent_iff_mem_nhds (F : U → X → β) :
    IsStrictlyConsistent F ↔ dom F ∈ nhds (0 : U) :=
  Iff.rfl

theorem isStrictlyConsistent_iff_exists_open_zero_subset_dom (F : U → X → β) :
    IsStrictlyConsistent F ↔ ∃ C : Set U, IsOpen C ∧ (0 : U) ∈ C ∧ C ⊆ dom F :=
  by
    constructor
    · intro hnhds
      have hzeroInterior : (0 : U) ∈ interior (dom F) :=
        (mem_interior_iff_mem_nhds).2 hnhds
      exact ⟨interior (dom F), isOpen_interior, hzeroInterior, interior_subset⟩
    · rintro ⟨C, hC_open, hC_zero, hC_sub⟩
      exact Filter.mem_of_superset (IsOpen.mem_nhds hC_open hC_zero) hC_sub

@[simp] theorem isStrictlyConsistent_iff (F : U → X → β) :
    IsStrictlyConsistent F ↔ 0 ∈ interior (dom F) :=
  (mem_interior_iff_mem_nhds : (0 : U) ∈ interior (dom F) ↔ dom F ∈ nhds (0 : U)).symm

end

section

variable {U : Type u} {X : Type v} {β : Type z}
variable [Top β] [LT β]
variable [Zero U] [TopologicalSpace U]

/-- Strict consistency implies ordinary consistency. -/
theorem IsStrictlyConsistent.isConsistent {F : U → X → β}
    (hF : IsStrictlyConsistent F) :
    IsConsistent F := by
  have hzero : (0 : U) ∈ interior (dom F) :=
    (isStrictlyConsistent_iff (F := F)).1 hF
  exact (isConsistent_iff_zero_mem_dom F).2
    (interior_subset hzero)

end

section

variable {U : Type u} {X : Type v} {β : Type z}
variable [CompleteLattice β]
variable [Zero U] [TopologicalSpace U]

/-- On the complete-lattice codomain layer, strict consistency is equivalent to membership of `0`
in the interior of `dom(perturbationFunction F)`. -/
@[simp] theorem isStrictlyConsistent_iff_mem_interior_dom_perturbationFunction
    (F : U → X → β) :
    IsStrictlyConsistent F ↔ 0 ∈ interior (dom(perturbationFunction F)) := by
  simpa [isStrictlyConsistent_iff] using
    (mem_interior_dom_iff_mem_interior_dom_perturbationFunction
      (F := F) (u := (0 : U)))

end

section

variable {𝕜 : Type w} {U : Type u} {V : Type*} {X : Type v} {β : Type z}
variable [Top β] [LT β]
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable [Zero U] [TopologicalSpace U] [AddTorsor V U]

/-- Strict consistency implies strong consistency. -/
theorem IsStrictlyConsistent.isStronglyConsistent {F : U → X → β}
    (hF : IsStrictlyConsistent F) :
    IsStronglyConsistent 𝕜 F := by
  exact interior_subset_intrinsicInterior ((isStrictlyConsistent_iff (F := F)).1 hF)

end

end Bifunction

/-! ### Lemma_6_29_10 (from Chap06) -/
noncomputable section

universe u

section

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [LinearOrder β] [TopologicalSpace β]
variable [OrderTopology β] [NoMinOrder β] [NoMaxOrder β] [DenselyOrdered β] [SMul 𝕜 β]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.10 is the pure-inequality characterization of strict consistency for
  an ordinary convex program: when there are no equality constraints, strict consistency is
  equivalent to the existence of a point of the constraint set where every inequality is strict.
- `core/canonical`: the strict-consistency owner already exists as
  `Bifunction.IsStrictlyConsistent`, applied to the associated perturbation bifunction.
- `bridge/view`: in the pure-inequality case `s = 0`, the associated bifunction is the
  perturbed-problem owner `P.perturbedProblem` on `P.ConstraintIndex = ι ⊕ κ` with empty equality
  block `κ`, i.e. the
  canonical index-sum perturbation layer with an empty equality block.

Domain-style sampling used here:
- `Bifunction.IsStrictlyConsistent` from `Definition_6_29_10`;
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.exists_kuhnTuckerVector_of_strict_inequality_point` from
  `Corollary_6_28_3`, which already uses the same strict-inequality witness surface
  `∃ x : P.constraintSet, ∀ i, P.inequality i x < 0`.

Primitive data vs derived API:
- primitive source data: a pure-inequality ordinary convex program
  `P : OrdinaryConvexProgram 𝕜 E β r 0 ι κ` with `Fintype.card κ = 0`;
- canonical owner-side predicate: strict consistency of the associated perturbation bifunction
  `P.perturbedProblem`;
- derived source-facing bridge: existence of a point of `P.constraintSet` satisfying all
  inequalities strictly.

Layer target: `source-facing`, stated directly on the existing ordinary-program owner and the
canonical strict-consistency predicate for the associated bifunction.
-/

variable {r : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = 0)]
variable (P : OrdinaryConvexProgram 𝕜 E β r 0 ι κ)

-- Proof sketch: unfold `Bifunction.IsStrictlyConsistent` for the associated bifunction
-- `P.perturbedProblem`, then rewrite the parameter domain using the pure-inequality description
-- of `P.perturbedFeasibleSet`. For the
-- forward implication, choose a
-- small negative perturbation vector in the interior neighborhood of `0`. For the reverse
-- implication, use the strict inequalities `P.inequality i x < 0` to build an open neighborhood
-- of `0` contained in that parameter domain.
/-- Lemma 6.29.10: when an ordinary convex program has only inequality constraints, it is
strictly consistent exactly when there exists a point of the constraint set where every
inequality constraint is satisfied strictly. -/
theorem strictlyConsistent_iff_exists_strict_inequality_point :
    Bifunction.IsStrictlyConsistent P.perturbedProblem ↔
      ∃ x : P.constraintSet, ∀ i, P.inequality i x < 0 := by
  letI : IsEmpty κ := Fintype.card_eq_zero_iff.mp (Fact.out : Fintype.card κ = 0)
  have hdom_iff {u : P.ConstraintIndex → β} :
      u ∈ Bifunction.dom P.perturbedProblem ↔
        ∃ x : P.constraintSet, ∀ i, P.inequality i x ≤ u (Sum.inl i) := by
    rw [Bifunction.mem_dom_iff_exists]
    constructor
    · rintro ⟨x, hx⟩
      have hxmem : x ∈ P.perturbedFeasibleSet u := by
        by_cases hmem : x ∈ P.perturbedFeasibleSet u
        · exact hmem
        · simp [hmem] at hx
      rcases (P.mem_perturbedFeasibleSet_split).1 hxmem with ⟨hxC, hxI, _⟩
      refine ⟨⟨x, hxC⟩, fun i ↦ hxI i⟩
    · rintro ⟨x, hxI⟩
      have hxmem : x.1 ∈ P.perturbedFeasibleSet u := by
        rw [P.mem_perturbedFeasibleSet_split]
        refine ⟨x.2, ?_, ?_⟩
        · intro i
          simpa using hxI i
        · intro j
          exact isEmptyElim j
      refine ⟨x.1, ?_⟩
      simpa [P.perturbedProblem_apply, hxmem] using
        (WithBotTop.coe_lt_top (P.objective x))
  rw [Bifunction.isStrictlyConsistent_iff]
  constructor
  · intro hstrict
    rcases (isOpen_pi_iff'.1 isOpen_interior) 0 hstrict with ⟨v, hv, hsubset⟩
    choose a b hab hsub using
      fun i ↦ (mem_nhds_iff_exists_Ioo_subset.1 ((hv i).1.mem_nhds (hv i).2))
    choose c hca hc0 using
      fun i ↦ exists_between ((Set.mem_Ioo.mp (hab i)).1)
    let u : P.ConstraintIndex → β := c
    have hu_box : u ∈ Set.univ.pi v := by
      rw [Set.mem_pi]
      intro i hi
      apply hsub i
      rcases (Set.mem_Ioo.mp (hab i)) with ⟨hai, hbi⟩
      refine Set.mem_Ioo.mpr ?_
      constructor
      · simpa [u] using hca i
      · exact lt_trans (by simpa [u] using hc0 i) hbi
    rcases hdom_iff.1 (interior_subset (hsubset hu_box)) with ⟨x, hx⟩
    refine ⟨x, fun i ↦ ?_⟩
    have hu_neg : u (Sum.inl i) < 0 := by
      simpa [u] using hc0 (Sum.inl i)
    exact lt_of_le_of_lt (hx i) hu_neg
  · rintro ⟨x, hxstrict⟩
    let lower : P.ConstraintIndex → β := Sum.elim (fun i ↦ P.inequality i x) isEmptyElim
    have hbox :
        Set.univ.pi (fun i ↦ Set.Ioi (lower i)) ∈ nhds (0 : P.ConstraintIndex → β) := by
      refine set_pi_mem_nhds Set.finite_univ ?_
      intro i hi
      cases i with
      | inl i =>
          simpa [lower] using Ioi_mem_nhds (hxstrict i)
      | inr j =>
          exact isEmptyElim j
    have hsubset :
        Set.univ.pi (fun i ↦ Set.Ioi (lower i)) ⊆ Bifunction.dom P.perturbedProblem := by
      intro u hu
      refine hdom_iff.2 ⟨x, fun i ↦ ?_⟩
      have hui : u (Sum.inl i) ∈ Set.Ioi (lower (Sum.inl i)) :=
        (Set.mem_pi.mp hu) (Sum.inl i) (by simp)
      simpa [lower] using le_of_lt hui
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset hbox hsubset

end OrdinaryConvexProgram

end

/-! ### Definition_6_29_11 (from Chap06) -/
noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {α : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.11 introduces the bifunction attached to a constrained problem
  with objective `f₀` and feasible slices `u ↦ S u`, written in the source as
  `F u = f₀ + δ(· | S u)`.
- `core/canonical`: for each fixed `u`, the chapter already owns the canonical extension
  `Function.toWithBotTopOn f₀ (S u)` of the finite objective `f₀` by `+∞` outside the slice
  `S u`.
- `bridge/view`: the source formula `f₀.toWithBotTop + δ(· | S u)` is exactly the companion
  bridge `Function.toWithBotTopOn_eq_add_indicator` applied slice-wise.

Domain-style sampling used here:
- `Function.toWithBotTopOn`;
- `Function.toWithBotTopOn_eq_add_indicator`;
- `indicator` and the notation `δ(· | C)`.

Primitive data vs derived API:
- primitive data: an `α`-valued objective `f₀ : X → α` and feasible slices `S : U → Set X`;
- main owner: the associated bifunction as the direct canonical expression
  `fun u ↦ Function.toWithBotTopOn f₀ (S u)`;
- derived API: the slice formula `Function.toWithBotTopOn f₀ (S u) =
    f₀.toWithBotTop + δ(· | S u)`.

Layer target: `source-facing`, expressed by direct canonical recall/use of
`Function.toWithBotTopOn` rather than by a second Chapter 6 wrapper owner.
-/

variable (f₀ : X → α) (S : U → Set X)

/-- Definition 6.29.11, primitive slice rule: on the feasible slice `S u`, the associated
bifunction agrees with the finite objective branch `f₀`. -/
@[simp] theorem toWithBotTopOn_slice_of_mem
    (u : U) {x : X} (hx : x ∈ S u) :
    Function.toWithBotTopOn f₀ (S u) x = f₀ x := by
  simpa using Function.toWithBotTopOn_of_mem f₀ (S u) hx

/-- Definition 6.29.11, primitive slice rule: outside the feasible slice `S u`, the associated
bifunction takes value `+∞`. -/
@[simp] theorem toWithBotTopOn_slice_of_notMem
    (u : U) {x : X} (hx : x ∉ S u) :
    Function.toWithBotTopOn f₀ (S u) x = (⊤ : WithBotTop α) := by
  simpa using Function.toWithBotTopOn_of_notMem f₀ (S u) hx

section

variable [AddZeroClass α]

/-- Slice-wise bridge/view for Definition 6.29.11: evaluating the associated bifunction at a fixed
parameter `u` is the canonical source formula `f₀.toWithBotTop + δ(· | S u)`. -/
theorem toWithBotTopOn_slice_eq_add_indicator (u : U) :
    Function.toWithBotTopOn f₀ (S u) = f₀.toWithBotTop + (δ(· | S u)) := by
  simpa using Function.toWithBotTopOn_eq_add_indicator f₀ (S u)

/-- Definition 6.29.11 in bifunction owner form: the associated bifunction is the sum of the
constant finite branch `u ↦ f₀.toWithBotTop` and the indicator bifunction `δᵇ(S)`. -/
theorem toWithBotTopOn_eq_const_add_indicatorBifunction :
    (fun u ↦ Function.toWithBotTopOn f₀ (S u)) =
      (fun _ : U ↦ f₀.toWithBotTop) + δᵇ(S) := by
  funext u
  simpa [Pi.add_apply] using
    (toWithBotTopOn_slice_eq_add_indicator (f₀ := f₀) (S := S) u)

end

end

end Bifunction

/-! ### Lemma_6_29_11 (from Chap06) -/
noncomputable section

universe u v w z

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type w} {U : Type u}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable [CompleteSpace 𝕜]
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.11 says that a convex generalized program is strictly consistent if
  and only if every direction in the perturbation space meets the bifunction effective domain after
  some positive dilation.
- `core/canonical`: the existing owner for strict consistency is
  `Bifunction.IsStrictlyConsistent F`, while the source domain owner from Definition 6.29.8 is
  `Bifunction.dom F`.
- `bridge/view`: the source clause “`F (λu)` is not the constant function `+∞`” is exactly the
  membership condition `λ • u ∈ dom F`.

Domain-style sampling used here:
- `Bifunction.IsStrictlyConsistent`;
- `dom(·)` from Chapter 1 effective-domain notation;
- `convᵇ[𝕜](F)`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β`;
- primitive owner hypotheses: strict consistency of `F` and convexity of the source-facing domain
  owner `dom F`;
- derived source-facing bridge: the convex-bifunction specialization where
  `convᵇ[𝕜](F)` implies `Convex 𝕜 (dom F)`.

Layer target: `source-facing`, stated directly on the existing canonical owners rather than through
any new program wrapper; the primary theorem stays at the primitive domain-convexity layer.
-/

-- Proof sketch: `Bifunction.isStrictlyConsistent_iff` identifies strict consistency with
-- `0 ∈ interior (dom F)`, and Corollary 6.4.1 rewrites interior membership at `0` for a convex
-- set into the positive-ray intersection criterion.
/-- Primitive-domain form of Lemma 6.29.11: if `dom F` is convex, then strict consistency is
equivalent to the condition that every perturbation direction `u` has a positive dilation `a`
with `a • u ∈ dom F`. -/
theorem isStrictlyConsistent_iff_forall_exists_pos_smul_mem_dom
    {X : Type v} {β : Type z}
    [Top β] [LT β]
    {F : U → X → β}
    (hdom_convex : Convex 𝕜 (dom F)) :
    IsStrictlyConsistent F ↔
      ∀ u : U, ∃ a > (0 : 𝕜), a • u ∈ dom F := by
  have hzero :
      (0 : U) ∈ interior (dom F) ↔
        ∀ u : U, ∃ a > (0 : 𝕜), (0 : U) + a • u ∈ dom F :=
    hdom_convex.mem_interior_iff_forall_exists_pos_add_smul_mem
  have hzero' :
      (0 : U) ∈ interior (dom F) ↔
        ∀ u : U, ∃ a > (0 : 𝕜), a • u ∈ dom F := by
    simpa [zero_add] using hzero
  exact (isStrictlyConsistent_iff (F := F)).trans hzero'

-- `convᵇ[𝕜](F)` is a derived sufficient owner hypothesis via
-- `Bifunction.convex_dom`.
/-- Convex-bifunction specialization of Lemma 6.29.11. -/
theorem isStrictlyConsistent_iff_forall_exists_pos_smul_mem_dom_of_convex_bifunction
    {X : Type v} {α : Type z}
    [AddCommMonoid X] [SMul 𝕜 X]
    [AddCommMonoid α] [Preorder α] [SMul 𝕜 α]
    {F : U → X → WithBotTop α}
    (hF_convex : convᵇ[𝕜](F)) :
    IsStrictlyConsistent F ↔
      ∀ u : U, ∃ a > (0 : 𝕜), a • u ∈ dom F := by
  exact isStrictlyConsistent_iff_forall_exists_pos_smul_mem_dom
    (convex_dom hF_convex.convex_dom)

end

end Bifunction

/-! ### Definition_6_29_12 (from Chap06) -/
universe u v w r

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.12 attaches to a bifunction `F : U → X → Y` the
  zero-slice objective `x ↦ F 0 x`; in Chapter 6 this is then used on the canonical
  extended-value layer `WithTopBot α` (with `EReal` as a specialization).
- `core/canonical`: the Chapter 6 owner for those perturbation values is already
  `Bifunction.perturbationFunction` from Definition 6.29.1.
- `bridge/view`: the owner file `Definition_6_29_1` already records both the
  `sInf (Set.range (F u))` evaluation formula and the Chapter 1 first-projection
  linear-image identification.

Domain-style sampling used here:
- `Bifunction.perturbationFunction`;
- `Bifunction.perturbationFunction_apply`;
- `Bifunction.perturbationFunction_apply_eq_sInf_range`;
- `Bifunction.perturbationFunction_eq_linearImage_fst`.

Primitive data vs derived API:
- primitive data: the bifunction `F : U → X → Y`;
- primitive source-facing owners: the zero-slice objective `objective F` and the already existing
  perturbation owner `perturbationFunction F`;
- derived API: both perturbation-function companion theorems are reused from the owner file
  `Definition_6_29_1`.

Layer target:
- `source-facing` for `objective`;
- `core/canonical recall/use` for the perturbation-value owner.

Notation decision: Rockafellar uses the recurring zero-slice objective notation `F₀`, so the
owner file exposes the scoped postfix surface `₀`. In `open scoped Rockafellar`, Lean writes this
as `(F)₀` for a general term and also accepts `F ₀` for a named bifunction.
-/

section Objective

variable {U : Type u} {X : Type v} {Y : Type w} [Zero U]

/-- Definition 6.29.12: the objective function of the generalized convex program associated with a
bifunction `F` is its zero slice. -/
def objective (F : U → X → Y) : X → Y :=
  F 0

end Objective

end Bifunction

namespace Rockafellar

/- Rockafellar's zero-slice objective notation. In `open scoped Rockafellar`, a bifunction term
`F` is written as `(F)₀`; for a named bifunction, Lean also accepts `F ₀`. -/
scoped[Rockafellar] postfix:max "₀" => Bifunction.objective

end Rockafellar

namespace Bifunction

open scoped Rockafellar

section Objective

variable {U : Type u} {X : Type v} {Y : Type w} [Zero U]

@[simp] theorem objective_eq (F : U → X → Y) :
    (F)₀ = F 0 :=
  rfl

@[simp] theorem objective_apply (F : U → X → Y) (x : X) :
    (F)₀ x = F 0 x :=
  rfl

end Objective

section ObjectivePerturbation

variable {U : Type u} {X : Type v} {α : Type r}
variable [Zero U]

/-- The unperturbed perturbation value is the infimum of the objective range. -/
@[simp] theorem perturbationFunction_zero_eq_sInf_range
    [InfSet α]
    (F : U → X → α) :
    infᵇ(F) 0 = sInf (Set.range ((F)₀)) := by
  simpa [objective] using
    (perturbationFunction_apply_eq_sInf_range F (0 : U))

/-- The unperturbed perturbation value is the indexed infimum of the objective. -/
@[simp] theorem perturbationFunction_zero_eq_iInf
    [InfSet α]
    (F : U → X → α) :
    infᵇ(F) 0 = ⨅ x, (F)₀ x := by
  simpa [objective] using (perturbationFunction_apply F (0 : U))

end ObjectivePerturbation

/- Definition 6.29.12 uses the existing Chapter 6 owner
`Bifunction.perturbationFunction` for the perturbation-value function `u ↦ inf_x F u x`. -/
recall perturbationFunction

end Bifunction

/-! ### Definition_6_29_13 (from Chap06) -/
universe u v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {Y : Type w} [Zero U]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.13 specializes the generalized-program objective to the case of
  a convex bifunction and records that this zero-slice function is convex.
- `core/canonical`: the source-facing owner for the zero slice is already `Bifunction.objective`
  from Definition 6.29.12, while convexity of a bifunction is already owned by
  `Function.IsConvex 𝕜 (uncurry F)` from Definition 6.29.4.
- `bridge/view`: convexity of the objective is obtained by restricting the convex epigraph of
  `uncurry F` to first-coordinate value `u = 0`.

Domain-style sampling used here:
- `Bifunction.objective` from `Definition_6_29_12`;
- `objective_apply` from the same file;
- `Function.isConvex_iff_convex_epigraph` from `Chap01.Theorem_4_2`;
- `Function.IsConvex` from `Chap01.Theorem_4_2`.

Primitive data vs derived API:
- primitive source-facing owner: `(F)₀`;
- primitive convexity hypothesis: `(uncurry F).IsConvex 𝕜`;
- derived API: convexity of the zero slice `(F)₀.IsConvex 𝕜`.

Layer target:
- clause `(1)` is `core/canonical recall/use` for the objective-function owner;
- clause `(2)` first records the intrinsic fixed-slice owner theorem
  `Function.IsConvex.slice_fixed` at the primitive epigraph layer, then specializes it to the
  zero-slice theorem `Function.IsConvex.slice_zero` and finally to the source-facing objective
  theorem `Function.IsConvex.objective`.
-/

/- Definition 6.29.13 (1): for the generalized convex program associated with a convex bifunction
`F`, the objective function `F₀` is the zero slice already owned by `Bifunction.objective`. -/
recall objective

end

end Bifunction

namespace Function.IsConvex

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMulZeroClass 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid α] [SMul 𝕜 α] [LE α]

/-- A slice at a fixed first-coordinate value is convex whenever that value is fixed by all convex
combinations `(a, b)` with `a + b = 1`. -/
theorem slice_fixed
    {f : U × X → WithBotTop α} (hf : f.IsConvex 𝕜) {u : U}
    (hfixed : ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 → a • u + b • u = u) :
    (fun x : X ↦ f (u, x)).IsConvex 𝕜 := by
  rw [Function.isConvex_iff_convex_epigraph] at hf ⊢
  let S : Set ((U × X) × α) := {r | f r.1 ≤ r.2}
  have hS : Convex 𝕜 S := by
    simpa [S] using hf
  intro p hp q hq a b ha hb hab
  have hp' : (((u, p.1), p.2) : (U × X) × α) ∈ S := by
    simpa [S] using hp
  have hq' : (((u, q.1), q.2) : (U × X) × α) ∈ S := by
    simpa [S] using hq
  simpa [S, Prod.smul_mk, Prod.mk_add_mk, hfixed a b ha hb hab] using
    hS hp' hq' ha hb hab

/-- Definition 6.29.13 (2): the zero-slice objective function of a convex
bifunction is convex. -/
theorem slice_zero
    {f : U × X → WithBotTop α} (hf : f.IsConvex 𝕜) :
    (fun x : X ↦ f (0, x)).IsConvex 𝕜 := by
  refine hf.slice_fixed ?_
  intro a b ha hb hab
  simp

-- Proof sketch: this is the source-facing `Bifunction.objective` specialization of the intrinsic
-- owner theorem `Function.IsConvex.slice_zero`.
theorem objective
    {F : U → X → WithBotTop α} (hF : (uncurry F).IsConvex 𝕜) :
    (F)₀.IsConvex 𝕜 := by
  simpa [Bifunction.objective, Function.uncurry] using
    (hF.slice_zero : (fun x : X ↦ uncurry F (0, x)).IsConvex 𝕜)

end

end Function.IsConvex

/-! ### Definition_6_29_14 (from Chap06) -/
universe u v w

namespace Bifunction

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.14 does not introduce a new mathematical object; it only names
  the zero-slice `F₀` for `(P)` as the objective function.
- `core/canonical`: that owner is already the Chapter 6 declaration `Bifunction.objective`,
  introduced in Definition 6.29.12 and reused in Definition 6.29.13.
- `bridge/view`: the displayed source equation for the zero slice is exactly the existing
  owner-side evaluation theorem `Bifunction.objective_apply`.

Domain-style sampling used here:
- `Bifunction.objective`;
- `Bifunction.objective_apply`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → Y` with zero parameter in `U`;
- owner: `objective F`;
- derived API: the owner-side pointwise identity `objective_apply`.

Layer target: `core/canonical recall/use`.
-/

section

variable {U : Type u} {X : Type v} {Y : Type w}
variable [Zero U]
variable (F : U → X → Y)

/- Definition 6.29.14: the function `F₀` attached to the generalized convex program `(P)` is the
already existing zero-slice owner `Bifunction.objective F`; this item simply calls it the
objective function for `(P)`. -/
#check F ₀
#check objective_apply F

recall objective

/- The displayed source evaluation of `F₀` is the owner-side theorem
`Bifunction.objective_apply`. -/
recall objective_apply

end

end Bifunction
