import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_23
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_29_1

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.29.2 says that a polyhedral convex bifunction has polyhedral
  objective and perturbation functions, and that finite optimal value yields existence and
  polyhedrality of the primal optimal-solution set and the Kuhn--Tucker-vector set.
- `core/canonical`: the existing owner layer is already present as
  `Function.HasPolyhedralEpigraph` on `Function.uncurry F`, `objective`,
  `perturbationFunction`, `optimalValue`, `optimalSolutionSet`, and the intrinsic-dual
  Kuhn--Tucker owner `(kuhnTuckerVectorSet F : Set (StrongDual 𝕜 U))`.
- `bridge/view`: the primal optimal-solution set is compared with `minimumSet (F)₀`, while the
  Kuhn--Tucker vectors are compared with the intrinsic subdifferential set
  `∂[StrongDual 𝕜 U](perturbationFunction F)(0)`.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph.comp_linearMap` and
  `Function.HasPolyhedralEpigraph.linearImage` from Chapter 19;
- `Function.HasPolyhedralEpigraph.isPolyhedral_preimage_Iic` from Chapter 19;
- `objective` from `Definition_6_29_13`;
- `perturbationFunction` and `IsKuhnTuckerVector` from `Theorem_6_29_1`;
- `optimalSolutionSet` and `optimalSolutionSet_eq_minimumSet_of_consistent` from `Lemma_6_29_8`;
- `Function.HasPolyhedralEpigraph.exists_mem_isMinOn_of_isPolyhedral_of_lower_bound` from
  `Corollary_6_27_4`;
- `Function.HasPolyhedralEpigraph.subdifferentialAt_nonempty` and
  `Function.HasPolyhedralEpigraph.subdifferentialAt_isPolyhedral` from `Theorem_23_10`, both
  on `StrongDual 𝕜 U`.

Primitive data vs derived API:
- primitive source data: a bifunction `F`;
- primitive owner hypothesis: `polyᵇ F`;
- derived owners: polyhedrality of `(F)₀` and `perturbationFunction F`, existence of an element of
  `optimalSolutionSet F`, nonemptiness of
  `(kuhnTuckerVectorSet F : Set (StrongDual 𝕜 U))`, and the polyhedrality of the corresponding
  primal and intrinsic-dual solution sets.

Ambient refinement:
- clauses `(1)`, `(2)`, `(3)`, and `(5)` live on the scalar-generic Chapter 19/27 owner layer;
- clauses `(4)` and `(6)` stay on the canonical intrinsic-dual owner `StrongDual 𝕜 U`, matching
  the scalar-generic Chapter 23 subdifferential API.

Layer target: `source-facing`, stated directly on the established Chapter 6 owners and split only
along the genuine owner boundary between scalar-generic polyhedral program data and the intrinsic
strong-dual API.
-/

section Objective

variable {𝕜 : Type w} [Semiring 𝕜] [Preorder 𝕜]
variable {U : Type u} [AddCommMonoid U] [Module 𝕜 U]
variable {X : Type v} [AddCommMonoid X] [Module 𝕜 X]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: rewrite `(F)₀` as the pullback of `Function.uncurry F` along the linear map
-- `LinearMap.inr 𝕜 U X : X →ₗ[𝕜] U × X`, then apply the Chapter 19 pullback owner for
-- polyhedral epigraphs.
/-- Theorem 6.29.2 (1): if `F` is a polyhedral convex bifunction, then its objective function
`F₀` is a polyhedral convex function. -/
theorem objective_hasPolyhedralEpigraph
    (hF_poly : polyᵇ F) :
    ((F)₀).HasPolyhedralEpigraph := sorry

end Objective

section Perturbation

variable {𝕜 : Type w} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [DenselyOrdered 𝕜] [NoBotOrder 𝕜] [NoMaxOrder 𝕜]
variable {U : Type u} [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable {X : Type v} [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: rewrite `perturbationFunction F` as the linear image in the `U`-direction of the
-- polyhedral graph function `Function.uncurry F`, then apply the Chapter 19 linear-image theorem
-- for polyhedral epigraphs.
/-- Theorem 6.29.2 (2): if `F` is a polyhedral convex bifunction, then its perturbation function
`perturbationFunction F` is a polyhedral convex function. -/
theorem perturbationFunction_hasPolyhedralEpigraph
    (hF_poly : polyᵇ F) :
    (perturbationFunction F).HasPolyhedralEpigraph := sorry

end Perturbation

section PolyhedralProgram

variable {𝕜 : Type w} [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [CompleteSpace 𝕜]
variable {U : Type u} [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable {X : Type v} [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: clause `(1)` gives a polyhedral objective. The finite optimal value furnishes a
-- scalar lower bound for `(F)₀`, so Chapter 6.27 attainment on the polyhedral set `Set.univ`
-- yields a minimizer of `(F)₀`. Consistency follows from the finite-value hypothesis, and
-- Lemma 6.29.8 then identifies that minimizer with an element of `optimalSolutionSet F`.
/-- Theorem 6.29.2 (3): if `F` is polyhedral and `optimalValue F` is finite, then the generalized
convex program attached to `F` has an optimal solution. -/
theorem optimalSolutionSet_nonempty_of_optimalValue_finite
    (hF_poly : polyᵇ F)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (optimalSolutionSet F).Nonempty := sorry

-- Proof sketch: clause `(1)` gives a polyhedral objective. Under finite optimal value,
-- `optimalSolutionSet F` agrees with `minimumSet (F)₀`, which is the scalar sublevel set of
-- `(F)₀` at the finite level `optimalValue F`. Chapter 19 makes that scalar sublevel set
-- polyhedral.
/-- Theorem 6.29.2 (5): if `F` is polyhedral and `optimalValue F` is finite, then the set of all
optimal solutions is a polyhedral convex set. -/
theorem optimalSolutionSet_isPolyhedral_of_optimalValue_finite
    (hF_poly : polyᵇ F)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (optimalSolutionSet F).IsPolyhedral 𝕜 := sorry

end PolyhedralProgram

section CanonicalDual

variable {𝕜 : Type w} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {U : Type u} {X : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: clause `(2)` gives a polyhedral perturbation function. The finiteness of
-- `optimalValue F = perturbationFunction F 0` makes the value at `0` finite, so Theorem 23.10
-- gives a nonempty intrinsic subdifferential at `0` in `StrongDual 𝕜 U`. Theorem 6.29.1 then
-- identifies Kuhn--Tucker vectors with the negatives of those subgradients.
/-- Theorem 6.29.2 (4): if `F` is polyhedral and `optimalValue F` is finite, then the generalized
convex program attached to `F` has a Kuhn--Tucker vector in the canonical dual
`StrongDual 𝕜 U`. -/
theorem kuhnTuckerVectorSet_nonempty_of_optimalValue_finite
    (hF_poly : polyᵇ F)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (KT(F) : Set (StrongDual 𝕜 U)).Nonempty := sorry

-- Proof sketch: clause `(2)` gives a polyhedral perturbation function, and the finiteness
-- hypothesis gives a finite value at `0`. Theorem 23.10 makes the intrinsic subdifferential
-- `∂[StrongDual 𝕜 U](perturbationFunction F)(0)` nonempty and polyhedral, while Theorem 6.29.1
-- identifies `KT(F)` with its image under negation.
/-- Theorem 6.29.2 (6): if `F` is polyhedral and `optimalValue F` is finite, then the set of all
Kuhn--Tucker vectors in the canonical dual `StrongDual 𝕜 U` is a polyhedral convex set. -/
theorem kuhnTuckerVectorSet_isPolyhedral_of_optimalValue_finite
    (hF_poly : polyᵇ F)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (KT(F) : Set (StrongDual 𝕜 U)).IsPolyhedral 𝕜 := sorry

end CanonicalDual

end Bifunction
