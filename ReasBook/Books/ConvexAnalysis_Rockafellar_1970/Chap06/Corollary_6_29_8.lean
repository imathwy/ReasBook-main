import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_21
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_29_4

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
