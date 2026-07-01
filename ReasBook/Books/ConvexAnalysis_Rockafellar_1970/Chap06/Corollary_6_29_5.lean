import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_6_29_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_29_1

noncomputable section

open Function
open scoped Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.5 states two consequences for a convex bifunction `F` whose
  associated generalized convex program has finite optimal value and is strictly consistent:
  `(inf F)` is finite and continuous on some open convex neighborhood of `0`, and the
  Kuhn--Tucker vectors form a nonempty closed bounded convex set.
- `core/canonical`: the relevant owner layer is already present as
  `Bifunction.perturbationFunction`, `Bifunction.optimalValue`, `Bifunction.IsStrictlyConsistent`,
  and `Bifunction.kuhnTuckerVectorSet`, with the Kuhn--Tucker geometry owned intrinsically on
  `StrongDual ℝ U`.
- `bridge/view`: clause `(1)` routes continuity of `inf F` through the canonical convex-function
  continuity theorem on subsets of the effective domain, while the Euclidean self-dual reading of
  the Kuhn--Tucker geometry is kept only as an inner-product-space bridge specialization.

Domain-style sampling used here:
- `Bifunction.perturbationFunction_isConvex` and
  `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite`
  from `Chap06.Theorem_6_29_1`;
- `Bifunction.IsStrictlyConsistent` and
  `Bifunction.isStrictlyConsistent_iff_mem_interior_dom_perturbationFunction` from
  `Chap06.Definition_6_29_10`;
- `Bifunction.kuhnTuckerVectorSet_nonempty_of_optimalValue_finite_of_stronglyConsistent` from
  `Chap06.Corollary_6_29_4`, together with
  `Bifunction.isClosed_kuhnTuckerVectorSet_of_optimalValue_finite` and
  `Bifunction.convex_kuhnTuckerVectorSet_of_optimalValue_finite` from
  `Chap06.Corollary_6_29_1`;
- `Function.IsConvex.continuousOn` from
  `Chap02.Theorem_10_1`;
- `_root_.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom` from
  `Chap05.Theorem_23_4`.

Primitive data vs derived API:
- primitive source data: a convex bifunction `F : U → X → WithBotTop ℝ`;
- primitive owner hypotheses: finiteness of `optimalValue F` and strict consistency of `F`;
- derived API: an open convex neighborhood of `0` on which `perturbationFunction F = inf F` is
  finite and continuous, and the nonempty/closed/bounded/convex geometry of the Kuhn--Tucker set
  in the canonical dual, with Euclidean vector-space restatements only as bridge views.

Layer target:
- clause `(1)` remains `source-facing`, written directly with `IsOpen`, `Convex`, `dom(·)`,
  `≠ ⊥`, and `ContinuousOn` rather than through a parallel neighborhood wrapper;
- clauses `(2)` and `(3)` are refined first to the `core/canonical` dual owner
  `StrongDual ℝ U`;
- Euclidean inner-product-space formulations are kept only as `bridge/view` companions.
-/

section Neighborhood

variable {U : Type u} {X : Type v}
variable [AddCommGroup U] [TopologicalSpace U] [IsTopologicalAddGroup U]
variable [Module ℝ U] [ContinuousConstSMul ℝ U] [FiniteDimensional ℝ U]
variable [AddCommMonoid X] [Module ℝ X]
variable {F : U → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F

-- Proof sketch: `perturbationFunction F` is convex by Theorem 6.29.1. Strict consistency gives
-- `0 ∈ interior (dom (perturbationFunction F))`, and finiteness of `optimalValue F = p 0`
-- rules out the improper case by Theorem 7.2, so `p` is finite on that interior neighborhood.
-- Then Theorem 10.1 yields continuity on the chosen open convex neighborhood, and the
-- conclusion is recorded directly by the canonical owners `IsOpen`, `Convex`, `dom(·)`,
-- `ContinuousOn`, together with the lower-side finiteness clause `p u ≠ ⊥`.
omit [AddCommMonoid X] [Module ℝ X] in
/-- Corollary 6.29.5 (1), owner form: assuming convexity of the perturbation-function owner
`perturbationFunction F`, finite optimal value, and strict consistency, there is an open convex
neighborhood `C` of `0` on which `perturbationFunction F` is finite and continuous. -/
theorem
    exists_open_convex_neighborhood_zero_finite_continuous_of_perturbationFunction_isConvex
    (hp_convex : (perturbationFunction F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    ∃ C : Set U,
      IsOpen C ∧ Convex ℝ C ∧ (0 : U) ∈ C ∧ C ⊆ dom(perturbationFunction F) ∧
        (∀ u : U, u ∈ C → perturbationFunction F u ≠ ⊥) ∧
        ContinuousOn (perturbationFunction F) C := sorry

/-- Corollary 6.29.5 (1), source-facing form: if a convex bifunction `F` has finite optimal value
and is strictly consistent, then there exists an open convex neighborhood `C` of `0` on which the
perturbation function `perturbationFunction F`, i.e. `inf F`, is finite and continuous. Here
“finite” is recorded canonically as `u ∈ dom(p)` together with `p u ≠ ⊥`. -/
theorem exists_open_convex_neighborhood_zero_on_which_perturbationFunction_is_finite_and_continuous
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    ∃ C : Set U,
      IsOpen C ∧ Convex ℝ C ∧ (0 : U) ∈ C ∧ C ⊆ dom(p) ∧
        (∀ u : U, u ∈ C → p u ≠ ⊥) ∧ ContinuousOn p C := by
  exact
    exists_open_convex_neighborhood_zero_finite_continuous_of_perturbationFunction_isConvex
      (F := F) (hp_convex := perturbationFunction_isConvex hF) hoptimal hstrict

end Neighborhood

section KuhnTuckerDual

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [AddCommMonoid X] [Module ℝ X]
variable {F : U → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F

-- Proof sketch: Theorem 6.29.1 identifies Kuhn--Tucker vectors with negatives of the
-- subdifferential of `perturbationFunction F` at `0`. Strict consistency puts `0` in the
-- interior of the perturbation-function domain, and Theorem 23.4 then makes that
-- subdifferential nonempty and bounded; reflection by negation preserves both properties.
omit [AddCommMonoid X] [Module ℝ X] in
/-- Corollary 6.29.5 (2), owner boundedness form: if `perturbationFunction F` is convex, the
optimal value is finite, and `F` is strictly consistent, then the Kuhn--Tucker vector set is
bounded in the canonical dual perturbation space. -/
theorem
    isBounded_kuhnTuckerVectorSet_of_optimalValue_finite_of_strictConsistency_of_pConvex
    (hp_convex : (perturbationFunction F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    Bornology.IsBounded (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)) := sorry

/-- Corollary 6.29.5 (2): under finite optimal value and strict consistency, the Kuhn--Tucker
vectors of `F` form a nonempty bounded subset of the canonical dual perturbation space. -/
theorem kuhnTuckerVectorSet_nonempty_and_bounded_of_optimalValue_finite_of_isStrictlyConsistent
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)).Nonempty ∧
      Bornology.IsBounded (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)) := by
  refine ⟨?_, ?_⟩
  · exact kuhnTuckerVectorSet_nonempty_of_optimalValue_finite_of_stronglyConsistent
      hF hoptimal hstrict.isStronglyConsistent
  · exact
      isBounded_kuhnTuckerVectorSet_of_optimalValue_finite_of_strictConsistency_of_pConvex
        (F := F) (hp_convex := perturbationFunction_isConvex hF) hoptimal hstrict

-- Proof sketch: Corollary 6.29.1 already gives closedness and convexity of the Kuhn--Tucker
-- vector set from finiteness of the optimal value, via the subdifferential characterization at
-- `0` and invariance of these properties under negation.
omit [FiniteDimensional ℝ U] [AddCommMonoid X] [Module ℝ X] in
/-- Corollary 6.29.5 (3): if the optimal value of the generalized convex program associated with
`F` is finite, then the Kuhn--Tucker vectors form a closed convex subset of the perturbation
dual space. -/
theorem isClosed_and_convex_kuhnTuckerVectorSet_of_optimalValue_finite
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤) :
    IsClosed (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)) ∧
      Convex ℝ (kuhnTuckerVectorSet F : Set (StrongDual ℝ U)) := by
  exact ⟨isClosed_kuhnTuckerVectorSet_of_optimalValue_finite hoptimal,
    convex_kuhnTuckerVectorSet_of_optimalValue_finite hoptimal⟩

end KuhnTuckerDual

section KuhnTuckerEuclideanBridge

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [AddCommMonoid X] [Module ℝ X]
variable {F : U → X → WithBotTop ℝ}

local notation "KTᵥ(" F ")" => (kuhnTuckerVectorSet F : Set U)

-- Proof sketch: transport the intrinsic dual-owner theorem through the Fréchet-Riesz
-- identification `InnerProductSpace.toDualMap ℝ U`.
/-- Corollary 6.29.5 (2), Euclidean bridge form: under finite optimal value and strict
consistency, the Kuhn--Tucker vectors form a nonempty bounded subset of the self-dual
inner-product perturbation space. -/
theorem kuhnTuckerVectorSet_nonempty_and_bounded_euclidean
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hstrict : IsStrictlyConsistent F) :
    (KTᵥ(F)).Nonempty ∧ Bornology.IsBounded (KTᵥ(F)) := sorry

-- Proof sketch: transport the intrinsic dual-owner closed/convex theorem through the same
-- Fréchet-Riesz identification.
omit [FiniteDimensional ℝ U] [AddCommMonoid X] [Module ℝ X] in
/-- Corollary 6.29.5 (3), Euclidean bridge form: if the optimal value is finite, then the
Kuhn--Tucker vectors form a closed convex subset of the self-dual inner-product perturbation
space. -/
theorem isClosed_and_convex_kuhnTuckerVectorSet_euclidean
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤) :
    IsClosed (KTᵥ(F)) ∧ Convex ℝ (KTᵥ(F)) := sorry

end KuhnTuckerEuclideanBridge

end Bifunction
