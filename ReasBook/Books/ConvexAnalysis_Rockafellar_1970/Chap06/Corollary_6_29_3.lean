import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_1_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_29_1

noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar
open Function

set_option linter.style.longLine false

universe u v

namespace Bifunction

section

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [AddCommMonoid X] [Module ℝ X]

variable {F : E → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F
local notation "p.realBranch" => Function.realBranch p
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set (StrongDual ℝ E))

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.3 characterizes uniqueness of the Kuhn--Tucker object for the
  generalized convex program attached to a convex bifunction `F` by differentiability of the
  perturbation function `p = perturbationFunction F` at `0`. In the inner-product bridge
  specialization, the unique Kuhn--Tucker vector is `-∇ p.realBranch 0`, and only after that
  Euclidean bridge does one read its coordinates by partial derivatives.
- `core/canonical`: the existing owners are `Bifunction.perturbationFunction`,
  `Bifunction.IsKuhnTuckerVector`, the Chapter 23 subdifferential owner at `0`, and the Chapter
  25 differentiability/gradient owners for finite real-valued functions on the perturbation
  space.
- `bridge/view`: Theorem 6.29.1 identifies Kuhn--Tucker functionals with negative subgradients of
  the perturbation function `p` at `0`. Definition 6.29.10 supplies the missing local-finiteness
  owner `IsStrictlyConsistent F ↔ 0 ∈ interior (dom p)`, Theorem 25.2 turns uniqueness of that
  subgradient into differentiability of `p.realBranch`, the Fréchet-Riesz inner-product bridge
  turns the unique supporting functional into the vector `-∇ p.realBranch 0`, and
  Theorem 25.1.3 is only the final coordinate translation on the Euclidean perturbation space
  `E = EuclideanSpace ℝ ι`.

Primary mathematical domain:
- perturbation functions of convex bifunctions, Kuhn--Tucker functionals/vectors, and the
  real differentiability/subgradient bridge (with finite-dimensionality needed only for the
  uniqueness-equivalence direction).

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.IsKuhnTuckerVector` from `Definition_6_29_19`;
- `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite` from
  `Theorem_6_29_1`;
- `Function.differentiableAt_iff_existsUnique_mem_subdifferentialAt` from `Theorem_25_2`;
- `∇` on real inner-product spaces from mathlib's gradient owner;
- `Function.gradient_eq_partialDeriv` from `Theorem_25_1_3`;
- the canonical finite real branch `Function.realBranch p` of the perturbation function.

Primitive data vs derived API:
- primitive source data: a convex bifunction `F`, finiteness of `optimalValue F`, and the local
  finiteness owner `IsStrictlyConsistent F`;
- primitive owner surface: `perturbationFunction F` and `IsKuhnTuckerVector F` on the intrinsic
  dual owner `StrongDual ℝ E`;
- derived API in this file: the intrinsic uniqueness criterion via strict consistency together
  with differentiability of `p.realBranch` at `0`, the inner-product bridge
  `uStar = -∇ p.realBranch 0`, and the final Euclidean coordinate formula on the perturbation
  variable via the Chapter 25 partial-derivative owner.

Layer target:
- the first theorem is `source-facing`, but on the weakest finite-dimensional real normed-space
  owner layer `StrongDual ℝ E`;
- the vector identity is `bridge/view` on the inner-product specialization;
- the coordinate formula is the downstream Euclidean bridge only, so only the perturbation space
  should be specialized to Euclidean coordinates.
-/

-- Proof sketch: apply Theorem 6.29.1 to identify Kuhn--Tucker vectors with negative
-- subgradients of `p` at `0`. Definition 6.29.10 records the source's local finiteness at the
-- base point as `IsStrictlyConsistent F`, and once that interior-domain hypothesis is present,
-- uniqueness of the subgradient is equivalent to differentiability of `p.realBranch` at `0` by
-- the Chapter 25 singleton-subdifferential criterion for convex functions.
/-- Corollary 6.29.3 on the intrinsic dual owner: for a convex bifunction `F`, if the optimal
value of the associated generalized convex program is finite, then the program has a unique
Kuhn--Tucker functional exactly when the program is strictly consistent and the real branch
`p.realBranch` of the perturbation function is differentiable at `0`. -/
theorem
    existsUnique_kuhnTuckerFunctional_iff_differentiableAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤) :
    (∃! uStar : StrongDual ℝ E, uStar ∈ KT(F)) ↔
      IsStrictlyConsistent F ∧ DifferentiableAt ℝ p.realBranch 0 := sorry

end

section

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid X] [Module ℝ X]

variable {F : E → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F
local notation "p.realBranch" => Function.realBranch p
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set E)

-- Proof sketch: unpack `hkt : uStar ∈ KT(F)` to recover finite optimal value, then invoke
-- Theorem 6.29.1 to identify the Kuhn--Tucker vector with a negative subgradient of `p` at `0`.
-- The missing local-finiteness hypothesis is the canonical owner `IsStrictlyConsistent F`; with
-- that in place, differentiability of `p.realBranch` rewrites the unique subgradient as
-- `∇ p.realBranch 0`, yielding the source-facing vector identity.
/-- Inner-product bridge for Corollary 6.29.3: in the differentiable case, any Kuhn--Tucker
vector is exactly the negative gradient `-∇ p.realBranch 0`, provided the generalized convex
program is strictly consistent; finiteness of the optimal value is derived from the Kuhn--Tucker
hypothesis. -/
theorem kuhnTuckerVector_eq_neg_gradient_perturbationFunction_zero
    (hF : (uncurry F).IsConvex ℝ)
    (hstrict : IsStrictlyConsistent F)
    {uStar : E}
    (hkt : uStar ∈ KT(F))
    (hdiff : DifferentiableAt ℝ p.realBranch 0) :
    uStar = -∇ p.realBranch 0 := sorry

end

section

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [AddCommMonoid X] [Module ℝ X]

variable {F : E → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F
local notation "p.realBranch" => Function.realBranch p
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set E)

-- Proof sketch: transfer the intrinsic dual-owner theorem to the Riesz-identified vector model
-- `E`, leaving the theorem surface on the chapter notation `KT(F)`.
/-- Corollary 6.29.3 in the inner-product vector model: if the optimal value is finite, then
there is a unique Kuhn--Tucker vector exactly when the program is strictly consistent and
`p.realBranch` is differentiable at `0`. -/
theorem
    existsUnique_kuhnTuckerVector_iff_differentiableAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤) :
    (∃! uStar : E, uStar ∈ KT(F)) ↔
      IsStrictlyConsistent F ∧ DifferentiableAt ℝ p.realBranch 0 := sorry

end

section

variable {ι : Type u} {X : Type v}
variable [Fintype ι]
variable [AddCommMonoid X] [Module ℝ X]

variable {F : EuclideanSpace ℝ ι → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F
local notation "p.realBranch" => Function.realBranch p
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set (EuclideanSpace ℝ ι))

-- Proof sketch: first rewrite `uStar` as `-∇ p.realBranch 0` by the inner-product bridge above;
-- strict consistency supplies the missing local finiteness at `0`, and the needed optimal-value
-- finiteness input is derived by unpacking `hkt : uStar ∈ KT(F)`. Then read the `i`-th coordinate
-- of the gradient using Theorem 25.1.3.
/-- In the differentiable case, every Kuhn--Tucker vector has coordinates given by the negative
partial derivatives of the perturbation function at `0`. This is the Euclidean coordinate bridge
of the canonical vector identity `uStar = -∇ p.realBranch 0`, and only the perturbation space is
specialized to Euclidean coordinates here; strict consistency supplies the source's local
finiteness hypothesis, while finiteness of the optimal value is derived from the Kuhn--Tucker
hypothesis. -/
theorem
    kuhnTuckerVector_apply_eq_neg_partialDeriv_perturbationFunction_zero
    (hF : (uncurry F).IsConvex ℝ)
    (hstrict : IsStrictlyConsistent F)
    {uStar : EuclideanSpace ℝ ι}
    (hkt : uStar ∈ KT(F))
    (hdiff : DifferentiableAt ℝ p.realBranch 0)
    (i : ι) :
    uStar i = -partialDeriv p.realBranch 0 i := sorry

end

end Bifunction
