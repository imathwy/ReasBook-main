import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_19_1_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_15
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14

noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.18 states strong duality for the polyhedral primal-dual pair:
  the primal optimal value and the dual optimal value coincide unless both programs are
  inconsistent.
- `core/canonical`: the Chapter 6 owners already present are `optimalValue`,
  `upperPerturbationFunction`, `adjoint`, and `IsConsistent`.
- `bridge/view`: the source dual value `v(P*)` is rendered canonically by the dual perturbation
  value `upperPerturbationFunction (adjoint F) 0`, which Corollary 6.30.2 also identifies
  with the supremum of the dual zero-slice objective.

Primary mathematical domain:
- convex duality for polyhedral proper convex bifunctions on finite-dimensional paired
  spaces with the Chapter 6 extended-value codomain `WithBotTop 𝕜`.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph` and its convexity/closedness API from Chapter 19;
- `optimalValue` from Definition 6.29.15;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` from Definition 6.30.14;
- the primal-dual value identities at `0` from Corollary 6.30.2.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- source hypotheses: polyhedrality of the graph epigraph, properness of the graph function, and
  consistency of at least one side of the primal-dual pair;
- primitive owners already upstream: `optimalValue F`, `upperPerturbationFunction F⋆ 0`, and the
  consistency predicates for `F` and `F⋆`;
- derived API added here: the strong-duality equality of the primal and dual optimal values.

Layer target: `bridge/view`, stated directly on the canonical Chapter 6 value owners rather than
through a new wrapper for the primal-dual program pair.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [T2Space U] [FiniteDimensional 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)
local notation "q" => supᵇ(F⋆)

-- Proof sketch: use polyhedrality plus properness to upgrade `Function.uncurry F` to the closed
-- proper convex owner, and use polyhedrality again on the primal or dual perturbation function
-- that corresponds to the consistent side. Corollary 6.30.2 identifies the dual value with
-- `cl(perturbationFunction F) 0`; consistency of either the primal or the dual side forces the
-- relevant polyhedral perturbation function to be closed at `0`, so the closure value equals the
-- actual value and yields `optimalValue F = upperPerturbationFunction F⋆ 0`.
/-- Theorem 6.30.18: if `F` has polyhedral epigraph, its graph function is proper, and at least
one of the primal program `(P)` or the adjoint dual program `(P*)` is consistent, then the
optimal values of `(P)` and `(P*)` are equal. Canonically, this is the equality between the
primal optimal value `optimalValue F` and the dual perturbation value
`upperPerturbationFunction F⋆ 0`. The polyhedral-epigraph owner already includes the convexity
part of the source phrase “polyhedral proper convex.” -/
theorem optimalValue_eq_dualValue_of_polyhedral_of_primal_or_dual_consistent
    (hF_poly : (Function.uncurry F).HasPolyhedralEpigraph)
    (hF_proper : (Function.uncurry F).IsProper)
    (hconsistent : IsConsistent F ∨ IsConsistent F⋆) :
    optimalValue F = q 0 := sorry

end

end Bifunction
