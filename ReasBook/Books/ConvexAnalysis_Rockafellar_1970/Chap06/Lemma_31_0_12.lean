import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_16
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_6_30_3

noncomputable section

universe u

open Filter
open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasContinuousPairing E Y 𝕜]
variable {f g : E → WithTopBot 𝕜}

local notation "F" =>
  (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)
local notation "p" => perturbationFunction F
local notation "F⋆" => ((adjoint Y Y F) : Y → Y → WithTopBot 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.12 compares the dual objective
  `sup_xStar (g* xStar - f* xStar)` on an abstract dual-side pairing carrier `Y`
  with the perturbation-value function
  `p(u) = inf_x (f x - g (x + u))`, concluding
  `sup_xStar (g* xStar - f* xStar) = liminf_{u → 0} p(u) ≤ p(0)`.
- `core/canonical`: the relevant owner abstractions already present in the project are
  `perturbationFunction (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)`,
  the Chapter 6 dual-objective owner `((F⋆)₀)`,
  the Chapter 6 consistency owners `IsConsistent F` and `IsConsistent F⋆`,
  the pairing-level identity-map specialization pattern used in `Lemma_31_0_13`,
  and the filter-side liminf owner.
- `bridge/view`: the source liminf statement is the evaluation at `0` of the canonical
  Chapter 6 perturbation/adjoint duality layer, with the self-dual or Euclidean surface treated
  only as a later bridge. No new local `p` definition or second dual-objective owner is needed.

Domain-style sampling used here:
- `Bifunction.perturbationFunction`;
- `((adjoint Y Y F)₀)` / `(F⋆)₀` from `Definition_6_30_16`;
- `IsConsistent` from `Definition_6_29_1`;
- `Bifunction.objective_adjoint_fenchelPerturbation_apply` from `Lemma_31_0_8`;
- the pairing-level dual-owner formulation in `Lemma_31_0_13`;
- the Corollary 6.30.3 liminf owner theorem for perturbation functions and adjoint upper
  perturbation functions, whose self-dual specialization underlies this source-facing statement.

Primitive data vs derived API:
- primitive source data: joint convexity of the identity-map Fenchel perturbation on `E × E`,
  together with primal-or-dual consistency at the Chapter 6 owner layer
  `IsConsistent F ∨ IsConsistent F⋆`;
- primitive owner object: the perturbation function of the identity-map Fenchel perturbation;
- derived API: the dual-objective equality with the liminf of that perturbation function, and the
  immediate neighborhood-filter inequality `liminf ... ≤ p(0)`.

Layer target: `source-facing`, stated directly on the existing owner objects instead of on a
parallel local wrapper around `p` or around the concave conjugate.
-/

/-- Core owner form for Lemma 31.0.12: if the identity-map Fenchel perturbation is jointly convex
on `E × E` and either the primal or the dual program is consistent, then the dual upper
perturbation value at `0` equals the liminf at `0` of the perturbation function. -/
theorem upperPerturbationFunction_adjoint_zero_eq_liminf_perturbationFunction_fenchelPerturbation_id
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hconsistent : IsConsistent F ∨ IsConsistent F⋆) :
    supᵇ(F⋆) (0 : Y) =
      liminf p (nhds (0 : E)) := by
  symm
  simpa [p] using
    (liminf_perturbationFunction_eq_upperPerturbationFunction_adjoint_zero_of_primal_or_dual_consistent
      (F := F) hF_convex hconsistent)

/-- Lemma 31.0.12, source dual-objective surface: the supremum of the dual objective
`((F⋆)₀ : Y → WithTopBot 𝕜)` equals the liminf at `0` of the perturbation function. This is the
zero-slice rewrite of
`upperPerturbationFunction_adjoint_zero_eq_liminf_perturbationFunction_fenchelPerturbation_id`. -/
theorem dualObjective_eq_liminf_perturbationFunction_fenchelPerturbation_id
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hconsistent : IsConsistent F ∨ IsConsistent F⋆) :
    (⨆ xStar : Y, (F⋆)₀ xStar) =
      liminf p (nhds (0 : E)) := by
  simpa using
    (upperPerturbationFunction_adjoint_zero_eq_liminf_perturbationFunction_fenchelPerturbation_id
      (hF_convex := hF_convex) (hconsistent := hconsistent))

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [Ring 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
variable {f g : E → WithTopBot 𝕜}

local notation "F" =>
  (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)
local notation "p" => perturbationFunction F

/-- The liminf at `0` of the identity-map Fenchel perturbation value function is bounded above by
its value at `0`, i.e. by Rockafellar's `p(0)`. Together with
`perturbationFunction_fenchelPerturbation_id_apply (u := 0)`, this is the source inequality
`liminf_{u → 0} p(u) ≤ p(0) = inf_x (f x - g x)`. -/
theorem liminf_perturbationFunction_fenchelPerturbation_id_le_at_zero
    : liminf p (nhds (0 : E)) ≤ p 0 := by
  refine liminf_le_of_frequently_le' ?_
  rw [frequently_iff]
  intro s hs
  exact ⟨0, mem_of_mem_nhds hs, le_rfl⟩

end

end Bifunction
