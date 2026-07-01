import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Proposition_5_24_3

noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜]
variable [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜]
variable [AddRightReflectLE 𝕜] [PosSMulMono 𝕜 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.11 characterizes cyclically monotone multivalued mappings as
  exactly those relations contained in the subdifferential graph of some closed proper convex
  function.
- `core/canonical`: the owner abstractions already present in the project are the relation owner
  `SetRel E Y` for multivalued mappings at the pairing layer,
  `SetRel.CyclicallyMonotone` from Definition 5.24.5,
  `subdifferentialGraph`, and `Function.IsClosedProperConvex`.
- `bridge/view`: the source pointwise clause `ρ(x) ⊆ ∂f(x)` is the relation inclusion
  `ρ ≤ subdifferentialGraph f`.

Domain-style sampling used here:
- `SetRel` from mathlib's relation API, which is the canonical owner layer for multivalued maps;
- `SetRel.CyclicallyMonotone` from
  `Items/Chap05/Definition_5_24_5.lean`,
  the source-facing owner introduced for cyclic monotonicity;
- `subdifferentialGraph` from
  `Items/Chap05/Definition_5_24_3.lean`,
  the canonical graph owner for the dual-valued subdifferential;
- `Function.IsClosedProperConvex` from
  `Items/Chap03/Text_12_3_6.lean`,
  the chapter owner for the admissible convex functions;
- the pairing-parametric codomain layer `Y` with `[HasPairing E Y 𝕜]`, so theorem surfaces stay
  at the intrinsic pairing owner and do not hard-code one concrete dual model.

Primitive data vs derived API:
- primitive owner input: a relation `ρ : SetRel E Y`;
- primitive witness in the existence clause: a function `f : E → WithTopBot 𝕜` with
  `IsClosedProperConvex[𝕜] f`;
- derived bridge API: the source pointwise clause `x⋆ ∈ ∂f(x)` is already read through
  `mem_subdifferentialGraph`.

Layer target: `source-facing`. The theorem keeps Rockafellar's characterization theorem as the
main labeled entry, but it is stated directly with the canonical relation owner and the existing
subdifferential graph owner instead of a parallel multivalued-map wrapper.

Ambient-assumption minimization:
- the source is written on `R^n`; this file keeps only the scalar/order layer used by the reused
  owners and stays codomain-parametric at `HasPairing` level;
- finite-dimensionality and inner-product self-identification are excluded from the theorem
  surface, since only the intrinsic pairing-valued subdifferential owner is used.
-/

namespace SetRel

-- Proof sketch: if `ρ ≤ ∂f`, then every cycle in the graph of `ρ` is also in
-- the graph of `∂f`,
-- and Proposition 5.24.3 gives cyclic monotonicity of `∂f`. Conversely, for a cyclically
-- monotone relation, define Rockafellar's supremum of affine functions using a fixed base graph
-- point when the graph is nonempty, and take any closed proper convex function when `ρ = ∅`; the
-- source proof then shows that the resulting function has `ρ ≤ ∂f`.
/-- The converse existence clause of Theorem 5.24.11: a cyclically monotone relation is contained
in the canonical pairing-valued subdifferential graph of some closed proper convex function. -/
theorem CyclicallyMonotone.exists_isClosedProperConvex_le_subdifferentialGraph
    {ρ : SetRel E Y} (hρ : CMon[𝕜](ρ)) :
    ∃ f : E → WithTopBot 𝕜,
      IsClosedProperConvex[𝕜] f ∧ ρ ≤ gph∂[Y](f) := by
  by_cases hρempty : ρ = ∅
  · refine ⟨(δ[𝕜](· | (Set.univ : Set E))), ?_, ?_⟩
    · simpa using
        (indicatorFunction_isClosedProperConvex_of_nonempty
          (𝕜 := 𝕜) (C := (Set.univ : Set E))
          Set.univ_nonempty isClosed_univ
          (convex_univ : Convex 𝕜 (Set.univ : Set E)))
    · intro p hp
      simp [hρempty] at hp
  · -- Nonempty-graph branch: Rockafellar's cyclic-potential construction.
    sorry

/-- Theorem 5.24.11 (Rockafellar's Theorem 24.8): a multivalued mapping on the intrinsic
topological-module layer is cyclically monotone exactly when it is contained in the subdifferential
graph of some closed proper convex function. The theorem surface uses the intrinsic pairing-valued
owner `subdifferentialGraph`, rather than the inner-product bridge owner.
-/
theorem cyclicallyMonotone_iff_exists_isClosedProperConvex_le_subdifferentialGraph
    (ρ : SetRel E Y) :
    CMon[𝕜](ρ) ↔
      ∃ f : E → WithTopBot 𝕜,
        IsClosedProperConvex[𝕜] f ∧ ρ ≤ gph∂[Y](f) := by
  constructor
  · intro hρ
    exact hρ.exists_isClosedProperConvex_le_subdifferentialGraph
  · rintro ⟨f, hf, hρf⟩
    -- The graph `subdifferentialGraph f` is cyclically monotone by Proposition 5.24.3, and
    -- cyclic monotonicity is inherited by subrelations via `hρf`.
    have hsubgrad :
        CMon[𝕜](gph∂[Y](f)) := by
      simpa using (subdifferentialGraph_cyclicallyMonotone (f := f) hf.proper)
    refine ⟨?_⟩
    intro m x xStar hx
    exact hsubgrad.sum_nonpos m x xStar (fun i ↦ hρf (hx i))

end SetRel

end
