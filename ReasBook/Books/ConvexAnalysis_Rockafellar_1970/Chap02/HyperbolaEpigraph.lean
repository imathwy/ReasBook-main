import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this shared source-facing owner will be reused by multiple items.

section

open Set
variable {𝕜 : Type*} [Inv 𝕜] [Zero 𝕜] [Preorder 𝕜]

/-!
Source/core/bridge triage for this owner.

- `source-facing`: the closed convex set
  `C = {(ξ₁, ξ₂) | 0 < ξ₁ ∧ ξ₁⁻¹ ≤ ξ₂} ⊆ 𝕜 × 𝕜` recurs in Chapter 2 and again in Chapter 11 as a
  standard counterexample/separation witness.
- `core/canonical`: the organizing owner abstraction is the chapter epigraph notation `epi`,
  applied to the reciprocal function on `Set.Ioi (0 : 𝕜)`, together with the standard predicates
  `Convex 𝕜` and `IsClosed`.
- `bridge/view`: the coordinate description `(ξ₁, ξ₂)` is recovered by `p.1` and `p.2`, and the
  membership rewrite is the canonical companion lemma derived from the epigraph owner.

Primitive data vs derived API:
- primitive data: the source-facing set `hyperbolaEpigraph`;
- derived API: its coordinate membership description, convexity, and closedness.

Domain-style sampling used here:
- `epi` and `mem_epi_restrict_iff` from Definition 4.1;
- `ConvexOn.convex_epigraph` and `convexOn_iff_convex_epigraph`;
- `lowerSemicontinuousOn_iff_isClosed_epigraph` and `IsClosed.epigraph`.

Layer target: this file is the shared `source-facing` owner for the concrete hyperbola epigraph.
Downstream files should reuse it instead of importing an example file just to access the set.
-/

/-- The hyperbolic epigraph
`C = { (ξ₁, ξ₂) | 0 < ξ₁ ∧ ξ₁⁻¹ ≤ ξ₂ }` used in Rockafellar's projection and separation examples. -/
def hyperbolaEpigraph : Set (𝕜 × 𝕜) :=
  epi[Set.Ioi (0 : 𝕜)] fun x : 𝕜 ↦ ((x⁻¹ : 𝕜) : WithBotTop 𝕜)

-- Proof sketch: `hyperbolaEpigraph` is the chapter epigraph owner for the reciprocal function on
-- `Ioi (0 : 𝕜)`. Unpack membership with `mem_epi_restrict_iff` and coerce the reciprocal inequality
-- back to `𝕜`.
/-- Membership in `hyperbolaEpigraph` is exactly the coordinate inequality
`0 < x` and `x⁻¹ ≤ y`. -/
theorem mem_hyperbolaEpigraph_iff {x y : 𝕜} :
    (x, y) ∈ hyperbolaEpigraph ↔ 0 < x ∧ x⁻¹ ≤ y := by
  simp [hyperbolaEpigraph, epi]
  intro _
  change
    (((x⁻¹ : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜)) ≤
        (((y : 𝕜) : WithBot 𝕜) : WithTop (WithBot 𝕜)) ↔ x⁻¹ ≤ y
  rw [WithTop.coe_le_coe, WithBot.coe_le_coe]

section

variable [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
local notation "hyperbolaEpigraph" => (@hyperbolaEpigraph 𝕜 _ _ _)

-- Proof sketch: view `hyperbolaEpigraph` as the epigraph of the convex function `x ↦ x⁻¹` on the
-- convex domain `Ioi (0 : 𝕜)`, then apply the standard convex-epigraph criterion.
/-- The set `hyperbolaEpigraph` is convex. -/
theorem hyperbolaEpigraph_convex : Convex 𝕜 hyperbolaEpigraph := sorry

-- Proof sketch: treat `hyperbolaEpigraph` as the epigraph of `x ↦ x⁻¹` on `Ioi (0 : 𝕜)`. The
-- domain and the defining inequality are closed under limits along convergent sequences, so the
-- epigraph is closed.
section

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/-- The set `hyperbolaEpigraph` is closed in `𝕜 × 𝕜`. -/
theorem hyperbolaEpigraph_isClosed : IsClosed hyperbolaEpigraph := sorry

end

end

end
