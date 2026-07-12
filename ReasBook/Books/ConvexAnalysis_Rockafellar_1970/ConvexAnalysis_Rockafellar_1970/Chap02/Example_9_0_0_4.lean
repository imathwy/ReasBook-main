import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3
import ConvexAnalysis_Rockafellar_1970.Chap02.HyperbolaEpigraph

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set
open Function

variable {𝕜 : Type*}
variable [Inv 𝕜] [Zero 𝕜]

local notation "π₁" => (Prod.fst : 𝕜 × 𝕜 → 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 9.0.0.4 is the projection statement that the concrete closed convex
  set `hyperbolaEpigraph` has nonclosed first-coordinate image.
- `core/canonical`: the reusable owner object for projections of sets in `𝕜 × 𝕜` is the effective
  domain of `Function.verticalInfimum`; for this example that owner is
  `dom(verticalInfimum hyperbolaEpigraph)`.
- `bridge/view`: the textbook projection onto `ξ₁` is recovered through
  `Function.effectiveDomain_verticalInfimum_eq_image_fst`.
- Primitive data vs derived API: the primitive data now live upstream in
  `Chap02.HyperbolaEpigraph`; this file contributes the example-specific projection computation at
  the primitive set-image layer, then exports owner-form corollaries via the
  vertical-infimum bridge.
- Layer target: `source-facing`, reusing the shared owner instead of redefining it locally.

Domain-style sampling used here:
- the shared Chapter 2 owner `hyperbolaEpigraph`;
- `mem_hyperbolaEpigraph_iff`;
- `Function.effectiveDomain_verticalInfimum_eq_image_fst` as the set-projection/effective-domain
  bridge;
- `closure_Ioi` for the nonclosedness of the projected image.
-/

section

variable [Preorder 𝕜]

-- Proof sketch: compute the first-coordinate projection directly: a projected point `(x, y)` in
-- `hyperbolaEpigraph` has `x > 0`; conversely, each `x > 0` has witness `(x, x⁻¹)`.
/-- The first-coordinate projection of `hyperbolaEpigraph` is exactly `(0, +∞)`. -/
theorem image_fst_hyperbolaEpigraph_eq_Ioi :
    π₁ '' hyperbolaEpigraph = Ioi (0 : 𝕜) := by
  ext x
  constructor
  · rintro ⟨⟨x, y⟩, hp, rfl⟩
    exact (mem_hyperbolaEpigraph_iff.mp hp).1
  · intro hx
    exact ⟨(x, x⁻¹), mem_hyperbolaEpigraph_iff.mpr ⟨hx, le_rfl⟩, rfl⟩

end

section

variable [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜]
  [NoMaxOrder 𝕜]

-- Proof sketch: rewrite the projection as `Ioi (0 : 𝕜)`, whose closure is `Ici 0`.
/-- Example 9.0.0.4 (source-facing form): the projection `π₁ '' hyperbolaEpigraph` is not
closed. -/
theorem image_fst_hyperbolaEpigraph_not_closed :
    ¬ IsClosed (π₁ '' hyperbolaEpigraph) := by
  rw [image_fst_hyperbolaEpigraph_eq_Ioi]
  intro hclosed
  have h0 : (0 : 𝕜) ∈ closure (Ioi (0 : 𝕜)) := by
    have hclosure : closure (Ioi (0 : 𝕜)) = Ici (0 : 𝕜) := closure_Ioi (a := (0 : 𝕜))
    rw [hclosure]
    simp
  rw [hclosed.closure_eq] at h0
  simp at h0

end

section

variable [ConditionallyCompleteLattice 𝕜]

-- Proof sketch: this is the local specialization of the global projection/domain bridge
-- `effectiveDomain_verticalInfimum_eq_image_fst`.
/-- Bridge form: the first-coordinate projection of `hyperbolaEpigraph` equals
`dom(verticalInfimum hyperbolaEpigraph)`. -/
theorem image_fst_hyperbolaEpigraph_eq_dom_verticalInfimum :
    π₁ '' hyperbolaEpigraph = dom(verticalInfimum hyperbolaEpigraph) := by
  symm
  simpa [π₁] using
    (effectiveDomain_verticalInfimum_eq_image_fst (F := hyperbolaEpigraph))

-- Proof sketch: use the global bridge
-- `effectiveDomain_verticalInfimum_eq_image_fst`, then the direct projection computation.
/-- The effective domain of `verticalInfimum hyperbolaEpigraph` is exactly `(0, +∞)`. -/
theorem dom_verticalInfimum_hyperbolaEpigraph_eq_Ioi :
    dom(verticalInfimum hyperbolaEpigraph) = Ioi (0 : 𝕜) := by
  calc
    dom(verticalInfimum hyperbolaEpigraph) = π₁ '' hyperbolaEpigraph := by
      exact image_fst_hyperbolaEpigraph_eq_dom_verticalInfimum.symm
    _ = Ioi (0 : 𝕜) := image_fst_hyperbolaEpigraph_eq_Ioi

-- Proof sketch: rewrite `dom(verticalInfimum hyperbolaEpigraph)` as `Ioi (0 : 𝕜)`.
/-- Owner-membership form: `x` belongs to `dom(verticalInfimum hyperbolaEpigraph)` exactly when
`x > 0`. -/
theorem mem_dom_verticalInfimum_hyperbolaEpigraph_iff {x : 𝕜} :
    x ∈ dom(verticalInfimum hyperbolaEpigraph) ↔ 0 < x := by
  rw [dom_verticalInfimum_hyperbolaEpigraph_eq_Ioi]
  simp [mem_Ioi]

end

section

variable [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]

-- Proof sketch: rewrite `dom(verticalInfimum hyperbolaEpigraph)` as the first-coordinate
-- projection via `effectiveDomain_verticalInfimum_eq_image_fst`, then apply the source-facing
-- nonclosedness theorem for that projection.
/-- Example 9.0.0.4 in owner form: `dom(verticalInfimum hyperbolaEpigraph)` is not closed. -/
theorem dom_verticalInfimum_hyperbolaEpigraph_not_closed :
    ¬ IsClosed (dom(verticalInfimum hyperbolaEpigraph)) := by
  simpa [image_fst_hyperbolaEpigraph_eq_dom_verticalInfimum] using
    (image_fst_hyperbolaEpigraph_not_closed : ¬ IsClosed (π₁ '' hyperbolaEpigraph))

end

end
