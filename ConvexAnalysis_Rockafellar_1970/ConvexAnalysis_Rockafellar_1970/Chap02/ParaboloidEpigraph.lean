import Mathlib

-- Declarations for this shared source-facing owner will be reused by multiple items.

open Set

section Ordered

variable {𝕜 : Type*} [LE 𝕜] [Pow 𝕜 ℕ]

/-!
Source/core/bridge triage:

- `source-facing`: the closed convex paraboloid epigraph `{(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` is a recurring
  concrete set used in Chapter 2 and later again in Chapter 4 as a standard counterexample.
- `core/canonical`: the ambient owner abstractions are mathlib's `Set`, `IsClosed`, and
  `Convex 𝕜`; no extra wrapper object is mathematically needed.
- `bridge/view`: the coordinate inequality `ξ₁² ≤ ξ₂` is the pointwise membership view of the set.

Primitive data vs derived API:
- primitive data: the set `paraboloidEpigraph : Set (𝕜 × 𝕜)`;
- derived API: the membership rewrite and convexity statement.

Layer target: this file is the shared `source-facing` owner for the concrete paraboloid epigraph.
Downstream files should reuse it instead of re-declaring parallel copies.
-/

/-- The paraboloid epigraph `{(ξ₁, ξ₂) | ξ₂ ≥ ξ₁²}` in `𝕜²`. -/
def paraboloidEpigraph : Set (𝕜 × 𝕜) :=
  {ξ | ξ.1 ^ 2 ≤ ξ.2}

/-- Canonical set-of view of the paraboloid epigraph owner. -/
@[simp] theorem paraboloidEpigraph_eq_setOf_sq_le :
    (paraboloidEpigraph : Set (𝕜 × 𝕜)) = {ξ | ξ.1 ^ 2 ≤ ξ.2} :=
  rfl

/-- Membership in `paraboloidEpigraph` is exactly the defining coordinate inequality
`ξ₂ ≥ ξ₁²`. -/
theorem mem_paraboloidEpigraph_iff {ξ : 𝕜 × 𝕜} :
    ξ ∈ paraboloidEpigraph ↔ ξ.1 ^ 2 ≤ ξ.2 :=
  Iff.rfl

section OrderedCommRing

variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The paraboloid epigraph is convex. -/
-- Proof sketch: it is the epigraph of the convex function `x ↦ x^2`.
theorem paraboloidEpigraph_convex :
    Convex 𝕜 (paraboloidEpigraph : Set (𝕜 × 𝕜)) := by
  simpa [paraboloidEpigraph, and_true] using
    (ConvexOn.convex_epigraph
      (Even.convexOn_pow (𝕜 := 𝕜) (n := 2) (by decide)))

end OrderedCommRing

end Ordered

section OrderedTopologicalRing

variable {𝕜 : Type*}
    [Ring 𝕜] [LinearOrder 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsTopologicalRing 𝕜]

/-- The paraboloid epigraph is closed. -/
-- Proof sketch: it is the inverse image of the closed ray `Set.Ici 0` under the continuous
-- function `ξ ↦ ξ.2 - ξ.1 ^ 2`.
theorem paraboloidEpigraph_isClosed :
    IsClosed (paraboloidEpigraph : Set (𝕜 × 𝕜)) := by
  simpa [paraboloidEpigraph] using
    (isClosed_le (continuous_fst.pow 2) continuous_snd)

end OrderedTopologicalRing
