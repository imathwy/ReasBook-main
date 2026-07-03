import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_18_4 (from Chap04) -/
section

open scoped Affine Convex Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 18.4 says that every relative interior point of a closed convex set `C`
  lies on a segment whose endpoints are relative-boundary points, provided `C` is neither affine
  nor a closed half of an affine set.
- `core/canonical`: the owner notions are `IsClosed`, `Convex 𝕜`, the canonical relative interior
  `ri[𝕜](C) = intrinsicInterior 𝕜 C`, the canonical relative boundary
  `rb[𝕜](C) = intrinsicFrontier 𝕜 C`, the affine hull `affineSpan 𝕜 C`, the intrinsic
  closed-linear-half-space owner `Set.IsClosedLinearHalfSpace`, the chapter owner
  `Set.IsClosedHalfAffineHull`, and the segment owner `[x₁ -[𝕜] x₂]`.
- `bridge/view`: the textbook exclusion of “a closed half of an affine set” is recorded directly
  by the owner predicate `Set.IsClosedHalfAffineHull`; this keeps theorem surfaces on the
  intrinsic linear-functional half-space layer and removes auxiliary pairing parameters. The
  separate non-affineness hypothesis is
  stated canonically as `¬ affine[𝕜] C`, ruling out the trivial case where this
  intersection is the whole affine hull.
- Primitive data vs derived API: the primitive inputs are the closed convex set `C`, the candidate
  point `y`, and the two exclusion hypotheses for the source-facing segment theorem; the boundary
  endpoints are derived existential data in that conclusion, and the convex-hull identity proved
  afterward is companion `bridge/view` API obtained from the segment statement and the canonical
  `convexHull` owner.
- Domain-style sampling used here: `intrinsicFrontier` from `Text_6_10`,
  `Set.IsClosedLinearHalfSpace` from `Definition_2_0_3`,
  `closed_convex_eq_sInter_closedHalfSpacesContaining` and
  `closed_convex_eq_sInter_closedHalfSpacesContaining_inner` from `Theorem_11_5`,
  `exists_nontrivial_supporting_hyperplane_of_mem_rb` from `Theorem_11_6`,
  `Set.IsSupportingHalfSpace` from `Text_11_3_1`, and the segment owner `[x₁ -[𝕜] x₂]`.
- Layer target: `exists_intrinsicFrontier_points_segment_of_mem_intrinsicInterior` is the
  `source-facing` main item, stated directly in the canonical relative interior/frontier API rather
  than by introducing a wrapper structure for admissible convex sets; the follow-up theorem
  `eq_convexHull_intrinsicFrontier_of_isClosed_of_convex` is a `bridge/view` consequence kept only
  because later chapter results use the canonical `convexHull` owner.
- Ambient refinement: the public hypothesis about “closed halves of an affine set” is expressed on
  the intrinsic linear-functional half-space layer, so the theorem lives on arbitrary topological
  module spaces over ordered fields, with finite-dimensionality localized to the affine hull of
  `C` rather than fixed globally on the ambient space.
-/

/-- Theorem 18.4: if `C` is a closed convex set which is neither affine nor a closed half of its
affine hull, then every relative interior point `y ∈ ri[𝕜](C)` lies on a segment joining two
relative boundary points of `C`. The “closed half of an affine set” condition is formalized by
the owner predicate `Set.IsClosedHalfAffineHull`, while “`C` is not affine” is stated
canonically as `¬ affine[𝕜] C`, with finite-dimensionality carried by
`(affineSpan 𝕜 C).direction`. -/
-- Proof sketch: let `D := rb[𝕜](C)`. Theorem 11.6 shows first that `D` cannot be convex: otherwise
-- `D` would lie in a nontrivial supporting hyperplane of `C`, and the corresponding supporting
-- half-space would force `C` to be either affine or a closed half of its affine hull, contrary to
-- the hypotheses. Hence there exist boundary points whose segment meets `ri[𝕜](C)`.
-- Theorem 6.1 then
-- shows that, along the line through such a pair, the intersection with `C` is exactly a bounded
-- closed segment with boundary endpoints in `rb[𝕜](C)`. Corollary 8.4.1 propagates that bounded-
-- section property to every parallel line, so the line through any given `y ∈ ri[𝕜](C)` parallel to
-- the first one meets `C` in a segment whose two endpoints lie in `rb[𝕜](C)`.
theorem exists_intrinsicFrontier_points_segment_of_mem_intrinsicInterior
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_not_affine : ¬ affine[𝕜] C)
    (hC_not_closed_half : ¬ Set.IsClosedHalfAffineHull 𝕜 C) (y : E)
    (hy : y ∈ ri[𝕜](C)) :
    ∃ x₁ ∈ rb[𝕜](C), ∃ x₂ ∈ rb[𝕜](C), y ∈ [x₁ -[𝕜] x₂] := sorry

end

section

open scoped Convex Rockafellar

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

/-- Canonical bridge API: if every relative interior point of a set belongs to a segment with
relative-boundary endpoints and `rb[𝕜](C) ⊆ C`, then `C` is the convex hull of its relative
boundary. -/
theorem eq_convexHull_intrinsicFrontier_of_intrinsicFrontier_subset_of_convex_of_exists_segment
    {C : Set E} (hrbC : rb[𝕜](C) ⊆ C) (hC_convex : Convex 𝕜 C)
    (hsegment :
      ∀ y ∈ ri[𝕜](C), ∃ x₁ ∈ rb[𝕜](C), ∃ x₂ ∈ rb[𝕜](C), y ∈ [x₁ -[𝕜] x₂]) :
    C = conv[𝕜] (rb[𝕜](C)) := by
  refine subset_antisymm ?_ ?_
  · intro x hxC
    by_cases hxri : x ∈ ri[𝕜](C)
    · rcases hsegment x hxri with
        ⟨x₁, hx₁, x₂, hx₂, hxseg⟩
      exact (convex_convexHull 𝕜 (rb[𝕜](C))).segment_subset
        (subset_convexHull 𝕜 (rb[𝕜](C)) hx₁)
        (subset_convexHull 𝕜 (rb[𝕜](C)) hx₂)
        hxseg
    · have hxbd : x ∈ rb[𝕜](C) := by
        rw [← intrinsicClosure_diff_intrinsicInterior]
        exact ⟨subset_intrinsicClosure hxC, hxri⟩
      exact subset_convexHull 𝕜 (rb[𝕜](C)) hxbd
  · exact convexHull_min hrbC hC_convex

end

section

open scoped Affine Convex Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- Derived bridge from Theorem 18.4: under the same hypotheses, the closed convex set `C` is the
convex hull of its relative boundary `intrinsicFrontier 𝕜 C`. -/
theorem eq_convexHull_intrinsicFrontier_of_isClosed_of_convex
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_not_affine : ¬ affine[𝕜] C)
    (hC_not_closed_half : ¬ Set.IsClosedHalfAffineHull 𝕜 C) :
    C = conv[𝕜] (rb[𝕜](C)) := by
  refine eq_convexHull_intrinsicFrontier_of_intrinsicFrontier_subset_of_convex_of_exists_segment
      (intrinsicFrontier_subset hC_closed) hC_convex ?_
  intro y hy
  exact exists_intrinsicFrontier_points_segment_of_mem_intrinsicInterior
    hC_closed hC_convex hC_not_affine hC_not_closed_half y hy

end
