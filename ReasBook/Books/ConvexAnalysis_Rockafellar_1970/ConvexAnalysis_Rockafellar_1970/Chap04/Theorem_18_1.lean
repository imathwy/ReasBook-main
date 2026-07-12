import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- Primary mathematical domain: convex faces and relative interior over an ordered normed field.
- `source-facing`: Theorem 18.1 says that if a subset `D ⊆ C` has relative interior meeting a
  face `C'` of `C`, then the whole of `D` lies in that face.
- `core/canonical`: the primitive owner abstraction is the extreme-subset predicate
  `IsExtreme 𝕜 C C'` together with open-segment membership from points of `D`; the
  source-facing theorem is then
  obtained by the chapter relative-interior notation `ri[𝕜](D) = intrinsicInterior 𝕜 D`.
- `bridge/view`: Rockafellar's face language is represented by `C'.IsFace 𝕜 C`, while
  `ri[𝕜](D)` is represented by `intrinsicInterior 𝕜 D`; the segment prolongation bridge is
  supplied by the project owner theorem
  `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior`.
- Domain-style sampling used here:
  `Set.IsFace` from `Defn_18_1`,
  `IsExtreme.left_mem_of_mem_openSegment`,
  `IsExtreme.right_mem_of_mem_openSegment`,
  `ri[𝕜](·)`,
  `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior`,
  and `lineMap_mem_openSegment`.
- Primitive data vs derived API: the primitive owner theorem uses the extreme-subset hypothesis
  `IsExtreme 𝕜 C C'`, containment `D ⊆ C`, and the open-segment witness hypothesis
  `∀ x ∈ D, ∃ y ∈ D, z ∈ openSegment 𝕜 x y`; the relative-interior theorem is a bridge obtained
  from this primitive owner layer by
  `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior`.
- Layer target: primitive owner theorem on `IsExtreme`, then bridge theorems on
  `ri[𝕜](·)` and `Set.IsFace`.
- Redundant-source-assumption check: the textbook states the result for faces of a convex set, but
  the proof only uses the owner face hypothesis `C'.IsFace 𝕜 C`, the containment `D ⊆ C`,
  and the relative-interior neighborhood at a meeting point. No separate ambient convexity binder
  on `C` changes the mathematical content here, so the refined statement omits it.
- Ambient refinement: the statement only uses the owner face and relative-interior APIs together
  with the Chapter 2 prolongation theorem, so the ambient scalar does not need to be fixed to
  `ℝ`. Specializing `𝕜 = ℝ` recovers the textbook presentation.
-/

namespace IsExtreme

/-- Primitive owner form behind Theorem 18.1: if `C'` is an extreme subset of `C`, `D ⊆ C`,
`z ∈ C'`, and each `x ∈ D` can be joined to another `y ∈ D` with `z` on the open segment
`openSegment 𝕜 x y`, then `D ⊆ C'`. -/
theorem subset_of_forall_exists_mem_openSegment
    {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
    {C C' D : Set E} (hC' : IsExtreme 𝕜 C C') (hDC : D ⊆ C) {z : E} (hzC' : z ∈ C')
    (hseg : ∀ x ∈ D, ∃ y ∈ D, z ∈ openSegment 𝕜 x y) :
    D ⊆ C' := by
  intro x hxD
  rcases hseg x hxD with ⟨y, hyD, hzSeg⟩
  exact hC'.left_mem_of_mem_openSegment (hDC hxD) (hDC hyD) hzC' hzSeg

section IntrinsicInteriorBridge

open AffineMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Primitive witness form of Theorem 18.1 on the `IsExtreme` owner: if
`z ∈ C' ∩ ri[𝕜](D)`, then `D ⊆ C'`. -/
theorem subset_of_mem_inter_ri
    {C C' D : Set E} (hC' : IsExtreme 𝕜 C C') (hDC : D ⊆ C) {z : E}
    (hz : z ∈ C' ∩ ri[𝕜](D)) :
    D ⊆ C' := by
  refine hC'.subset_of_forall_exists_mem_openSegment hDC hz.1 ?_
  intro x hxD
  rcases Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior hz.2 x hxD with
    ⟨μ, hμ, hyD⟩
  have hμpos : 0 < μ := zero_lt_one.trans hμ
  have hμ0 : μ ≠ 0 := hμpos.ne'
  have hμInv : μ⁻¹ ∈ Set.Ioo (0 : 𝕜) 1 := by
    exact ⟨inv_pos.mpr hμpos, (inv_lt_one₀ hμpos).2 hμ⟩
  have hzSeg : z ∈ openSegment 𝕜 x (lineMap x z μ) := by
    simpa [hμ0] using
      (lineMap_mem_openSegment 𝕜 x (lineMap x z μ) hμInv :
        lineMap x (lineMap x z μ) μ⁻¹ ∈ openSegment 𝕜 x (lineMap x z μ))
  exact ⟨lineMap x z μ, hyD, hzSeg⟩

/-- Primitive owner form of Theorem 18.1: an extreme subset `C'` of `C` contains every subset
`D ⊆ C` whose relative interior meets `C'`. -/
theorem subset_of_nonempty_inter_ri
    {C C' D : Set E} (hC' : IsExtreme 𝕜 C C') (hDC : D ⊆ C)
    (hmeet : (C' ∩ ri[𝕜](D)).Nonempty) :
    D ⊆ C' := by
  rcases hmeet with ⟨z, hz⟩
  exact hC'.subset_of_mem_inter_ri hDC hz

end IntrinsicInteriorBridge

end IsExtreme

namespace Set.IsFace

section IntrinsicInteriorBridge

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! `source-facing` theorem surface in face-family notation. -/
/-- Theorem 18.1 on the face-family surface: if `C' ∈ 𝓕[𝕜](C)` and a subset `D ⊆ C` has
relative interior meeting `C'`, then `D ⊆ C'`. -/
theorem subset_of_nonempty_inter_ri_of_mem_faces
    {C C' D : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hDC : D ⊆ C)
    (hmeet : (C' ∩ ri[𝕜](D)).Nonempty) :
    D ⊆ C' := by
  exact (mem_faces_iff.mp hC').isExtreme.subset_of_nonempty_inter_ri hDC hmeet

-- Proof sketch: pass from face language to its primitive owner payload `hC'.isExtreme`, then
-- apply `IsExtreme.subset_of_nonempty_inter_ri`.
/-- Theorem 18.1: if `C'` is a face of `C`, represented by `C'.IsFace 𝕜 C`, and a subset
`D ⊆ C` has relative interior `ri[𝕜](D)` meeting `C'`, then `D ⊆ C'`. The source
also assumes `C` convex, but that ambient convexity hypothesis is redundant for this owner-level
statement. -/
theorem subset_of_nonempty_inter_ri
    {C C' D : Set E} (hC' : C'.IsFace 𝕜 C) (hDC : D ⊆ C)
    (hmeet : (C' ∩ ri[𝕜](D)).Nonempty) :
    D ⊆ C' := by
  exact subset_of_nonempty_inter_ri_of_mem_faces (C := C) (C' := C') (D := D)
    (mem_faces_iff.mpr hC') hDC hmeet

end IntrinsicInteriorBridge
end Set.IsFace

end
