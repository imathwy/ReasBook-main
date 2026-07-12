import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_18_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 18.1.2 says that two faces of `C` are equal whenever their relative
  interiors meet.
- `core/canonical`: the primitive owner is `IsExtreme 𝕜 C ·`, while the source-facing owners are
  chapter face-family membership `C' ∈ 𝓕[𝕜](C)` and `Set.IsFace`; relative interior is written on
  theorem surfaces as `ri[𝕜](·)`.
- `bridge/view`: Rockafellar's face language is represented by `C' ∈ 𝓕[𝕜](C)` and
  `C'' ∈ 𝓕[𝕜](C)`, bridged to the primitive owner through `mem_faces_iff` and
  `hC'.isExtreme`/`hC''.isExtreme`.
- Domain-style sampling used here:
  `IsExtreme.eq_of_nonempty_inter_ri`,
  `IsExtreme.subset_of_nonempty_inter_ri`,
  `IsExtreme.subset`,
  `ri[𝕜](·)`,
  and `intrinsicInterior_subset`.
- Primitive data vs derived API: the primitive inputs are the two extreme-subset hypotheses and
  the source-level nonempty relative-interior intersection
  `(ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty`. Face hypotheses are bridge data that provide the
  corresponding extreme-subset hypotheses.
- Layer target: primitive theorem in `IsExtreme`, then source-facing bridge theorems on
  `𝓕[𝕜](C)` and `Set.IsFace`.

The source assumes `C` is convex, but for this equality statement the proof only uses the two face
hypotheses themselves, so no separate ambient convexity binder is needed.

Ambient refinement: the proof only uses the owner theorem from `Theorem_18_1` and
`intrinsicInterior_subset`, so neither finite-dimensionality, nor the specialization `𝕜 = ℝ`, nor
the concrete model `EuclideanSpace ℝ (Fin n)` is part of the mathematical content.
-/

namespace IsExtreme

variable {C C' C'' : Set E}

/-- Primitive one-sided owner form behind Corollary 18.1.2: if the relative interiors of two
extreme subsets of `C` meet, then the first subset is contained in the second. -/
private theorem subset_of_nonempty_inter_ri_ri_aux
    (hC' : IsExtreme 𝕜 C C') (hC'' : IsExtreme 𝕜 C C'')
    (hri : (ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty) :
    C' ⊆ C'' := by
  exact hC''.subset_of_nonempty_inter_ri hC'.subset
    (hri.mono fun x hx ↦ ⟨intrinsicInterior_subset hx.2, hx.1⟩)

/-- Primitive owner form behind Corollary 18.1.2: if the relative interiors of two extreme
subsets meet, then the subsets are equal. -/
theorem eq_of_nonempty_inter_ri
    (hC' : IsExtreme 𝕜 C C') (hC'' : IsExtreme 𝕜 C C'')
    (hri : (ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty) :
    C' = C'' := by
  refine subset_antisymm ?_ ?_
  · exact subset_of_nonempty_inter_ri_ri_aux hC' hC'' hri
  · exact subset_of_nonempty_inter_ri_ri_aux hC'' hC'
      (hri.mono fun x hx ↦ ⟨hx.2, hx.1⟩)

end IsExtreme

namespace Set.IsFace

variable {C C' C'' : Set E}

/-- Corollary 18.1.2 on the chapter face-family surface: if `C'` and `C''` are members of
`𝓕[𝕜](C)` and their relative interiors have a point in common, then `C' = C''`. -/
theorem eq_of_nonempty_inter_ri_of_mem_faces
    (hC' : C' ∈ 𝓕[𝕜](C)) (hC'' : C'' ∈ 𝓕[𝕜](C))
    (hri : (ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty) :
    C' = C'' := by
  exact (mem_faces_iff.mp hC').isExtreme.eq_of_nonempty_inter_ri
    (mem_faces_iff.mp hC'').isExtreme hri

/-- Corollary 18.1.2: if `C'` and `C''` are faces of `C`, represented by `C'.IsFace 𝕜 C` and
`C''.IsFace 𝕜 C`, and their relative interiors have a point in common, then `C' = C''`. -/
-- Proof sketch: route through the chapter face-family notation theorem
-- `eq_of_nonempty_inter_ri_of_mem_faces`.
theorem eq_of_nonempty_inter_ri
    (hC' : C'.IsFace 𝕜 C) (hC'' : C''.IsFace 𝕜 C)
    (hri : (ri[𝕜](C') ∩ ri[𝕜](C'')).Nonempty) :
    C' = C'' := by
  exact eq_of_nonempty_inter_ri_of_mem_faces (mem_faces_iff.mpr hC') (mem_faces_iff.mpr hC'') hri

end Set.IsFace

end
