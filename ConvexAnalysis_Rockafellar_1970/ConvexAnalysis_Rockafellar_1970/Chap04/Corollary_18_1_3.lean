import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_3_3
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_18_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

namespace IsExtreme

section AmbientNonempty

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [SMul R E]

/-- Owner-level properness consequence: if `C'` is a proper extreme subset of `C`, then `C` is
nonempty. -/
theorem ambient_nonempty_of_ne
    {C C' : Set E} (hC' : IsExtreme R C C') (hne : C' ≠ C) :
    C.Nonempty := by
  by_contra hCne
  have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
  apply hne
  rw [hCempty]
  exact Set.Subset.antisymm (by
    intro x hx
    simpa [hCempty] using hC'.subset hx) (Set.empty_subset _)

/-- Strict-inclusion surface of `ambient_nonempty_of_ne` on the primitive owner. -/
theorem ambient_nonempty_of_ssubset
    {C C' : Set E} (hC' : IsExtreme R C C') (hssub : C' ⊂ C) :
    C.Nonempty := by
  exact hC'.ambient_nonempty_of_ne hssub.ne

end AmbientNonempty

end IsExtreme

namespace Set.IsFace

section AmbientNonempty

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {E : Type*} [AddCommMonoid E] [SMul R E]

/-- Face-family notation surface of properness: if `C' ∈ 𝓕[R](C)` and `C' ≠ C`, then `C` is
nonempty. -/
theorem ambient_nonempty_of_ne_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[R](C)) (hne : C' ≠ C) :
    C.Nonempty := by
  exact (mem_faces_iff.mp hC').isExtreme.ambient_nonempty_of_ne hne

/-- Owner-level properness consequence: if `C'` is a proper face of `C`, then `C` is nonempty. -/
theorem ambient_nonempty_of_ne
    {C C' : Set E} (hC' : C'.IsFace R C) (hne : C' ≠ C) :
    C.Nonempty := by
  exact ambient_nonempty_of_ne_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hne

/-- Face-family notation strict-inclusion surface of `ambient_nonempty_of_ne_of_mem_faces`. -/
theorem ambient_nonempty_of_ssubset_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[R](C)) (hssub : C' ⊂ C) :
    C.Nonempty := by
  exact ambient_nonempty_of_ne_of_mem_faces hC' hssub.ne

/-- Strict-inclusion surface of `ambient_nonempty_of_ne` on `Set.IsFace`. -/
theorem ambient_nonempty_of_ssubset
    {C C' : Set E} (hC' : C'.IsFace R C) (hssub : C' ⊂ C) :
    C.Nonempty := by
  exact ambient_nonempty_of_ssubset_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hssub

end AmbientNonempty

end Set.IsFace

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage:

- Primary mathematical domain: faces, relative boundary, and affine dimension in
  finite-dimensional normed spaces over an ordered complete nontrivially normed field.
- `source-facing`: Corollary 18.1.3 says that a proper face of a convex set lies in the relative
  boundary of the ambient set, and therefore has strictly smaller affine dimension.
- `core/canonical`: the primitive owner abstraction is `IsExtreme 𝕜 C C'`, while the
  source-facing bridge owner is `Set.IsFace`; the codomain-side owners are `rb[𝕜](·)` and the
  chapter owner theorem `Convex.affineDim_lt_of_subset_rb`.
- `bridge/view`: first prove the proper-extreme-subset to relative-boundary inclusion on
  `IsExtreme`, then route the affine-dimension clause through the canonical face owner
  `Set.IsFace`.

Domain-style sampling used here:
- `IsExtreme.subset_of_nonempty_inter_ri`;
- `IsExtreme.subset`;
- `rb[𝕜](·)`;
- `intrinsicClosure_diff_intrinsicInterior`;
- `Convex.affineDim_lt_of_subset_rb`.
- Primitive data vs derived API: the primitive owner input is `IsExtreme 𝕜 C C'` for the
  relative-boundary inclusion. The affine-dimension drop is source-facing on `Set.IsFace`, where
  face convexity is carried by the owner itself.
- Layer target: primitive owner theorem on `IsExtreme` for boundary inclusion, then source-facing
  bridge theorems on `Set.IsFace` (including the affine-dimension drop).
- Ambient refinement: the face-to-boundary step already lives on the ordered nontrivially normed
  field layer used by `Theorem_18_1`, and the affine-dimension drop then follows on the stronger
  finite-dimensional ordered-complete layer required by
  `Convex.affineDim_lt_of_subset_rb`.
-/

namespace IsExtreme

section RelativeBoundary

variable [IsStrictOrderedRing 𝕜]

/-- Primitive owner form of Corollary 18.1.3: a proper extreme subset `C'` of `C` lies in the
relative boundary `rb[𝕜](C)` of `C`. -/
-- Proof sketch: if some point of `C'` lay in `ri[𝕜](C)`, then Theorem 18.1 applied to `D = C`
-- would give `C ⊆ C'`. Together with `hC'.subset`, that would force `C' = C`, contradicting
-- properness. Since `C' ⊆ C ⊆ intrinsicClosure 𝕜 C`, disjointness from the relative interior
-- rewrites through `intrinsicClosure_diff_intrinsicInterior`.
theorem subset_rb_of_ne
    {C C' : Set E} (hC' : IsExtreme 𝕜 C C') (hne : C' ≠ C) :
    C' ⊆ rb[𝕜](C) := by
  intro x hxC'
  have hxC : x ∈ C := hC'.subset hxC'
  have hx_not_ri : x ∉ ri[𝕜](C) := by
    intro hxri
    have hC_subset : C ⊆ C' :=
      hC'.subset_of_nonempty_inter_ri subset_rfl ⟨x, hxC', hxri⟩
    exact hne <| Set.Subset.antisymm hC'.subset hC_subset
  rw [← intrinsicClosure_diff_intrinsicInterior]
  exact ⟨subset_intrinsicClosure hxC, hx_not_ri⟩

/-- Properness-on-`⊂` surface for Corollary 18.1.3 on the primitive owner: a strict extreme
subset of `C` lies in `rb[𝕜](C)`. -/
theorem subset_rb_of_ssubset
    {C C' : Set E} (hC' : IsExtreme 𝕜 C C') (hssub : C' ⊂ C) :
    C' ⊆ rb[𝕜](C) := by
  exact hC'.subset_rb_of_ne hssub.ne

end RelativeBoundary

end IsExtreme

namespace Set.IsFace

section RelativeBoundary

variable [IsStrictOrderedRing 𝕜]

/-- Face-family notation form of Corollary 18.1.3: if `C' ∈ 𝓕[𝕜](C)` and `C' ≠ C`, then
`C' ⊆ rb[𝕜](C)`. -/
theorem subset_rb_of_ne_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hne : C' ≠ C) :
    C' ⊆ rb[𝕜](C) := by
  exact (mem_faces_iff.mp hC').isExtreme.subset_rb_of_ne hne

/-- Corollary 18.1.3: a face `C'` of a convex set `C` that is not equal to `C` is contained in the
relative boundary `rb[𝕜](C)` of `C`. -/
theorem subset_rb_of_ne
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hne : C' ≠ C) :
    C' ⊆ rb[𝕜](C) := by
  exact subset_rb_of_ne_of_mem_faces (C := C) (C' := C') (mem_faces_iff.mpr hC') hne

/-- Corollary 18.1.3 on strict inclusion, face-family notation surface. -/
theorem subset_rb_of_ssubset_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hssub : C' ⊂ C) :
    C' ⊆ rb[𝕜](C) := by
  exact subset_rb_of_ne_of_mem_faces hC' hssub.ne

/-- Corollary 18.1.3 on strict inclusion: a strict face of `C` lies in `rb[𝕜](C)`. -/
theorem subset_rb_of_ssubset
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hssub : C' ⊂ C) :
    C' ⊆ rb[𝕜](C) := by
  exact subset_rb_of_ssubset_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hssub

section

variable [OrderTopology 𝕜] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- Face-family notation owner surface: if `C' ∈ 𝓕[𝕜](C)` is proper and `C` is convex, then
`dim[𝕜](C') < dim[𝕜](C)`. -/
theorem affineDim_lt_of_ne_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hC : Convex 𝕜 C) (hne : C' ≠ C) :
    dim[𝕜](C') < dim[𝕜](C) := by
  have hFace : C'.IsFace 𝕜 C := mem_faces_iff.mp hC'
  have hCne : C.Nonempty := ambient_nonempty_of_ne_of_mem_faces hC' hne
  exact Convex.affineDim_lt_of_subset_rb hC hCne hFace.convex
    (subset_rb_of_ne_of_mem_faces hC' hne)

/-- A proper face of a convex set in a finite-dimensional normed `𝕜`-space has strictly smaller
affine dimension than the ambient convex set. -/
theorem affineDim_lt_of_ne
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C) (hne : C' ≠ C) :
    dim[𝕜](C') < dim[𝕜](C) := by
  exact affineDim_lt_of_ne_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hC hne

/-- Face-family notation strict-inclusion surface of `affineDim_lt_of_ne_of_mem_faces`. -/
theorem affineDim_lt_of_ssubset_of_mem_faces
    {C C' : Set E} (hC' : C' ∈ 𝓕[𝕜](C)) (hC : Convex 𝕜 C) (hssub : C' ⊂ C) :
    dim[𝕜](C') < dim[𝕜](C) := by
  exact affineDim_lt_of_ne_of_mem_faces hC' hC hssub.ne

/-- A strict face of a convex set in a finite-dimensional normed `𝕜`-space has strictly smaller
affine dimension than the ambient convex set. -/
theorem affineDim_lt_of_ssubset
    {C C' : Set E} (hC' : C'.IsFace 𝕜 C) (hC : Convex 𝕜 C) (hssub : C' ⊂ C) :
    dim[𝕜](C') < dim[𝕜](C) := by
  exact affineDim_lt_of_ssubset_of_mem_faces (C := C) (C' := C')
    (mem_faces_iff.mpr hC') hC hssub

end

end RelativeBoundary

end Set.IsFace

end
