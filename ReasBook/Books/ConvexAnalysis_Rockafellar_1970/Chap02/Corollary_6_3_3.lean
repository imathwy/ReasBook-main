import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_10
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AffineSubspace
open scoped Rockafellar

section

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.3.3 says that a convex subset of the relative boundary of a
  nonempty convex set has strictly smaller affine dimension than the ambient set.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicFrontier 𝕜`,
  `ri[𝕜](C)`, and the chapter owner `Set.affineDim`.
- `bridge/view`: Rockafellar's relative boundary and relative interior are represented by
  `rb[𝕜](C)` and `ri[𝕜](C)`.
- Domain-style sampling used here: `Convex.intrinsicInterior_nonempty`,
  `Convex.ri_intrinsicClosure_eq_ri`,
  `mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset`,
  `Set.exists_simplex_points_subset_affineDim_eq`, and
  `Affine.Simplex.affineDim_le_of_points_subset`.
- Primitive data vs derived API: the core bridge theorem isolates the primitive closure/interior
  inclusion `ri[𝕜](intrinsicClosure 𝕜 C) ⊆ ri[𝕜](C)`, nonemptiness of `ri[𝕜](C')`, and
  `C' ⊆ rb[𝕜](C)`; convexity/nonemptiness assumptions are deferred to a thin source-facing
  wrapper.
- Layer target: this item has a primitive bridge theorem at a weaker affine-torsor metric layer,
  with a source-facing convex finite-dimensional wrapper on the chapter's ordered-complete
  nontrivially normed field layer.
-/

namespace Convex

section Primitive

variable {𝕜 V P : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [PseudoMetricSpace P] [AddTorsor V P] [FiniteDimensional 𝕜 V]

/-- If `ri[𝕜](C')` is nonempty, `C' ⊆ intrinsicClosure 𝕜 C`, and `C'` has the same affine
dimension as `C`, then `C'` meets `ri[𝕜](intrinsicClosure 𝕜 C)`. -/
private theorem inter_intrinsicInterior_nonempty_of_subset_intrinsicClosure_of_affineDim_eq
    {C C' : Set P} (hC'ri : (ri[𝕜](C')).Nonempty)
    (hsubset : C' ⊆ intrinsicClosure 𝕜 C) (hdim : dim[𝕜](C') = dim[𝕜](C)) :
    (C' ∩ ri[𝕜](intrinsicClosure 𝕜 C)).Nonempty := by
  obtain ⟨x, hxri⟩ := hC'ri
  have hxC' : x ∈ C' := intrinsicInterior_subset hxri
  have hspan : affineSpan 𝕜 C' = affineSpan 𝕜 C := by
    have hle : affineSpan 𝕜 C' ≤ affineSpan 𝕜 C := by
      have hle' : affineSpan 𝕜 C' ≤ affineSpan 𝕜 (intrinsicClosure 𝕜 C) :=
        affineSpan_mono 𝕜 hsubset
      exact hle'.trans_eq (affineSpan_intrinsicClosure (𝕜 := 𝕜) C)
    have hspan_nonempty : (affineSpan 𝕜 C' : Set P).Nonempty := by
      exact ⟨x, subset_affineSpan 𝕜 C' hxC'⟩
    have hC'bot : affineSpan 𝕜 C' ≠ ⊥ :=
      (AffineSubspace.nonempty_iff_ne_bot (affineSpan 𝕜 C')).1 hspan_nonempty
    have hCbot : affineSpan 𝕜 C ≠ ⊥ := by
      intro hCbot
      exact hC'bot <| eq_bot_iff.mpr <| hCbot ▸ hle
    change
      AffineSubspace.affineDim (affineSpan 𝕜 C') =
        AffineSubspace.affineDim (affineSpan 𝕜 C) at hdim
    rw [AffineSubspace.affineDim, AffineSubspace.affineDim, if_neg hC'bot, if_neg hCbot] at hdim
    have hdir_eq : (affineSpan 𝕜 C').direction = (affineSpan 𝕜 C).direction := by
      apply Submodule.eq_of_le_of_finrank_eq
      · exact AffineSubspace.direction_le hle
      · exact_mod_cast hdim
    exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_eq hspan_nonempty hle
  obtain ⟨_, ε, hε, hxball⟩ :=
    (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).1 hxri
  have hxri_closure : x ∈ ri[𝕜](intrinsicClosure 𝕜 C) := by
    refine
      (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).2
        ⟨subset_affineSpan 𝕜 (intrinsicClosure 𝕜 C) (hsubset (intrinsicInterior_subset hxri)),
          ε, hε, ?_⟩
    intro y hy
    exact hsubset <| hxball <| by
      have hySpan : y ∈ affineSpan 𝕜 C := by
        exact (affineSpan_intrinsicClosure (𝕜 := 𝕜) C) ▸ hy.2
      refine ⟨hy.1, ?_⟩
      simpa [hspan] using hySpan
  exact ⟨x, hxC', hxri_closure⟩

/-- Primitive bridge form of Corollary 6.3.3: if `ri[𝕜](C')` is nonempty,
`C' ⊆ rb[𝕜](C)`, and `ri[𝕜](intrinsicClosure 𝕜 C) ⊆ ri[𝕜](C)`, then
`C'` has strictly smaller affine dimension than `C`. -/
-- Proof sketch: first note that `C' ⊆ intrinsicClosure 𝕜 C`, so every simplex contained in `C'`
-- is also contained in `intrinsicClosure 𝕜 C`; Theorem 2.4 therefore gives
-- `C'.affineDim ≤ C.affineDim`. If equality
-- held, then `C'` and `C` would have the same affine span. A relative-interior point of `C'`
-- would then satisfy the closed-ball criterion in the common affine span and hence lie in
-- `ri[𝕜](intrinsicClosure 𝕜 C) ⊆ ri[𝕜](C)`, contradicting `C' ⊆ rb[𝕜](C)`.
theorem affineDim_lt_of_subset_rb_of_ri_intrinsicClosure_subset_ri
    {C C' : Set P} (hC'ri : (ri[𝕜](C')).Nonempty)
    (hsubset : C' ⊆ rb[𝕜](C))
    (hri : ri[𝕜](intrinsicClosure 𝕜 C) ⊆ ri[𝕜](C)) :
    dim[𝕜](C') < dim[𝕜](C) := by
  have hC'ne : C'.Nonempty := hC'ri.mono intrinsicInterior_subset
  have hsubset_iclosure : C' ⊆ intrinsicClosure 𝕜 C := by
    exact hsubset.trans <| by
      exact (intrinsicFrontier_subset_intrinsicClosure :
        rb[𝕜](C) ⊆ intrinsicClosure 𝕜 C)
  have hle : dim[𝕜](C') ≤ dim[𝕜](C) := by
    rcases C'.exists_simplex_points_subset_affineDim_eq (𝕜 := 𝕜) hC'ne with
      ⟨n, hC'dim, s, hs⟩
    calc
      dim[𝕜](C') = n := hC'dim
      _ ≤ dim[𝕜](intrinsicClosure 𝕜 C) := by
        exact s.affineDim_le_of_points_subset (hs.trans hsubset_iclosure)
      _ = dim[𝕜](C) := by
        change AffineSubspace.affineDim (affineSpan 𝕜 (intrinsicClosure 𝕜 C)) =
          AffineSubspace.affineDim (affineSpan 𝕜 C)
        exact congrArg (fun A : AffineSubspace 𝕜 P => AffineSubspace.affineDim A)
          (affineSpan_intrinsicClosure (𝕜 := 𝕜) C)
  by_contra hlt
  have hdim : dim[𝕜](C') = dim[𝕜](C) := le_antisymm hle (not_lt.mp hlt)
  rcases inter_intrinsicInterior_nonempty_of_subset_intrinsicClosure_of_affineDim_eq
      hC'ri hsubset_iclosure hdim with ⟨x, hxC', hxri_closure⟩
  have hxri : x ∈ ri[𝕜](C) := by
    exact hri hxri_closure
  have hxnot : x ∉ rb[𝕜](C) := by
    have hxpair : x ∈ intrinsicClosure 𝕜 C \ rb[𝕜](C) := by
      simpa [intrinsicClosure_diff_intrinsicFrontier] using hxri
    exact hxpair.2
  exact hxnot (hsubset hxC')

end Primitive

section SourceFacing

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Source-facing owner form of Corollary 6.3.3 at the canonical intrinsic-owner layer:
if `C` is convex with nonempty `ri[𝕜](C)`, and `ri[𝕜](C')` is nonempty with
`C' ⊆ rb[𝕜](C)`, then `C'` has strictly smaller affine dimension than `C`. -/
theorem affineDim_lt_of_subset_rb_of_ri_nonempty
    {C C' : Set E} (hC : Convex 𝕜 C) (hCri : (ri[𝕜](C)).Nonempty)
    (hC'ri : (ri[𝕜](C')).Nonempty)
    (hsubset : C' ⊆ rb[𝕜](C)) :
    dim[𝕜](C') < dim[𝕜](C) := by
  exact affineDim_lt_of_subset_rb_of_ri_intrinsicClosure_subset_ri hC'ri hsubset (by
    intro x hx
    exact hC.ri_intrinsicClosure_eq_ri_of_nonempty hCri ▸ hx)

variable [OrderTopology 𝕜] [CompleteSpace 𝕜]

/-- Corollary 6.3.3: if `C'` is a convex subset of the relative boundary
`rb[𝕜](C)` of a nonempty convex set `C` in a finite-dimensional normed space over an ordered
complete nontrivially normed field `𝕜`, then `C'` has strictly smaller affine dimension than `C`. -/
theorem affineDim_lt_of_subset_rb
    {C C' : Set E} (hC : Convex 𝕜 C) (hCne : C.Nonempty) (hC' : Convex 𝕜 C')
    (hsubset : C' ⊆ rb[𝕜](C)) :
    dim[𝕜](C') < dim[𝕜](C) := by
  obtain rfl | hC'ne := Set.eq_empty_or_nonempty C'
  · rcases C.exists_simplex_points_subset_affineDim_eq (𝕜 := 𝕜) hCne with
      ⟨n, hCdim, s, hs⟩
    have hEmpty : dim[𝕜]((∅ : Set E)) = -1 := by
      simp [Set.affineDim, AffineSubspace.affineDim]
    rw [hEmpty, hCdim]
    have hn : (0 : ℤ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    linarith
  exact affineDim_lt_of_subset_rb_of_ri_nonempty hC
    (hC.intrinsicInterior_nonempty hCne)
    (hC'.intrinsicInterior_nonempty hC'ne) hsubset

end SourceFacing

end Convex

end
