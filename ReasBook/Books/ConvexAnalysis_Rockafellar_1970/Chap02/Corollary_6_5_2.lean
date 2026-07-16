import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_5_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_10
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.5.2 says that if `C₂` lies in `closure C₁` but is not entirely
  contained in the relative boundary of a convex set `C₁`, then the relative interior of `C₂`
  is contained in the relative interior of `C₁`. The source also states `C₂` convex, but that
  hypothesis is redundant for the owner-form inclusion.
- `core/canonical`: the owner notions are `Convex 𝕜`, `closure`,
  `intrinsicInterior 𝕜`, `intrinsicClosure 𝕜`, and `intrinsicFrontier 𝕜`, together with the
  affine-owner object `AffineSubspace 𝕜 E`; the public theorem should therefore live on the
  `Convex` owner surface, with the chapter notation `ri[𝕜](C)` and `rb[𝕜](C)` and with
  `intrinsicClosure 𝕜 C`
  used on theorem surfaces.
- `bridge/view`: Rockafellar's relative interior and relative boundary are represented on the
  chapter theorem surface by `ri[𝕜](C)` and `rb[𝕜](C)`, over the canonical owners
  `intrinsicInterior 𝕜` and `intrinsicFrontier 𝕜`.
- Domain-style sampling: the relevant canonical/project declarations are `intrinsicFrontier`,
  `intrinsicClosure_diff_intrinsicFrontier`, the chapter bridge
  `mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset`, the
  affine-hull control theorems `subset_affineSpan` and `affineSpan_intrinsicClosure`, together
  with the affine-owner section formulas `AffineSubspace.intrinsicInterior_inter_eq` and
  `AffineSubspace.intrinsicClosure_inter_eq`.
- Primitive data vs derived API: the primitive input data is the convex owner `hC₁`, the
  relative-closure inclusion `C₂ ⊆ intrinsicClosure 𝕜 C₁`, and the witness-level condition
  `(C₂ ∩ ri[𝕜](C₁)).Nonempty`; the source hypothesis
  `¬ C₂ ⊆ rb[𝕜](C₁)` is then a thin bridge to this primitive layer.
- Layer target: this item is `source-facing`, stated directly in the canonical
  `intrinsicInterior`/`intrinsicFrontier` language on the chapter's ambient finite-dimensional
  ordered-complete nontrivially normed-field owner layer, and organized as a `Convex` owner
  theorem.
-/

namespace Convex

/-- Primitive intrinsic-closure owner form for Corollary 6.5.2: if `C₂` lies in
`intrinsicClosure 𝕜 C₁` and `C₂` meets `ri[𝕜](C₁)`, then `ri[𝕜](C₂) ⊆ ri[𝕜](C₁)`. -/
-- Proof sketch: choose `x ∈ C₂ ∩ ri[𝕜](C₁)`. Let
-- `M = affineSpan 𝕜 C₂` and `S = M ∩ C₁`. Then `x ∈ M ∩ ri[𝕜](C₁)`, so
-- Corollary 6.5.1 yields
-- the owner identities `ri[𝕜](S) = M ∩ ri[𝕜](C₁)` and
-- `intrinsicClosure 𝕜 S = M ∩ intrinsicClosure 𝕜 C₁`. Hence
-- `C₂ ⊆ intrinsicClosure 𝕜 S`, while `intrinsicClosure 𝕜 S` has affine span `M`.
-- If `z ∈ ri[𝕜](C₂)`, the relative-interior neighborhood criterion gives a closed
-- ball in `M` around `z` contained in `C₂`, hence in `intrinsicClosure 𝕜 S`, so the same
-- criterion puts `z ∈ ri[𝕜](intrinsicClosure 𝕜 S) = ri[𝕜](S)`. Unwinding the
-- affine-owner identity for `ri[𝕜](S)` gives `z ∈ ri[𝕜](C₁)`.
theorem ri_subset_ri_of_subset_intrinsicClosure
    {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hsubset : C₂ ⊆ intrinsicClosure 𝕜 C₁)
    (hinter : (C₂ ∩ ri[𝕜](C₁)).Nonempty) :
    ri[𝕜](C₂) ⊆ ri[𝕜](C₁) := by
  rcases hinter with ⟨x, hx₂, hx₁⟩
  let M : AffineSubspace 𝕜 E := affineSpan 𝕜 C₂
  let S : Set E := (M : Set E) ∩ C₁
  have hxM : x ∈ (M : Set E) := by
    simpa [M] using subset_affineSpan 𝕜 C₂ hx₂
  have hMri : ((M : Set E) ∩ ri[𝕜](C₁)).Nonempty := ⟨x, hxM, hx₁⟩
  have hSconv : Convex 𝕜 S := by
    simpa [S] using M.convex.inter hC₁
  have hScl : intrinsicClosure 𝕜 S = (M : Set E) ∩ intrinsicClosure 𝕜 C₁ := by
    simpa [S] using M.intrinsicClosure_inter_eq hC₁ hMri
  have hSri : ri[𝕜](S) = (M : Set E) ∩ ri[𝕜](C₁) := by
    simpa [S] using M.intrinsicInterior_inter_eq hC₁ hMri
  have hC₂_clS : C₂ ⊆ intrinsicClosure 𝕜 S := by
    intro z hz
    have hzM : z ∈ (M : Set E) := by
      simpa [M] using subset_affineSpan 𝕜 C₂ hz
    rw [hScl]
    exact ⟨hzM, hsubset hz⟩
  have hspan_clS : affineSpan 𝕜 (intrinsicClosure 𝕜 S) = M := by
    refine le_antisymm ?_ ?_
    · rw [affineSpan_intrinsicClosure]
      exact affineSpan_le_of_subset_coe fun _ hz ↦ hz.1
    · change affineSpan 𝕜 C₂ ≤ affineSpan 𝕜 (intrinsicClosure 𝕜 S)
      exact affineSpan_le_of_subset_coe fun z hz ↦
        subset_affineSpan 𝕜 (intrinsicClosure 𝕜 S) (hC₂_clS hz)
  intro z hz
  obtain ⟨_, ε, hε, hzball⟩ :=
    (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).1 hz
  have hz_clS : z ∈ ri[𝕜](intrinsicClosure 𝕜 S) := by
    refine
      (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).2
        ⟨subset_affineSpan 𝕜 (intrinsicClosure 𝕜 S)
          (hC₂_clS (intrinsicInterior_subset hz)), ε, hε, ?_⟩
    intro y hy
    exact hC₂_clS <| hzball <| by
      refine ⟨hy.1, ?_⟩
      have hyM : y ∈ (M : Set E) := hspan_clS ▸ hy.2
      simpa [M] using hyM
  have hzS : z ∈ ri[𝕜](S) := by
    rw [← hSconv.ri_intrinsicClosure_eq_ri]
    exact hz_clS
  have hzSri : z ∈ (M : Set E) ∩ ri[𝕜](C₁) := by
    simpa [hSri] using hzS
  exact hzSri.2

/-- Corollary 6.5.2, intrinsic-closure source form: if a convex set `C₁`
satisfies `C₂ ⊆ intrinsicClosure 𝕜 C₁` and `C₂` is not contained in the
relative boundary `rb[𝕜](C₁)`, then `ri[𝕜](C₂) ⊆ ri[𝕜](C₁)`. -/
theorem ri_subset_ri_of_subset_intrinsicClosure_of_not_subset_rb
    {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hsubset : C₂ ⊆ intrinsicClosure 𝕜 C₁)
    (hnot_frontier : ¬ C₂ ⊆ rb[𝕜](C₁)) :
    ri[𝕜](C₂) ⊆ ri[𝕜](C₁) := by
  have hinter : (C₂ ∩ ri[𝕜](C₁)).Nonempty := by
    rcases Set.not_subset.mp hnot_frontier with ⟨x, hx₂, hxnot_frontier⟩
    have hxri : x ∈ intrinsicClosure 𝕜 C₁ \ rb[𝕜](C₁) := ⟨hsubset hx₂, hxnot_frontier⟩
    exact ⟨x, hx₂, by simpa [intrinsicClosure_diff_intrinsicFrontier] using hxri⟩
  exact ri_subset_ri_of_subset_intrinsicClosure hC₁ hsubset hinter

/-- Primitive ambient-closure bridge for Corollary 6.5.2: once intrinsic closure agrees with
ambient closure for `C₁`, the source-facing closure hypothesis yields
`ri[𝕜](C₂) ⊆ ri[𝕜](C₁)`. -/
theorem ri_subset_ri_of_subset_closure_of_not_subset_rb_of_intrinsicClosure_eq_closure
    {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hclosure : intrinsicClosure 𝕜 C₁ = closure C₁)
    (hsubset : C₂ ⊆ closure C₁) (hnot_frontier : ¬ C₂ ⊆ rb[𝕜](C₁)) :
    ri[𝕜](C₂) ⊆ ri[𝕜](C₁) := by
  have hsubset' : C₂ ⊆ intrinsicClosure 𝕜 C₁ := by
    intro x hx
    rw [hclosure]
    exact hsubset hx
  exact ri_subset_ri_of_subset_intrinsicClosure_of_not_subset_rb
    hC₁ hsubset' hnot_frontier

/-- Corollary 6.5.2, ambient-closure bridge: if `C₂ ⊆ closure C₁` and `C₂` is not
contained in the relative boundary `rb[𝕜](C₁)`, then `ri[𝕜](C₂) ⊆ ri[𝕜](C₁)`. -/
theorem ri_subset_ri_of_subset_closure_of_not_subset_rb
    {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hsubset : C₂ ⊆ closure C₁)
    (hnot_frontier : ¬ C₂ ⊆ rb[𝕜](C₁)) :
    ri[𝕜](C₂) ⊆ ri[𝕜](C₁) := by
  exact ri_subset_ri_of_subset_closure_of_not_subset_rb_of_intrinsicClosure_eq_closure
    hC₁ (intrinsicClosure_eq_closure 𝕜 C₁) hsubset hnot_frontier

end Convex

end
