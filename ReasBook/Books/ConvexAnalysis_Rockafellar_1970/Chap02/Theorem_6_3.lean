import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.3 states two closure/relative-interior identities for a convex set
  in `ℝ^n`.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicClosure 𝕜`, and
  `intrinsicInterior 𝕜`.
- `bridge/view`: Rockafellar's `ri C` is represented canonically by `intrinsicInterior ℝ C`.
- Domain-style sampling used here: the chapter owner notation `ri[𝕜](C)` from `Text_6_8`,
  `intrinsicInterior`, `intrinsicClosure`, `intrinsicClosure_eq_closure`,
  `Set.Nonempty.intrinsicInterior`,
  `Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior`,
  `Convex.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem`,
  and the intrinsic affine-hull owner theorem `affineSpan_intrinsicClosure`.
- Primitive data vs derived API: the primitive owner data is just `hC : Convex 𝕜 C`; both
  closure/relative-interior identities are derived API, so they belong on the `Convex`
  owner abstraction rather than as parallel global wrappers.
- Layer target: the intrinsic closure/interior identities are the primary public owner theorems;
  the ambient `closure` statements are finite-dimensional bridge corollaries.
-/

namespace Convex

open AffineMap

variable {𝕜 E : Type*} {C : Set E}

section Primitive

variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem right_mem_intrinsicClosure_openSegment (x y : E) :
    y ∈ intrinsicClosure 𝕜 (openSegment 𝕜 x y) := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  refine ⟨segment_subset_closure_openSegment (right_mem_segment 𝕜 x y), ?_⟩
  let u : E := lineMap x y ((1 : 𝕜) / 2)
  let v : E := lineMap u y ((1 : 𝕜) / 2)
  have hu : u ∈ openSegment 𝕜 x y := by
    dsimp [u]
    exact lineMap_mem_openSegment 𝕜 x y <| by constructor <;> norm_num
  have hv : v ∈ openSegment 𝕜 x y := by
    dsimp [v, u]
    rw [lineMap_lineMap_left]
    exact lineMap_mem_openSegment 𝕜 x y <| by constructor <;> norm_num
  have hy_line : y ∈ line[𝕜, u, v] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(2 : 𝕜), ?_⟩
    dsimp [v]
    rw [lineMap_lineMap_right]
    norm_num
  exact
    (affineSpan_pair_le_of_mem_of_mem
      (subset_affineSpan 𝕜 (openSegment 𝕜 x y) hu)
      (subset_affineSpan 𝕜 (openSegment 𝕜 x y) hv)) hy_line

/-- Primitive intrinsic owner form behind Theorem 6.3 (1): if `ri[𝕜](C)` is nonempty, then taking
intrinsic closure after relative interior leaves intrinsic closure unchanged. -/
theorem intrinsicClosure_ri_eq_intrinsicClosure_of_nonempty (hC : Convex 𝕜 C)
    (hri : (ri[𝕜](C)).Nonempty) :
    intrinsicClosure 𝕜 (ri[𝕜](C)) = intrinsicClosure 𝕜 C := by
  refine subset_antisymm (intrinsicClosure_mono intrinsicInterior_subset) ?_
  rcases hri with ⟨x, hx⟩
  intro y hy
  have hseg : openSegment 𝕜 x y ⊆ ri[𝕜](C) :=
    hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hx hy
  exact intrinsicClosure_mono hseg <| right_mem_intrinsicClosure_openSegment (𝕜 := 𝕜) x y

omit [OrderTopology 𝕜] in
/-- Theorem 6.3 (2), intrinsic owner form with explicit nonemptiness of `ri[𝕜](C)`. -/
theorem ri_intrinsicClosure_eq_ri_of_nonempty (hC : Convex 𝕜 C) (hri : (ri[𝕜](C)).Nonempty) :
    ri[𝕜](intrinsicClosure 𝕜 C) = ri[𝕜](C) := by
  refine subset_antisymm ?_ ?_
  · rcases hri with ⟨x, hx⟩
    intro z hz
    have hxcl : x ∈ intrinsicClosure 𝕜 C := subset_intrinsicClosure (intrinsicInterior_subset hx)
    rcases
        Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior
          (C := intrinsicClosure 𝕜 C) hz x hxcl with
      ⟨μ, hμ, hy⟩
    have hμ_inv : 0 < μ⁻¹ := inv_pos.mpr (lt_trans zero_lt_one hμ)
    have hμ_inv_lt_one : μ⁻¹ < 1 := by
      rw [inv_lt_one₀]
      · linarith
      · linarith
    have hz_seg : z ∈ openSegment 𝕜 x (lineMap x z μ) := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨μ⁻¹, ⟨hμ_inv, hμ_inv_lt_one⟩, ?_⟩
      have hμ0 : μ ≠ 0 := (lt_trans zero_lt_one hμ).ne'
      calc
        lineMap x (lineMap x z μ) μ⁻¹ = lineMap x z (μ⁻¹ * μ) := by simp
        _ = lineMap x z (1 : 𝕜) := by rw [inv_mul_cancel₀ hμ0]
        _ = z := lineMap_apply_one x z
    exact Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hC hx hy
      hz_seg
  · intro z hz
    rw [intrinsicInterior] at hz ⊢
    rw [affineSpan_intrinsicClosure (𝕜 := 𝕜) C]
    rcases hz with ⟨y, hy, rfl⟩
    exact ⟨y, interior_mono (Set.preimage_mono subset_intrinsicClosure) hy, rfl⟩

end Primitive

section FiniteDimensionalBridge

variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- Theorem 6.3 (1), intrinsic owner form: for a convex set `C`, taking intrinsic closure after
relative interior leaves the intrinsic closure unchanged. -/
theorem intrinsicClosure_ri_eq_intrinsicClosure (hC : Convex 𝕜 C) :
    intrinsicClosure 𝕜 (ri[𝕜](C)) = intrinsicClosure 𝕜 C := by
  obtain rfl | hCne := Set.eq_empty_or_nonempty C
  · simp
  exact hC.intrinsicClosure_ri_eq_intrinsicClosure_of_nonempty (hC.intrinsicInterior_nonempty hCne)

/-- Theorem 6.3 (1), ambient-closure bridge: in finite-dimensional spaces,
`closure (ri[𝕜](C)) = closure C`. -/
theorem closure_intrinsicInterior_eq_closure (hC : Convex 𝕜 C) :
    closure (ri[𝕜](C)) = closure C := by
  simpa [intrinsicClosure_eq_closure 𝕜 (ri[𝕜](C)),
    intrinsicClosure_eq_closure 𝕜 C] using
    intrinsicClosure_ri_eq_intrinsicClosure hC

/-- Theorem 6.3 (2), intrinsic owner form: for a convex set `C`, taking relative interior after
intrinsic closure leaves the relative interior unchanged. -/
theorem ri_intrinsicClosure_eq_ri (hC : Convex 𝕜 C) :
    ri[𝕜](intrinsicClosure 𝕜 C) = ri[𝕜](C) := by
  obtain rfl | hCne := Set.eq_empty_or_nonempty C
  · simp
  exact hC.ri_intrinsicClosure_eq_ri_of_nonempty (hC.intrinsicInterior_nonempty hCne)

/-- Theorem 6.3 (2), ambient-closure bridge: in finite-dimensional spaces,
`ri[𝕜](closure C) = ri[𝕜](C)`. -/
theorem intrinsicInterior_closure_eq_intrinsicInterior (hC : Convex 𝕜 C) :
    ri[𝕜](closure C) = ri[𝕜](C) := by
  simpa [intrinsicClosure_eq_closure 𝕜 C] using
    ri_intrinsicClosure_eq_ri hC

end FiniteDimensionalBridge

end Convex

end
