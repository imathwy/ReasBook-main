import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

section IntrinsicClosure

local notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

variable {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.5 (1) gives an intersection formula for the closure of convex subsets
  of a finite-dimensional ambient space whose relative interiors share a common point; the owner
  theorem below records the more primitive intrinsic-closure identity at the ordered topological
  `𝕜`-module layer, with the ordinary closure statement recovered later as its finite-dimensional
  corollary.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicClosure 𝕜`,
  `intrinsicInterior 𝕜`, and the indexed intersection operator `iInter`; the chapter's
  owner-style derived API for convex sets is organized under `namespace Convex`.
- `bridge/view`: Rockafellar's `ri Cᵢ` is represented by mathlib's canonical
  `intrinsicInterior 𝕜 (C i)`. In finite-dimensional normed spaces, the ambient closure statement
  is the corollary obtained from the intrinsic-closure owner theorem via
  `intrinsicClosure_eq_closure`.
- Domain-style sampling used here: `intrinsicClosure`, `intrinsicClosure_eq_closure`,
  `Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior`, and
  `intrinsicClosure_mono`.
- Primitive data vs derived API: the primitive data are the family `C` and the owner proofs
  `hC : ∀ i, Convex 𝕜 (C i)`; the closure identity is derived API, so it should live in the
  owner-style `Convex` namespace rather than as a parallel global wrapper.
- Layer target: this item stays `source-facing`, but Theorem 6.5 (1) is refined to the owner-style
  `Convex` API in canonical `intrinsicInterior`/`intrinsicClosure` language, with the ordinary
  closure version retained as a corollary.
-/

namespace Convex

open AffineMap

variable {C : ι → Set E}

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

/-- Theorem 6.5 (1), intrinsic form: if a family of convex sets in an ordered topological
`𝕜`-module has relative interiors with a common point, then the intrinsic closure of their
intersection is the intersection of their intrinsic closures. -/
-- Proof sketch: choose a common point `x ∈ ⋂ i, intrinsicInterior 𝕜 (C i)`. For
-- `y ∈ ⋂ i, intrinsicClosure 𝕜 (C i)`, Theorem 6.1 puts every point of the open segment from `x`
-- to `y` into each `intrinsicInterior 𝕜 (C i)`, hence into `⋂ i, C i`; letting the segment
-- endpoint enter `intrinsicClosure 𝕜 (openSegment 𝕜 x y)`, and then monotonicity of
-- `intrinsicClosure` finishes. The reverse inclusion is the monotonicity of intrinsic closure.
theorem intrinsicClosure_iInter_eq_iInter_intrinsicClosure (hC : ∀ i, Convex 𝕜 (C i))
    (hri : (⋂ i, ri[𝕜](C i)).Nonempty) :
    cl[𝕜](⋂ i, C i) = ⋂ i, cl[𝕜](C i) := by
  refine subset_antisymm ?_ ?_
  · intro y hy
    refine Set.mem_iInter.2 fun i ↦ ?_
    exact intrinsicClosure_mono (show (⋂ i, C i) ⊆ C i from fun z hz ↦ Set.mem_iInter.1 hz i) hy
  · rcases hri with ⟨x, hx⟩
    have hxri : ∀ i, x ∈ ri[𝕜](C i) := fun i ↦ Set.mem_iInter.1 hx i
    intro y hy
    have hycl : ∀ i, y ∈ cl[𝕜](C i) := fun i ↦ Set.mem_iInter.1 hy i
    have hseg : openSegment 𝕜 x y ⊆ ⋂ i, C i := by
      intro z hz
      refine Set.mem_iInter.2 fun i ↦ ?_
      exact intrinsicInterior_subset <|
        openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior (hC i) (hxri i)
          (hycl i) hz
    exact intrinsicClosure_mono hseg <| right_mem_intrinsicClosure_openSegment x y

end Convex

end IntrinsicClosure

section Closure

variable {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

namespace Convex

variable {C : ι → Set E}

/-- Theorem 6.5 (1), ambient-closure form in finite-dimensional normed spaces. -/
theorem closure_iInter_eq_iInter_closure (hC : ∀ i, Convex 𝕜 (C i))
    (hri : (⋂ i, ri[𝕜](C i)).Nonempty) :
    closure (⋂ i, C i) = ⋂ i, closure (C i) := by
  simpa [intrinsicClosure_eq_closure 𝕜 (⋂ i, C i)] using
    intrinsicClosure_iInter_eq_iInter_intrinsicClosure (C := C) hC hri

end Convex

end Closure

section Interior

variable {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E]

namespace Convex

open AffineMap

variable {C : ι → Set E}

/-- Theorem 6.5 (2): if a finite family of convex sets in a finite-dimensional normed space over
`𝕜` has relative interiors with a common point, then the relative interior of their intersection
is the intersection of their relative interiors. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement. -/
-- Proof sketch: by part (1), the sets `⋂ i, C i` and `⋂ i, intrinsicInterior 𝕜 (C i)` have the
-- same intrinsic closure. Applying the owner theorem `Convex.ri_intrinsicClosure_eq_ri`
-- to the convex intersection then gives
-- `intrinsicInterior 𝕜 (⋂ i, C i) ⊆ ⋂ i, intrinsicInterior 𝕜 (C i)`. For the reverse inclusion,
-- fix `z` in the right-hand side and use Theorem 6.4 to prolong any segment in `⋂ i, C i` past
-- `z` inside each `C i`; finiteness lets these prolongations be intersected into one common
-- prolongation in `⋂ i, C i`.
theorem intrinsicInterior_iInter_eq_iInter_intrinsicInterior (hC : ∀ i, Convex 𝕜 (C i))
    (hri : (⋂ i, ri[𝕜](C i)).Nonempty) [Finite ι] :
    ri[𝕜](⋂ i, C i) = ⋂ i, ri[𝕜](C i) := by
  have hCri : ∀ i, Convex 𝕜 (ri[𝕜](C i)) := fun i ↦ (hC i).intrinsicInterior
  have hInter : Convex 𝕜 (⋂ i, C i) := convex_iInter hC
  have hInterRi : Convex 𝕜 (⋂ i, ri[𝕜](C i)) := convex_iInter hCri
  refine subset_antisymm ?_ ?_
  · have hri_idem : ∀ i, ri[𝕜](ri[𝕜](C i)) = ri[𝕜](C i) := fun i ↦ by
      calc
        ri[𝕜](ri[𝕜](C i)) = ri[𝕜](closure (ri[𝕜](C i))) := by
          symm
          exact (hCri i).intrinsicInterior_closure_eq_intrinsicInterior
        _ = ri[𝕜](closure (C i)) := by
          rw [(hC i).closure_intrinsicInterior_eq_closure]
        _ = ri[𝕜](C i) := (hC i).intrinsicInterior_closure_eq_intrinsicInterior
    have hri' : (⋂ i, ri[𝕜](ri[𝕜](C i))).Nonempty := by
      rcases hri with ⟨x, hx⟩
      refine ⟨x, Set.mem_iInter.2 fun i ↦ ?_⟩
      simpa [hri_idem i] using (Set.mem_iInter.1 hx i)
    have hclosure_ri : ∀ i, closure (ri[𝕜](C i)) = closure (C i) := fun i ↦
      (hC i).closure_intrinsicInterior_eq_closure
    have hclosure : closure (⋂ i, ri[𝕜](C i)) = closure (⋂ i, C i) := by
      calc
        closure (⋂ i, ri[𝕜](C i)) = ⋂ i, closure (ri[𝕜](C i)) := by
          exact closure_iInter_eq_iInter_closure hCri hri'
        _ = ⋂ i, closure (C i) := by
          ext x
          simp [hclosure_ri]
        _ = closure (⋂ i, C i) := by
          symm
          exact closure_iInter_eq_iInter_closure hC hri
    intro z hz
    have hz' : z ∈ ri[𝕜](closure (⋂ i, C i)) := by
      simpa [hInter.intrinsicInterior_closure_eq_intrinsicInterior] using hz
    have hz'' : z ∈ ri[𝕜](closure (⋂ i, ri[𝕜](C i))) := by
      simpa [hclosure] using hz'
    have hz''' : z ∈ ri[𝕜](⋂ i, ri[𝕜](C i)) := by
      simpa [hInterRi.intrinsicInterior_closure_eq_intrinsicInterior] using hz''
    exact intrinsicInterior_subset hz'''
  · classical
    by_cases hι : IsEmpty ι
    · letI := hι
      have huniv : ri[𝕜]((Set.univ : Set E)) = Set.univ := by
        refine subset_antisymm intrinsicInterior_subset ?_
        simpa using
          (interior_subset_intrinsicInterior : interior (Set.univ : Set E) ⊆
            ri[𝕜]((Set.univ : Set E)))
      simp [huniv]
    · letI := Fintype.ofFinite ι
      letI : Nonempty ι := not_isEmpty_iff.mp hι
      intro z hz
      have hzri : ∀ i, z ∈ ri[𝕜](C i) := fun i ↦ Set.mem_iInter.1 hz i
      have hzInter : z ∈ ⋂ i, C i := Set.mem_iInter.2 fun i ↦ intrinsicInterior_subset (hzri i)
      have hInterNe : (⋂ i, C i).Nonempty := ⟨z, hzInter⟩
      refine (hInter.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem).2 ⟨hInterNe, ?_⟩
      intro x hx
      have hxC : ∀ i, x ∈ C i := fun i ↦ Set.mem_iInter.1 hx i
      choose μ hμ_gt hμ_mem using fun i : ι ↦
        (((hC i).mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem).1 (hzri i)).2 x
          (hxC i)
      have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
      let μmin : 𝕜 := (Finset.univ : Finset ι).inf' hne μ
      let ν : 𝕜 := (1 + μmin) / 2
      have hμmin_gt : 1 < μmin := by
        dsimp [μmin]
        rw [Finset.lt_inf'_iff hne]
        intro i hi
        exact hμ_gt i
      have hν_gt : 1 < ν := by
        dsimp [ν]
        linarith
      have hν_lt : ∀ i : ι, ν < μ i := by
        intro i
        have hle : μmin ≤ μ i := by
          dsimp [μmin]
          exact Finset.inf'_le μ (by simp)
        dsimp [ν]
        linarith
      refine ⟨ν, hν_gt, Set.mem_iInter.2 ?_⟩
      intro i
      have hseg : lineMap x z ν ∈ openSegment 𝕜 z (lineMap x z (μ i)) := by
        rw [openSegment_eq_image_lineMap]
        refine ⟨(ν - 1) / (μ i - 1), ?_, ?_⟩
        · constructor
          · have : 0 < ν - 1 := by linarith [hν_gt]
            have hden : 0 < μ i - 1 := by linarith [hμ_gt i]
            have : 0 < (ν - 1) / (μ i - 1) := div_pos this hden
            simpa
          · have hden : 0 < μ i - 1 := by linarith [hμ_gt i]
            have : (ν - 1) / (μ i - 1) < 1 := by
              rw [div_lt_one hden]
              linarith [hν_lt i]
            simpa
        · have hden : μ i - 1 ≠ 0 := by linarith [hμ_gt i]
          calc
            lineMap z (lineMap x z (μ i)) ((ν - 1) / (μ i - 1)) =
                lineMap (lineMap x z (μ i)) z (1 - (ν - 1) / (μ i - 1)) := by
                  rw [lineMap_symm]
                  simp
            _ = lineMap x z (1 - (1 - (1 - (ν - 1) / (μ i - 1))) * (1 - μ i)) := by
                  rw [lineMap_lineMap_left]
            _ = lineMap x z ν := by
                  congr 1
                  field_simp [hden]
                  ring
      exact intrinsicInterior_subset <|
        (hC i).openSegment_intrinsicInterior_closure_subset_intrinsicInterior (hzri i)
          (subset_closure (hμ_mem i)) hseg

end Convex

end Interior
