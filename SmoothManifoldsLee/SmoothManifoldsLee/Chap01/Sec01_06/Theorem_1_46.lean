import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

open Set Function
open scoped Manifold Topology

namespace ModelWithCorners

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {n : WithTop ℕ∞}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
variable {e e' : OpenPartialHomeomorph M H} {x : M}

/-- In a `C¹` manifold, any chart in the maximal atlas detects interior points by the image of the
point in the model space. -/
lemma mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := I.contDiffOn_extendCoordChange he he'
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) →
      e'.extend I x ∈ interior (range I) by
    refine e'.mem_interior_extend_target (by simp [hex']) <| h ?_
    exact
      (I.isInvertible_fderivWithin_extendCoordChange hn he he' <| by simp [hex, hex']).surjective
  intro hφx'
  wlog hR : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField hR]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
    exact e.extend_preimage_mem_nhds hex <| e'.open_source.mem_nhds hex'
  change Function.Surjective
      ⇑((fderivWithin 𝕜 φ φ.source (e.extend I x)).restrictScalars ℝ) at hφx'
  rw [(hφ.differentiableOn hn _ (by simp [φ, hex, hex'])).restrictScalars_fderivWithin ℝ
      (uniqueDiffWithinAt_of_mem_nhds hφx),
    fderivWithin_of_mem_nhds hφx] at hφx'
  rw [show e'.extend I x = φ (e.extend I x) by simp [φ, hex]]
  replace hφ := ((hφ.restrict_scalars ℝ).differentiableOn hn).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

/-- In a `C¹` manifold, charts in the maximal atlas detect interior points exactly by the image of
the point in the model space. -/
lemma mem_interior_range_iff_of_mem_maximalAtlas (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source) :
    e.extend I x ∈ interior (e.extend I).target ↔
      e'.extend I x ∈ interior (e'.extend I).target := by
  constructor <;>
    apply I.mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas hn <;>
      assumption

/-- In a `C¹` manifold, any chart in the maximal atlas detects interior points. -/
theorem isInteriorPoint_iff_of_mem_maximalAtlas (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  rw [I.isInteriorPoint_iff]
  exact I.mem_interior_range_iff_of_mem_maximalAtlas hn (IsManifold.chart_mem_maximalAtlas x) he
    (mem_chart_source H x) hx

/-- In a `C¹` manifold, any chart in the maximal atlas detects boundary points. -/
theorem isBoundaryPoint_iff_of_mem_maximalAtlas (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) :
    I.IsBoundaryPoint x ↔ e.extend I x ∈ frontier (e.extend I).target := by
  rw [← not_iff_not, ← I.isInteriorPoint_iff_not_isBoundaryPoint,
    I.isInteriorPoint_iff_of_mem_maximalAtlas hn he hx, mem_interior_iff_notMem_frontier]
  exact (e.extend I).mapsTo <| by rwa [e.extend_source]

end

end ModelWithCorners

section

universe uM

variable {n : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
variable [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M]

-- `smooth_boundary_chart_frontier_independence` is the source-facing bridge/view corollary of
-- `ModelWithCorners.isBoundaryPoint_iff_of_mem_maximalAtlas`.
/-- Theorem 1.46 (Smooth Invariance of the Boundary): if one smooth chart around `p` sends `p` to
the boundary of the half-space model, then every smooth chart around `p` does the same. -/
theorem smooth_boundary_chart_frontier_independence
    {e e' : OpenPartialHomeomorph M (EuclideanHalfSpace n)} {p : M}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M)
    (he' : e' ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M)
    (hp : p ∈ e.source) (hp' : p ∈ e'.source)
    (hboundary : e.extend (𝓡∂ n) p ∈ frontier (e.extend (𝓡∂ n)).target) :
    e'.extend (𝓡∂ n) p ∈ frontier (e'.extend (𝓡∂ n)).target :=
  ((𝓡∂ n).isBoundaryPoint_iff_of_mem_maximalAtlas (by simp) he' hp').1
    (((𝓡∂ n).isBoundaryPoint_iff_of_mem_maximalAtlas (by simp) he hp).2 hboundary)

end
