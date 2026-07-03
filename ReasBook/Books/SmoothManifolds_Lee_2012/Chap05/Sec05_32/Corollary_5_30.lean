import Mathlib.Geometry.Manifold.ContMDiff.Basic
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Topology

section RestrictingMapsToEmbeddedSubmanifolds

universe u𝕜 uE uH uM uE' uH' uE'' uH'' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S]
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H'' N]
variable {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ⊤ N]

namespace Manifold.IsSmoothEmbedding

/-- Helper for Corollary 5.30: the codomain-restricted map is continuous because the embedded
submanifold carries the induced subspace topology. -/
lemma continuous_codRestrict
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    Continuous (Set.codRestrict F S hFS) := by
  -- The embedding part of `hS` identifies continuity into `S` with continuity after composing
  -- with the inclusion `Subtype.val : S → M`.
  refine hS.isEmbedding.isInducing.continuous_iff.2 ?_
  simpa [Function.comp] using hF.continuous

/-- Helper for Corollary 5.30: in immersion charts for the inclusion `S ↪ M`, the restricted map
to `S` is recovered from the ambient chart expression by the projected inverse equivalence. -/
lemma writtenInCharts_codRestrict_eqOn
    {F : N → M} (hFS : ∀ x, F x ∈ S) {y : S}
    (hImm : IsImmersionAt J I ⊤ (Subtype.val : S → M) y) :
    Set.EqOn ((hImm.domChart.extend J) ∘ Set.codRestrict F S hFS)
      ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F))
      ((Set.codRestrict F S hFS) ⁻¹' hImm.domChart.source) := by
  -- Apply the immersion normal form to the point `Set.codRestrict F S hFS z` and solve for its
  -- domain-chart coordinates by postcomposing with `Prod.fst ∘ hImm.equiv.symm`.
  intro z hz
  have hz_target :
      hImm.domChart.extend J (Set.codRestrict F S hFS z) ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hz
  simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hz] using
    (congrArg (fun v => Prod.fst (hImm.equiv.symm v)) (hImm.writtenInCharts hz_target)).symm

/-- Helper for Corollary 5.30: each pointwise codomain restriction is smooth in the embedded
manifold structure. -/
lemma contMDiffAt_toSubtype
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) (x : N) :
    ContMDiffAt K J ⊤ (Set.codRestrict F S hFS) x := by
  let fS : N → S := Set.codRestrict F S hFS
  let y : S := fS x
  let hImm : IsImmersionAt J I ⊤ (Subtype.val : S → M) y := hS.isImmersion.isImmersionAt y
  let e : OpenPartialHomeomorph N H'' := chartAt H'' x
  let x' : E'' := e.extend K x
  have hcont : ContinuousAt fS x := (continuous_codRestrict hS hF hFS).continuousAt
  have hx : x ∈ e.source := mem_chart_source H'' x
  have hy : fS x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hy' : F x ∈ hImm.codChart.source := hImm.mem_codChart_source
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ) (e := e)
    (e' := hImm.domChart) (IsManifold.chart_mem_maximalAtlas x) hImm.domChart_mem_maximalAtlas
    hx hy,
    continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨hcont, ?_⟩
  have hambient :
      ContDiffWithinAt 𝕜 ⊤ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) (Set.range K) x' := by
    -- Rewrite the ambient smoothness in the chart pair `(e, hImm.codChart)`.
    simpa [Set.preimage_univ] using
      ((contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ) (e := e)
        (e' := hImm.codChart) (IsManifold.chart_mem_maximalAtlas x)
        hImm.codChart_mem_maximalAtlas hx hy').1 (hF.contMDiffAt.contMDiffWithinAt)).2
  have hproj :
      ContDiff 𝕜 ⊤ (fun v ↦ (hImm.equiv.symm v).1) := by
    simpa using contDiff_fst.comp hImm.equiv.symm.contDiff
  have hprojWithin :
      ContDiffWithinAt 𝕜 ⊤ (fun v ↦ (hImm.equiv.symm v).1) Set.univ
        (((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) x') :=
    hproj.contDiffWithinAt
  have hcomp :
      ContDiffWithinAt 𝕜 ⊤
        ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm))
        (Set.range K) x' := by
    -- Postcompose the ambient chart expression with the smooth linear projection onto the
    -- `S`-coordinates in the immersion normal form.
    exact hprojWithin.comp x' hambient (by intro z hz; simp)
  have hsource_mem : fS ⁻¹' hImm.domChart.source ∈ 𝓝 x := by
    -- The chosen immersion chart is open around `y = fS x`, so continuity of `fS` pulls it back
    -- to a neighborhood of `x`.
    have : hImm.domChart.source ∈ 𝓝 (fS x) :=
      hImm.domChart.open_source.mem_nhds hy
    exact hcont.preimage_mem_nhds this
  have hset_mem :
      (e.extend K).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈ 𝓝[Set.range K] x' := by
    -- Transport that neighborhood through the source chart on `N`.
    simpa [e, x', nhdsWithin_univ] using
      e.extend_preimage_mem_nhdsWithin (I := K) (s := Set.univ) (t := fS ⁻¹' hImm.domChart.source)
        hx (by simpa [nhdsWithin_univ] using hsource_mem)
  have heq :
      ((hImm.domChart.extend J) ∘ fS ∘ (e.extend K).symm)
        =ᶠ[𝓝[Set.range K] x']
          ((fun v ↦ (hImm.equiv.symm v).1) ∘
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm)) := by
    -- On the neighborhood where `fS` lands in the immersion domain chart, the two chart
    -- expressions agree by the previous `EqOn` lemma.
    refine Filter.eventuallyEq_of_mem hset_mem ?_
    intro z hz
    have hchartEq := writtenInCharts_codRestrict_eqOn (F := F) (hFS := hFS) (hImm := hImm)
    simpa [Function.comp] using hchartEq hz
  have hx'_target : x' ∈ (e.extend K).target := (e.extend K).map_source <| by
    simpa [OpenPartialHomeomorph.extend_source] using hx
  have hx'_range : x' ∈ Set.range K :=
    e.extend_target_subset_range hx'_target
  exact hcomp.congr_of_eventuallyEq_of_mem heq hx'_range

/-- If `Subtype.val : S → M` is a smooth embedding and a smooth map `F : N → M` has image in `S`,
then `F` is smooth as a map to `S`. This owner-based restriction-to-subtype bridge is the
canonical input for Corollary 5.30 and its boundary-ambient variant. -/
theorem contMDiff_toSubtype
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := by
  -- Smoothness is verified pointwise using the immersion normal form of the embedding.
  intro x
  exact contMDiffAt_toSubtype hS hF hFS x

end Manifold.IsSmoothEmbedding

/-- Corollary 5.30 (Embedded Case): every smooth map `F : N → M` whose image is contained in an
embedded submanifold `S ⊆ M` is smooth as a map from `N` to `S`. -/
theorem contMDiff_toSubtype_of_isEmbeddedSubmanifold {F : N → M}
    [IsEmbeddedSubmanifold I J S]
    (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := by
  simpa using
    IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val.contMDiff_toSubtype hF hFS

end RestrictingMapsToEmbeddedSubmanifolds
