import SmoothManifolds_Lee_2012.Chap05.Sec05_30.Definition_5_30_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_38.Definition_6_38_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_38.Lemma_6_6
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ContDiff Manifold Topology

-- Domain sampling for this refine pass checked the Section 6.38 owner
-- `has_measure_zero_in_manifold`, the Section 6.38 image theorem for that owner, and the nearby
-- Chapter 6 Sard-theorem statements about critical values.

universe uE uE' uH uH' uM uN

section

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable [MeasurableSpace E'] [BorelSpace E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Helper for Corollary 6.11: a `C¹` map from a lower-dimensional finite-dimensional real vector
space into a higher-dimensional one has additive Haar null range. -/
private theorem measure_zero_range_of_contDiff_of_model_finrank_lt {f : E → E'}
    (hf : ContDiff ℝ 1 f) (μ : Measure E') [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    μ (Set.range f) = 0 := by
  -- First show that the range has Hausdorff dimension strictly smaller than the ambient dimension.
  have hdimRange :
      dimH (Set.range f) < Module.finrank ℝ E' :=
    hf.dimH_range_le.trans_lt <| Nat.cast_lt.2 hdim
  have hhausdorff :
      Measure.hausdorffMeasure (Module.finrank ℝ E' : ℝ) (Set.range f) = 0 := by
    -- The ambient Hausdorff measure vanishes on sets of strictly smaller Hausdorff dimension.
    simpa using hausdorffMeasure_of_dimH_lt hdimRange
  -- Any additive Haar measure on a finite-dimensional real vector space is a scalar multiple of the
  -- canonical Hausdorff measure in top dimension.
  rw [Measure.isAddLeftInvariant_eq_smul μ
      (Measure.hausdorffMeasure (Module.finrank ℝ E' : ℝ))]
  simp [hhausdorff]

/-- Helper for Corollary 6.11: for a fixed target chart, the chart image of `Set.range F` has
measure zero when the source model dimension is strictly smaller than the target one. -/
private theorem chartRangeImage_hasMeasureZero_of_model_finrank_lt
    [SecondCountableTopology M] {F : M → N} (hF : ContMDiff I J ∞ F)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E')
    (μ : Measure E') (hμ : μ.IsAddHaarMeasure)
    {e : OpenPartialHomeomorph N H'} (he : e ∈ IsManifold.maximalAtlas J ∞ N) :
    μ (((e.extend J) '' (Set.range F ∩ e.source))) = 0 := by
  classical
  let s : Set M := F ⁻¹' e.source
  let V : s → Set s := fun p ↦ Subtype.val ⁻¹' (extChartAt I p.1).source
  -- Cover the relevant source locus by countably many source-chart domains.
  have hV_nhds : ∀ p : s, V p ∈ nhds p := by
    intro p
    exact preimage_coe_mem_nhds_subtype.2 <|
      mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds (I := I) p.1)
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  let sourceSet : s → Set M := fun p ↦ (extChartAt I p.1).source ∩ F ⁻¹' e.source
  let sourcePiece : s → Set E := fun p ↦ (extChartAt I p.1) '' sourceSet p
  let rep : s → E → E' := fun p ↦ e.extend J ∘ F ∘ (extChartAt I p.1).symm
  have hpiece_zero : ∀ p ∈ t, μ (rep p '' sourcePiece p) = 0 := by
    intro p hp
    have hsourceSet_open : IsOpen (sourceSet p) := by
      -- The source piece is cut out by the source chart and the open preimage `F ⁻¹' e.source`.
      exact (isOpen_extChartAt_source (I := I) p.1).inter (e.open_source.preimage hF.continuous)
    have hsource_subset : sourceSet p ⊆ (chartAt H p.1).source := by
      intro x hx
      simpa [sourceSet, Set.mem_inter_iff, extChartAt_source] using hx.1
    have hmapsTo : Set.MapsTo F (sourceSet p) e.source := by
      intro x hx
      exact hx.2
    have hrep_contDiff : ContDiffOn ℝ ∞ (rep p) (sourcePiece p) := by
      -- Rewrite manifold smoothness of `F` into ordinary smoothness on this source chart piece.
      exact
        (contMDiffOn_iff_of_mem_maximalAtlas'
          (I := I) (I' := J) (n := ∞) (e := chartAt H p.1) (e' := e) (f := F)
          (s := sourceSet p)
          (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) p.1) he
          hsource_subset hmapsTo).1 <|
          hF.contMDiffOn.mono (Set.subset_univ _)
    have hsourcePiece_eq :
        sourcePiece p = I '' ((chartAt H p.1) '' sourceSet p) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨x, hx, rfl⟩
        exact ⟨chartAt H p.1 x, ⟨x, hx, rfl⟩, rfl⟩
      · intro hz
        rcases hz with ⟨u, ⟨x, hx, hux⟩, huz⟩
        refine ⟨x, hx, ?_⟩
        calc
          (extChartAt I p.1) x = I ((chartAt H p.1) x) := rfl
          _ = I u := by rw [hux]
          _ = z := huz
    have hsourcePiece_subset_range : sourcePiece p ⊆ Set.range I := by
      intro y hy
      rcases hy with ⟨x, _, rfl⟩
      exact ⟨chartAt H p.1 x, rfl⟩
    have hlocLip :
        ∀ x ∈ sourcePiece p,
          ∃ C : NNReal, ∃ t : Set E, t ∈ nhdsWithin x (sourcePiece p) ∧
            LipschitzOnWith C (rep p) t := by
      intro x hx
      rcases hx with ⟨y, hy, hxy⟩
      have hchart_image_open : IsOpen ((chartAt H p.1) '' sourceSet p) := by
        exact
          (chartAt H p.1).isOpen_image_of_subset_source hsourceSet_open
            hsource_subset
      have hsourcePiece_nhds :
          sourcePiece p ∈ nhdsWithin ((extChartAt I p.1) y) (Set.range I) := by
        have hchart_nhds :
            (chartAt H p.1) '' sourceSet p ∈ nhds ((chartAt H p.1) y) := by
          exact hchart_image_open.mem_nhds ⟨y, hy, rfl⟩
        have himage_nhds :
            I '' ((chartAt H p.1) '' sourceSet p) ∈
              nhdsWithin (I ((chartAt H p.1) y)) (Set.range I) :=
          I.image_mem_nhdsWithin hchart_nhds
        rw [hsourcePiece_eq]
        simpa using himage_nhds
      have hrepWithin : ContDiffWithinAt ℝ 1 (rep p) (Set.range I) x := by
        -- Upgrade the chart piece to the convex ambient model range near the current point.
        have hrepWithinSource :
            ContDiffWithinAt ℝ 1 (rep p) (sourcePiece p) ((extChartAt I p.1) y) := by
          exact
            (hrep_contDiff ((extChartAt I p.1) y) ⟨y, hy, rfl⟩).of_le
              (show (1 : ℕ∞ω) ≤ ∞ by simp)
        rw [← hxy]
        exact hrepWithinSource.mono_of_mem_nhdsWithin hsourcePiece_nhds
      obtain ⟨C, u, hu, hLip⟩ := hrepWithin.exists_lipschitzOnWith (I.convex_range)
      have hsourcePiece_nhds' : sourcePiece p ∈ 𝓝[Set.range I] x := by
        rw [← hxy]
        exact hsourcePiece_nhds
      have hrestrict : 𝓝[Set.range I] x = 𝓝[sourcePiece p] x := by
        rw [nhdsWithin_restrict'' (Set.range I) hsourcePiece_nhds']
        congr
        exact Set.inter_eq_right.2 hsourcePiece_subset_range
      have hu' : u ∈ 𝓝[sourcePiece p] x := by
        rw [← hrestrict]
        exact hu
      exact ⟨C, u, hu', hLip⟩
    have hdimImage : dimH (rep p '' sourcePiece p) < Module.finrank ℝ E' := by
      -- Local Lipschitz control bounds the Hausdorff dimension of each chartwise image piece.
      calc
        dimH (rep p '' sourcePiece p) ≤ dimH (sourcePiece p) := by
          exact dimH_image_le_of_locally_lipschitzOn hlocLip
        _ ≤ dimH (Set.range I) := dimH_mono hsourcePiece_subset_range
        _ ≤ Module.finrank ℝ E := by
          rw [← Real.dimH_univ_eq_finrank E]
          exact dimH_mono (Set.subset_univ _)
        _ < Module.finrank ℝ E' := Nat.cast_lt.2 hdim
    have hhausdorff :
        Measure.hausdorffMeasure (Module.finrank ℝ E' : ℝ) (rep p '' sourcePiece p) = 0 := by
      -- Top-dimensional Hausdorff measure vanishes once the Hausdorff dimension is too small.
      simpa using hausdorffMeasure_of_dimH_lt hdimImage
    -- Compare volume to top-dimensional Hausdorff measure on the codomain model space.
    rw [Measure.isAddLeftInvariant_eq_smul μ
      (Measure.hausdorffMeasure (Module.finrank ℝ E' : ℝ))]
    simp [hhausdorff]
  have hsubset :
      (e.extend J) '' (Set.range F ∩ e.source) ⊆ ⋃ p ∈ t, rep p '' sourcePiece p := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy.1 with ⟨x, rfl⟩
    let xs : s := ⟨x, hy.2⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    have hx_source : x ∈ (extChartAt I p.1).source := by
      simpa [V] using hxp
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨(extChartAt I p.1) x, ?_, ?_⟩
    · refine ⟨x, ?_, rfl⟩
      exact ⟨hx_source, hy.2⟩
    · -- On the chosen chart piece, the representative agrees with the original chart image.
      change (e.extend J) (F ((extChartAt I p.1).symm ((extChartAt I p.1) x))) =
        (e.extend J) (F x)
      rw [(extChartAt I p.1).left_inv hx_source]
  -- The whole target-chart image is a countable union of the null source-chart pieces.
  exact
    measure_mono_null hsubset <|
      (measure_biUnion_null_iff ht_countable).2 hpiece_zero

/-- Helper for Corollary 6.11: the smooth image `Set.range F` has measure zero in `N` when the
source model dimension is strictly smaller than the target one. -/
private theorem rangeHasMeasureZeroInManifold_of_contMDiff_of_model_finrank_lt {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    has_measure_zero_in_manifold J (Set.range F) := by
  -- Work directly with the owner definition of manifold measure zero.
  intro μ hμ e he
  exact
    chartRangeImage_hasMeasureZero_of_model_finrank_lt
      (I := I) (J := J) (F := F) hF hdim μ hμ he

/-- Corollary 6.11: if `F : M → N` is a smooth map between smooth manifolds with or without
boundary and the model-space dimension of `M` is strictly smaller than that of `N`, then the image
`F(M)`, represented by `Set.range F`, has measure zero in `N`. -/
theorem range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    {F : M → N} (hF : ContMDiff I J ∞ F)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    has_measure_zero_in_manifold J (Set.range F) := by
  -- Apply the chartwise Hausdorff-dimension argument directly, without importing
  -- the full Sard file.
  exact rangeHasMeasureZeroInManifold_of_contMDiff_of_model_finrank_lt hF hdim

end

section

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Preferred-chart formulation of Corollary 6.11, derived from the manifold owner
`has_measure_zero_in_manifold`. -/
theorem range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt_chartwise
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    {F : M → N} (hF : ContMDiff I J ∞ F)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    ∀ x : N, volume ((extChartAt J x) '' (Set.range F ∩ (extChartAt J x).source)) = 0 := by
  intro x
  exact
    has_measure_zero_in_manifold.extChartAt_volume_eq_zero
      J (range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt hF hdim) x

end
