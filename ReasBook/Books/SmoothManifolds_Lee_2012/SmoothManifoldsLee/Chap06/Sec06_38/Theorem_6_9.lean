import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_38.Definition_6_38_extra_2
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Manifold Set
open scoped ContDiff Manifold

-- Domain sampling for this refine pass:
-- * source-facing owner: `has_measure_zero_in_manifold`;
-- * core/canonical ambient null-image theorem:
--   `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`;
-- * bridge/view layer here: the manifold image theorem derived from that owner stack.
-- * countability repair: `SecondCountableTopology M` is the canonical local assumption supplying
--   the countable chart subcover used in Lee's proof.

universe uE uE' uH uH' uM uN

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable [MeasurableSpace E'] [BorelSpace E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [SecondCountableTopology M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Theorem 6.9: if `M` and `N` are smooth manifolds with or without boundary modeled on
finite-dimensional real vector spaces `E` and `E'` of the same dimension, `F : M → N` is smooth,
and `A ⊆ M` has measure zero in `M`, then `F '' A` has measure zero in `N`. -/
theorem has_measure_zero_in_manifold.image_of_contMDiff {F : M → N} {A : Set M}
    (h_dim : Module.finrank ℝ E = Module.finrank ℝ E')
    (hA : has_measure_zero_in_manifold I A) (hF : ContMDiff I J ∞ F) :
    has_measure_zero_in_manifold J (F '' A) := by
  intro μ hμ e he
  classical
  let s : Set M := A ∩ F ⁻¹' e.source
  let V : s → Set s := fun p ↦ Subtype.val ⁻¹' (extChartAt I p.1).source
  -- Cover the relevant part of `A` by countably many source-chart domains.
  have hV_nhds : ∀ p : s, V p ∈ nhds p := by
    intro p
    exact preimage_coe_mem_nhds_subtype.2 <|
      mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds (I := I) p.1)
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq h_dim
  let μE : Measure E := Measure.map L.symm μ
  let sourceSet : s → Set M := fun p ↦ A ∩ (extChartAt I p.1).source ∩ F ⁻¹' e.source
  let sourcePiece : s → Set E := fun p ↦ (extChartAt I p.1) '' sourceSet p
  let rep : s → E → E' := fun p ↦ e.extend J ∘ F ∘ (extChartAt I p.1).symm
  let linearizedRep : s → E → E := fun p ↦ L.symm ∘ rep p
  -- Each chart piece has source measure zero, and its coordinate image stays measure zero after
  -- applying the ambient equal-dimension theorem.
  have hpiece_zero : ∀ p ∈ t, μ (rep p '' sourcePiece p) = 0 := by
    intro p hp
    have hsource_zero : μE (sourcePiece p) = 0 := by
      refine measure_mono_null ?_
        (has_measure_zero_in_manifold.extChartAt_eq_zero I μE inferInstance hA p.1)
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      simpa [sourceSet, Set.mem_inter_iff, Set.mem_preimage] using hy.1
    have hsource_subset : sourceSet p ⊆ (chartAt H p.1).source := by
      intro x hx
      simp only [sourceSet, Set.mem_inter_iff, Set.mem_preimage] at hx
      simpa [extChartAt_source] using hx.1.2
    have hmapsTo : Set.MapsTo F (sourceSet p) e.source := by
      intro x hx
      simp only [sourceSet, Set.mem_inter_iff, Set.mem_preimage] at hx
      exact hx.2
    have hrep_contDiff : ContDiffOn ℝ ∞ (rep p) (sourcePiece p) := by
      -- Rewrite smoothness of `F` on the chart piece into ordinary smoothness in coordinates.
      exact
        (contMDiffOn_iff_of_mem_maximalAtlas'
          (I := I) (I' := J) (n := ∞) (e := chartAt H p.1) (e' := e)
          (f := F) (s := sourceSet p)
          (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) p.1) he
          hsource_subset hmapsTo).1 <|
          hF.contMDiffOn.mono (Set.subset_univ _)
    have hlinearized_diff : DifferentiableOn ℝ (linearizedRep p) (sourcePiece p) := by
      -- Postcompose with a linear equivalence to reduce to a same-space differentiable map.
      exact (L.symm.comp_differentiableOn_iff).2 <| hrep_contDiff.differentiableOn (by simp)
    have hlinearized_zero : μE (linearizedRep p '' sourcePiece p) = 0 :=
      MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μE
        hlinearized_diff hsource_zero
    have hpreimage :
        L ⁻¹' (rep p '' sourcePiece p) = linearizedRep p '' sourcePiece p := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        refine ⟨y, hy, ?_⟩
        simpa [linearizedRep, rep, Function.comp] using congrArg L.symm hxy
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        refine ⟨y, hy, ?_⟩
        simpa [linearizedRep, rep, Function.comp] using congrArg L hxy
    have hmap : Measure.map L μE = μ := by
      change Measure.map L (Measure.map L.symm μ) = μ
      rw [Measure.map_map L.continuous.measurable L.symm.continuous.measurable]
      simp
    -- Transport the zero statement back across the linear equivalence.
    calc
      μ (rep p '' sourcePiece p) = (Measure.map L μE) (rep p '' sourcePiece p) := by rw [hmap]
      _ = μE (L ⁻¹' (rep p '' sourcePiece p)) := by
        exact MeasurableEmbedding.map_apply L.toHomeomorph.measurableEmbedding μE _
      _ = μE (linearizedRep p '' sourcePiece p) := by rw [hpreimage]
      _ = 0 := hlinearized_zero
  have hsubset :
      (e.extend J) '' (F '' A ∩ e.source) ⊆ ⋃ p ∈ t, rep p '' sourcePiece p := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨hy_range, hy_source⟩
    rcases hy_range with ⟨x, hxA, rfl⟩
    let xs : s := ⟨x, by
      simp only [s, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨hxA, hy_source⟩⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    have hx_source : x ∈ (extChartAt I p.1).source := by
      simpa [V] using hxp
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨(extChartAt I p.1) x, ?_, ?_⟩
    · refine ⟨x, ?_, rfl⟩
      simp only [sourceSet, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨⟨hxA, hx_source⟩, hy_source⟩
    · change (e.extend J) (F ((extChartAt I p.1).symm ((extChartAt I p.1) x))) = (e.extend J) (F x)
      rw [(extChartAt I p.1).left_inv hx_source]
  -- The target-chart image lies in a countable union of null chart pieces.
  exact measure_mono_null hsubset <| (measure_biUnion_null_iff ht_countable).2 hpiece_zero

end
