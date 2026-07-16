import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Example_4_20
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_37.Problem_5_4

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open Topology
open scoped ContDiff Manifold Torus

local notation "T2Model" => ModelWithCorners.pi (fun _ : Fin 2 ↦ 𝓡 1)

/-- Helper for Problem 5-5: the dense torus curve is continuous because each circle-valued
coordinate is a continuous Fourier character. -/
theorem denseTorusCurve_continuous (α : ℝ) : Continuous (denseTorusCurve α) := by
  -- Check continuity coordinatewise on the torus product.
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · simpa [denseTorusCurve] using Real.continuous_fourierChar
  · have hmul : Continuous (fun a : ℝ ↦ α * a) := continuous_const.mul continuous_id
    simpa [denseTorusCurve] using Real.continuous_fourierChar.comp hmul

/-- Helper for Problem 5-5: a continuous injective map from `ℝ` into a smooth `1`-manifold is a
local homeomorphism. -/
lemma continuous_injective_real_to_curve_manifold_isLocalHomeomorph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    {f : ℝ → M} (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    IsLocalHomeomorph f := by
  -- Route correction: work chart-by-chart and shrink to a small parameter interval inside one
  -- chart source, exactly as in the interval proof from Problem 5-4.
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  let e := chartAt ℝ (f x)
  have hx_source : f x ∈ e.source := mem_chart_source ℝ (f x)
  have hpreimage_source : f ⁻¹' e.source ∈ 𝓝 x := by
    exact hf_cont.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hx_source)
  obtain ⟨xL, hxL⟩ := exists_lt x
  obtain ⟨xR, hxR⟩ := exists_gt x
  obtain ⟨u, v, hxuv, huv_subset⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨xL, hxL⟩ ⟨xR, hxR⟩).1 hpreimage_source
  refine ⟨Set.Ioo u v, Ioo_mem_nhds hxuv.1 hxuv.2, ?_⟩
  have huv : u < v := lt_trans hxuv.1 hxuv.2
  haveI : Inhabited (Set.Ioo u v) := Classical.inhabited_of_nonempty (Set.nonempty_Ioo_subtype huv)
  haveI : Set.OrdConnected (Set.Ioo u v) := inferInstance
  letI : ConditionallyCompleteLinearOrder (Set.Ioo u v) := inferInstance
  have leftNeighbor : ∀ z : Set.Ioo u v, ∃ w : Set.Ioo u v, w < z := by
    intro z
    rcases exists_between z.2.1 with ⟨w, huw, hwz⟩
    have hw_mem : w ∈ Set.Ioo u v := ⟨huw, lt_trans hwz z.2.2⟩
    exact ⟨⟨w, hw_mem⟩, hwz⟩
  have rightNeighbor : ∀ z : Set.Ioo u v, ∃ w : Set.Ioo u v, z < w := by
    intro z
    rcases exists_between z.2.2 with ⟨w, hzw, hwv⟩
    have hw_mem : w ∈ Set.Ioo u v := ⟨lt_trans z.2.1 hzw, hwv⟩
    exact ⟨⟨w, hw_mem⟩, hzw⟩
  let g : Set.Ioo u v → M := (Set.Ioo u v).restrict f
  have hg_cont : Continuous g := by
    -- Restrict the original continuous map to the chosen parameter interval.
    simpa [g] using hf_cont.comp continuous_subtype_val
  have hg_inj : Function.Injective g := by
    -- Injectivity is unchanged after restricting the domain.
    exact hf_inj.comp Subtype.val_injective
  have hg_source : ∀ y : Set.Ioo u v, g y ∈ e.source := by
    -- The interval was chosen inside the preimage of the chart source.
    intro y
    exact huv_subset y.2
  let gChart : Set.Ioo u v → e.source := Set.codRestrict g e.source hg_source
  have hgChart_cont : Continuous gChart := by
    -- Codomain restriction preserves continuity when the image already lands in the target set.
    simpa [gChart] using hg_cont.subtype_mk hg_source
  have hgChart_inj : Function.Injective gChart := by
    -- Codomain restriction does not affect injectivity.
    intro y₁ y₂ h
    apply hg_inj
    exact congrArg Subtype.val h
  have hcoord_emb : IsOpenEmbedding ((e.source.restrict e) ∘ gChart) := by
    -- In chart coordinates we are back in the one-dimensional real situation from Problem 5-4.
    exact continuous_injective_order_to_real_isOpenEmbedding
      (leftNeighbor := leftNeighbor) (rightNeighbor := rightNeighbor)
      (e.isOpenEmbedding_restrict.continuous.comp hgChart_cont)
      (e.isOpenEmbedding_restrict.injective.comp hgChart_inj)
  have hgChart_emb : IsOpenEmbedding gChart := by
    -- Pull the coordinate open embedding back through the chart local homeomorphism.
    exact IsLocalHomeomorph.isOpenEmbedding_of_comp
      e.isOpenEmbedding_restrict.isLocalHomeomorph hcoord_emb hgChart_cont
  -- Compose with the open chart-source inclusion to recover the original restricted map.
  simpa [g, gChart, Function.comp] using
    e.open_source.isOpenEmbedding_subtypeVal.comp hgChart_emb

/-- Helper for Problem 5-5: a continuous injective map from `ℝ` into a smooth `1`-manifold is an
embedding. -/
lemma continuous_injective_real_to_curve_manifold_isEmbedding
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    {f : ℝ → M} (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    IsEmbedding f := by
  -- First obtain the local-homeomorphism structure, then upgrade by injectivity.
  have hLocal : IsLocalHomeomorph f :=
    continuous_injective_real_to_curve_manifold_isLocalHomeomorph hf_cont hf_inj
  exact (IsLocalHomeomorph.isOpenEmbedding_of_injective hLocal hf_inj).isEmbedding

/-- Helper for Problem 5-5: once the image subset is charted as a curve, the codomain-restricted
parametrization into that image subtype is an embedding. -/
lemma dense_torus_curve_range_lift_isEmbedding
    (α : ℝ) (hα : Irrational α)
    [ChartedSpace ℝ (Set.range (denseTorusCurve α))] :
    IsEmbedding
      (Set.codRestrict (denseTorusCurve α) (Set.range (denseTorusCurve α))
        (fun t ↦ Set.mem_range_self t)) := by
  let liftedCurve : ℝ → Set.range (denseTorusCurve α) :=
    Set.codRestrict (denseTorusCurve α) (Set.range (denseTorusCurve α))
      (fun t ↦ Set.mem_range_self t)
  have hLiftedContinuous : Continuous liftedCurve := by
    -- Codomain restriction into the actual range subtype preserves continuity.
    simpa [liftedCurve] using
      (denseTorusCurve_continuous α).subtype_mk (fun t ↦ Set.mem_range_self t)
  have hLiftedInj : Function.Injective liftedCurve := by
    -- Codomain restriction does not change injectivity.
    exact (denseTorusCurve_injective α hα).codRestrict (fun t ↦ Set.mem_range_self t)
  -- Apply the real-line embedding criterion to the lifted parametrization.
  simpa [liftedCurve] using
    continuous_injective_real_to_curve_manifold_isEmbedding hLiftedContinuous hLiftedInj

/-- Problem 5-5: for irrational `α`, the image of the torus curve from Example 4.20 is not an
embedded curve, hence not an embedded submanifold, of `𝕋²`. As in Problem 5-4, this is a
statement about the image subset `Set.range (denseTorusCurve α)`, not merely about whether the
parametrization `denseTorusCurve α` is an embedding. -/
theorem denseTorusCurve_image_not_embedded_curve (α : ℝ) (hα : Irrational α) :
    ¬ ∃ _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)),
        ∃ _ : IsManifold 𝓘(ℝ) ∞ (Set.range (denseTorusCurve α)),
          IsEmbeddedSubmanifold T2Model 𝓘(ℝ) (Set.range (denseTorusCurve α)) := by
  intro hRange
  rcases hRange with ⟨cs, _, _⟩
  let _ : ChartedSpace ℝ (Set.range (denseTorusCurve α)) := cs
  let liftedCurve : ℝ → Set.range (denseTorusCurve α) :=
    Set.codRestrict (denseTorusCurve α) (Set.range (denseTorusCurve α))
      (fun t ↦ Set.mem_range_self t)
  have hLiftedEmbedding : IsEmbedding liftedCurve := by
    -- The hypothetical embedded-curve structure forces the lifted parametrization to be an
    -- embedding of the line into its image subset.
    simpa [liftedCurve] using dense_torus_curve_range_lift_isEmbedding α hα
  have hCurveEmbedding : IsEmbedding (denseTorusCurve α) := by
    -- Composing the lifted embedding with the canonical range inclusion recovers the original
    -- torus curve.
    simpa [liftedCurve, Function.comp] using
      Topology.IsEmbedding.subtypeVal.comp hLiftedEmbedding
  exact denseTorusCurve_not_isEmbedding α hα hCurveEmbedding
