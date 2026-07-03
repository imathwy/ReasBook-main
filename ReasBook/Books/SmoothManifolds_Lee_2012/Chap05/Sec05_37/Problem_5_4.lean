import SmoothManifoldsLee.Chap04.Sec04_24.Example_4_19
import SmoothManifoldsLee.Chap05.Sec05_35.Definition_5_35_extra_4

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open Topology
open scoped Manifold

local notation "Plane" => ℝ × ℝ

/-- Helper for Problem 5-4: the restricted figure-eight parametrization is continuous because it is
the ambient continuous map composed with the interval inclusion. -/
theorem figureEightCurve_continuous : Continuous figureEightCurve := by
  -- Rewrite `figureEightCurve` as the ambient map restricted to the open interval `(-π, π)`.
  simpa [figureEightCurve] using
    figureEightCurveMap_contDiff.continuous.comp continuous_subtype_val

/-- Helper for Problem 5-4: a continuous injective map from a linear order without endpoints into
`ℝ` is an open embedding. -/
lemma continuous_injective_order_to_real_isOpenEmbedding
    {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α]
    {leftNeighbor : ∀ x : α, ∃ y : α, y < x}
    {rightNeighbor : ∀ x : α, ∃ y : α, x < y}
    {g : α → ℝ} (hg_cont : Continuous g) (hg_inj : Function.Injective g) :
    IsOpenEmbedding g := by
  -- A continuous image of an interval is order-connected, so it suffices to prove the range is open.
  have hrange_ordConnected : Set.OrdConnected (Set.range g) := by
    exact (isPreconnected_range hg_cont).ordConnected
  rcases Continuous.strictMono_of_inj hg_cont hg_inj with hmono | hanti
  · have hEmbedding : IsEmbedding g := hmono.isEmbedding_of_ordConnected hrange_ordConnected
    have hOpenRange : IsOpen (Set.range g) := by
      -- Every image point has image-points on both sides, so order-connectedness gives an open interval.
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨x, rfl⟩
      obtain ⟨xL, hxL⟩ := leftNeighbor x
      obtain ⟨xR, hxR⟩ := rightNeighbor x
      have hxL_mem : g xL ∈ Set.range g := ⟨xL, rfl⟩
      have hxR_mem : g xR ∈ Set.range g := ⟨xR, rfl⟩
      have hleft : g xL < g x := hmono hxL
      have hright : g x < g xR := hmono hxR
      refine Filter.mem_of_superset (Ioo_mem_nhds hleft hright) ?_
      intro z hz
      exact hrange_ordConnected.out hxL_mem hxR_mem ⟨hz.1.le, hz.2.le⟩
    exact ⟨hEmbedding, hOpenRange⟩
  · have hneg_mono : StrictMono (fun x ↦ -g x) := by
      intro x₁ x₂ hx
      exact neg_lt_neg (hanti hx)
    have hneg_ordConnected : Set.OrdConnected (Set.range fun x ↦ -g x) := by
      exact (isPreconnected_range (continuous_neg.comp hg_cont)).ordConnected
    have hneg_embedding : IsEmbedding (fun x ↦ -g x) := by
      exact hneg_mono.isEmbedding_of_ordConnected hneg_ordConnected
    have hEmbedding : IsEmbedding g := by
      exact IsEmbedding.of_comp hg_cont continuous_neg hneg_embedding
    have hOpenRange : IsOpen (Set.range g) := by
      -- The antitone case is the same argument with the left and right image endpoints swapped.
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨x, rfl⟩
      obtain ⟨xL, hxL⟩ := leftNeighbor x
      obtain ⟨xR, hxR⟩ := rightNeighbor x
      have hxL_mem : g xL ∈ Set.range g := ⟨xL, rfl⟩
      have hxR_mem : g xR ∈ Set.range g := ⟨xR, rfl⟩
      have hleft : g xR < g x := hanti hxR
      have hright : g x < g xL := hanti hxL
      refine Filter.mem_of_superset (Ioo_mem_nhds hleft hright) ?_
      intro z hz
      exact hrange_ordConnected.out hxR_mem hxL_mem ⟨hz.1.le, hz.2.le⟩
    exact ⟨hEmbedding, hOpenRange⟩

/-- Helper for Problem 5-4: a continuous injective map from an open real interval into a smooth
`1`-manifold is a local homeomorphism. -/
lemma continuous_injective_interval_to_curve_manifold_isLocalHomeomorph
    {a b : ℝ} (hab : a < b)
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold 𝓘(ℝ) ⊤ M]
    {f : Set.Ioo a b → M} (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    IsLocalHomeomorph f := by
  -- Work chart-by-chart and shrink to a smaller parameter interval that stays inside one chart source.
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  haveI : Inhabited (Set.Ioo a b) := ⟨x⟩
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
  let leftNeighbor : ∀ z : Set.Ioo u v, ∃ w : Set.Ioo u v, w < z := fun z ↦ by
    rcases exists_between z.2.1 with ⟨w, huw, hwz⟩
    have hw_mem : w ∈ Set.Ioo u v := ⟨huw, lt_trans hwz z.2.2⟩
    exact ⟨⟨w, hw_mem⟩, hwz⟩
  let rightNeighbor : ∀ z : Set.Ioo u v, ∃ w : Set.Ioo u v, z < w := fun z ↦ by
    rcases exists_between z.2.2 with ⟨w, hzw, hwv⟩
    have hw_mem : w ∈ Set.Ioo u v := ⟨lt_trans z.2.1 hzw, hwv⟩
    exact ⟨⟨w, hw_mem⟩, hzw⟩
  set g : Set.Ioo u v → M := (Set.Ioo u v).restrict f
  have hg_cont : Continuous g := by
    -- Restrict the original continuous map to the smaller interval.
    simpa [g] using hf_cont.comp continuous_subtype_val
  have hg_inj : Function.Injective g := by
    -- Injectivity is preserved under restriction to a subtype of the domain.
    exact hf_inj.comp Subtype.val_injective
  have hg_source : ∀ y : Set.Ioo u v, g y ∈ e.source := by
    -- The interval was chosen to lie inside the preimage of the chart source.
    intro y
    exact huv_subset y.2
  set gChart : Set.Ioo u v → e.source := Set.codRestrict g e.source hg_source
  have hgChart_cont : Continuous gChart := by
    -- Codomain restriction to the chart source is continuous because the image already lands there.
    simpa [gChart] using hg_cont.subtype_mk hg_source
  have hgChart_inj : Function.Injective gChart := by
    -- Codomain restriction does not change injectivity.
    intro y₁ y₂ h
    apply hg_inj
    exact congrArg Subtype.val h
  have hcoord_emb : IsOpenEmbedding ((e.source.restrict e) ∘ gChart) := by
    -- In chart coordinates we are back in the one-dimensional real case.
    exact continuous_injective_order_to_real_isOpenEmbedding
      (leftNeighbor := leftNeighbor) (rightNeighbor := rightNeighbor)
      (e.isOpenEmbedding_restrict.continuous.comp hgChart_cont)
      (e.isOpenEmbedding_restrict.injective.comp hgChart_inj)
  have hgChart_emb : IsOpenEmbedding gChart := by
    -- Pull the coordinate open embedding back through the chart local homeomorphism.
    exact IsLocalHomeomorph.isOpenEmbedding_of_comp
      e.isOpenEmbedding_restrict.isLocalHomeomorph hcoord_emb hgChart_cont
  -- Compose with the open inclusion of the chart source to recover the original restricted map.
  simpa [g, gChart, Function.comp] using
    e.open_source.isOpenEmbedding_subtypeVal.comp hgChart_emb

lemma continuous_injective_interval_to_curve_manifold_isEmbedding
    {a b : ℝ} (hab : a < b)
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold 𝓘(ℝ) ⊤ M]
    {f : Set.Ioo a b → M} (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    IsEmbedding f := by
  -- First obtain the local-homeomorphism structure, then upgrade by injectivity to an embedding.
  have hLocal : IsLocalHomeomorph f :=
    continuous_injective_interval_to_curve_manifold_isLocalHomeomorph hab hf_cont hf_inj
  exact (IsLocalHomeomorph.isOpenEmbedding_of_injective hLocal hf_inj).isEmbedding

/-- Problem 5-4: the image of the figure-eight curve from Example 4.19 is not an embedded curve,
so in particular it is not an embedded submanifold of `ℝ²`. This is a statement about the image
subset itself, not merely about whether the parametrization `figureEightCurve` is an embedding. -/
theorem figureEightCurve_image_not_embedded_curve :
    ¬ (Set.range figureEightCurve).AdmitsEmbeddedCurveStructure := by
  intro hEmbeddedCurve
  rcases hEmbeddedCurve with ⟨_, _, hEmbedded⟩
  let _ : IsEmbeddedSubmanifold 𝓘(ℝ, Plane) 𝓘(ℝ) (Set.range figureEightCurve) := hEmbedded
  let liftedCurve : Set.Ioo (-Real.pi) Real.pi → Set.range figureEightCurve :=
    Set.codRestrict figureEightCurve (Set.range figureEightCurve) fun t ↦ Set.mem_range_self t
  have hLiftedContinuous : Continuous liftedCurve := by
    -- The embedded-submanifold structure equips the subtype with the induced subspace topology.
    refine hEmbedded.isSmoothEmbedding_subtype_val.isEmbedding.isInducing.continuous_iff.2 ?_
    simpa [liftedCurve, Function.comp] using figureEightCurve_continuous
  have hLiftedInj : Function.Injective liftedCurve := by
    -- Injectivity is unchanged by codomain restriction to the range.
    exact figureEightCurve_injective.codRestrict (fun t ↦ Set.mem_range_self t)
  have hLiftedEmbedding : IsEmbedding liftedCurve := by
    -- Route correction: avoid the broken finite-dimensional immersion criterion import chain and
    -- reduce the remaining work to the one-dimensional topological statement above.
    exact continuous_injective_interval_to_curve_manifold_isEmbedding
      (by linarith [Real.pi_pos]) hLiftedContinuous hLiftedInj
  have hFigureEightEmbedding : IsEmbedding figureEightCurve := by
    -- Composing the lifted embedding with the subtype inclusion recovers `figureEightCurve`.
    simpa [liftedCurve, Function.comp] using
      hEmbedded.isSmoothEmbedding_subtype_val.isEmbedding.comp hLiftedEmbedding
  exact figureEightCurve_not_isEmbedding hFigureEightEmbedding
