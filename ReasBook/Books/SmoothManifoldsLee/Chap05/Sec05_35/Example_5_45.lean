import SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_2
import SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_4
import SmoothManifoldsLee.Chap05.Sec05_35.Definition_5_35_extra_4
import SmoothManifoldsLee.Chap05.Sec05_35.Proposition_5_35
import SmoothManifoldsLee.Chap05.Sec05_36.Proposition_5_49

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped ContDiff

noncomputable section

local notation "Plane" => ℝ × ℝ

-- Semantic search note: no `lean_leansearch` tool was available in this environment, so the API
-- choice was checked against local immersed-submanifold declarations and nearby curve examples.

/-- The subset `S = {(x,y) : y = |x|}` from Example 5.45, viewed as the graph of `x ↦ |x|`. -/
def absoluteValueGraph : Set Plane :=
  Set.univ.graphOn fun x : ℝ ↦ |x|

/-- The punctured subset `S \ {(0,0)}` of the absolute-value graph. -/
def puncturedAbsoluteValueGraph : Set Plane :=
  absoluteValueGraph \ ({(0, 0)} : Set Plane)

/-- A point `(x,y)` lies in `absoluteValueGraph` exactly when `y = |x|`. -/
theorem mem_absoluteValueGraph_iff {x y : ℝ} :
    (x, y) ∈ absoluteValueGraph ↔ y = |x| := by
  simp [absoluteValueGraph, eq_comm]

/-- A point `(x,y)` lies in the punctured absolute-value graph exactly when `y = |x|` and
`(x,y) ≠ (0,0)`. -/
theorem mem_puncturedAbsoluteValueGraph_iff {x y : ℝ} :
    (x, y) ∈ puncturedAbsoluteValueGraph ↔ y = |x| ∧ (x, y) ≠ (0, 0) := by
  simp [puncturedAbsoluteValueGraph, mem_absoluteValueGraph_iff]

/-- Helper for Example 5.45: away from `0`, the graph of `x ↦ |x|` is the range of the canonical
graph parametrization over the open set `{x : ℝ | x ≠ 0}`. -/
lemma punctured_absoluteValueGraph_eq_range_graphMap_nonzero :
    let U : TopologicalSpace.Opens ℝ :=
      ⟨{x : ℝ | x ≠ 0}, by
        simpa using (isOpen_ne (x := (0 : ℝ)) : IsOpen {x : ℝ | x ≠ 0})⟩
    Set.range (TopologicalSpace.Opens.graphMap U fun x : ℝ ↦ |x|) =
      puncturedAbsoluteValueGraph := by
  intro U
  rw [TopologicalSpace.Opens.graphMap, _root_.range_graphMap_eq_graphOn]
  ext p
  rcases p with ⟨x, y⟩
  rw [mem_puncturedAbsoluteValueGraph_iff]
  simp only [Set.mem_graphOn]
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hy.symm, ?_⟩
    intro hxy
    exact hx (Prod.mk.inj hxy).1
  · rintro ⟨hy, hne⟩
    refine ⟨?_, hy.symm⟩
    intro hx
    apply hne
    ext <;> simp [hx, hy]

/-- Helper for Example 5.45: the absolute-value map is smooth away from the origin. -/
lemma contMDiffOn_abs_away_from_zero :
    ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞) (fun x : ℝ ↦ |x|) {x : ℝ | x ≠ 0} := by
  -- Move to the Euclidean `ContDiffOn` API, where `abs` is smooth away from its zero set.
  rw [contMDiffOn_iff_contDiffOn]
  intro x hx
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hEq :
        (fun y : ℝ ↦ |y|) =ᶠ[nhdsWithin x {y : ℝ | y ≠ 0}] fun y : ℝ ↦ -y := by
      let hEqOn : Set.EqOn (fun y : ℝ ↦ |y|) (fun y : ℝ ↦ -y) (Set.Iio 0) := by
        intro y hy
        exact abs_of_neg (show y < 0 from hy)
      exact hEqOn.eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hneg))
    let hNeg :
        ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) (fun y : ℝ ↦ -y) {y : ℝ | y ≠ 0} x :=
      ((contDiffAt_id : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun y : ℝ ↦ y) x).neg).contDiffWithinAt
    simpa using hNeg.congr_of_eventuallyEq_of_mem hEq hx
  · have hEq :
        (fun y : ℝ ↦ |y|) =ᶠ[nhdsWithin x {y : ℝ | y ≠ 0}] fun y : ℝ ↦ y := by
      let hEqOn : Set.EqOn (fun y : ℝ ↦ |y|) (fun y : ℝ ↦ y) (Set.Ioi 0) := by
        intro y hy
        exact abs_of_pos (show 0 < y from hy)
      exact hEqOn.eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hpos))
    let hPos :
        ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) (fun y : ℝ ↦ y) {y : ℝ | y ≠ 0} x :=
      (contDiffAt_id : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun y : ℝ ↦ y) x).contDiffWithinAt
    simpa using hPos.congr_of_eventuallyEq_of_mem hEq hx

/-- Helper for Example 5.45: every point of the graph of `y = |x|` satisfies `x² = y²`. -/
lemma sq_eq_sq_of_mem_absoluteValueGraph {x y : ℝ} (h : (x, y) ∈ absoluteValueGraph) :
    x ^ 2 = y ^ 2 := by
  -- Rewrite the graph condition as `y = |x|`, then square both sides.
  rw [mem_absoluteValueGraph_iff] at h
  rw [h]
  exact (sq_abs x).symm

-- Proof sketch: away from the origin, `absoluteValueGraph` is the disjoint union of the two smooth
-- lines `y = x` and `y = -x`, so each point has a neighborhood carried by one of these branches.
/-- Example 5.45 (1): the punctured subset `S \ {(0,0)}` of `S = {(x,y) : y = |x|}` is an
embedded one-dimensional smooth submanifold of `ℝ²`. -/
theorem puncturedAbsoluteValueGraph_is_embedded_curve :
    puncturedAbsoluteValueGraph.AdmitsEmbeddedCurveStructure := by
  let U : TopologicalSpace.Opens ℝ :=
    ⟨{x : ℝ | x ≠ 0}, by
      simpa using (isOpen_ne (x := (0 : ℝ)) : IsOpen {x : ℝ | x ≠ 0})⟩
  have hEq :
      Set.range (TopologicalSpace.Opens.graphMap U fun x : ℝ ↦ |x|) =
        puncturedAbsoluteValueGraph :=
    punctured_absoluteValueGraph_eq_range_graphMap_nonzero
  rw [← hEq]
  have hSmooth :
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞) (fun x : ℝ ↦ |x|) (U : Set ℝ) := by
    simpa [U] using contMDiffOn_abs_away_from_zero
  have hEmbedding :=
    graphMap_isSmoothEmbedding (E := ℝ) (F := ℝ) (G := ℝ) (M := ℝ) (N := ℝ)
      (J := 𝓘(ℝ)) U (fun x : ℝ ↦ |x|) hSmooth
  obtain ⟨instCharted, instManifold, hSubtype⟩ :=
    smooth_embedding_range_has_manifold_with_boundary
      (F := TopologicalSpace.Opens.graphMap U fun x : ℝ ↦ |x|)
      hEmbedding
  refine ⟨instCharted, ?_⟩
  refine ⟨instManifold, ?_⟩
  exact
    { toBoundarylessManifold := inferInstance
      isSmoothEmbedding_subtype_val := by
        rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
        exact hSubtype }

/-- Helper for Example 5.45: the subtype inclusion of an immersed curve is smooth because the
immersion normal form writes it as the linear inclusion `u ↦ (u, 0)` in suitable charts. -/
lemma subtype_val_contMDiff_of_isImmersedCurve {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane)) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane) := by
  have hSmoothTop :
      ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) (Subtype.val : S → Plane) := by
    intro x
    let hImmAt :
        IsImmersionAt 𝓘(ℝ) 𝓘(ℝ, Plane) (⊤ : WithTop ℕ∞) (Subtype.val : S → Plane) x :=
      hImm.isImmersionAt x
    let x' : ℝ := (hImmAt.domChart.extend 𝓘(ℝ)) x
    let L : ℝ →L[ℝ] Plane :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ ℝ hImmAt.complement)
    have hcont : ContinuousAt (Subtype.val : S → Plane) x := by
      let h := hImmAt.isImmersionAtOfComplement_complement
      have hdomChart_source : h.domChart.source ∈ nhds x :=
        IsOpen.mem_nhds h.domChart.open_source h.mem_domChart_source
      have hsource : (Subtype.val : S → Plane) ⁻¹' h.codChart.source ∈ nhds x :=
        Filter.mem_of_superset hdomChart_source h.source_subset_preimage_source
      have hEqOn :
          Set.EqOn ((h.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane))
            (h.equiv ∘ fun y : S ↦ (h.domChart.extend 𝓘(ℝ) y, (0 : hImmAt.complement)))
            h.domChart.source := by
        intro y hy
        have hy_target :
            h.domChart.extend 𝓘(ℝ) y ∈ (h.domChart.extend 𝓘(ℝ)).target :=
          (h.domChart.extend 𝓘(ℝ)).map_source <| by
            simpa [OpenPartialHomeomorph.extend_source] using hy
        simpa [Function.comp, OpenPartialHomeomorph.extend_coe, h.domChart.left_inv hy] using
          h.writtenInCharts hy_target
      have hEq :
          ((h.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane)) =ᶠ[nhds x]
            h.equiv ∘ fun y : S ↦ (h.domChart.extend 𝓘(ℝ) y, (0 : hImmAt.complement)) :=
        hEqOn.eventuallyEq_of_mem hdomChart_source
      have hcont_rhs :
          ContinuousAt
            (h.equiv ∘ fun y : S ↦ (h.domChart.extend 𝓘(ℝ) y, (0 : hImmAt.complement))) x := by
        have hcont_dom : ContinuousAt (h.domChart.extend 𝓘(ℝ)) x :=
          h.domChart.continuousAt_extend h.mem_domChart_source
        have hcont_pair :
            ContinuousAt (fun y : S ↦ (h.domChart.extend 𝓘(ℝ) y, (0 : hImmAt.complement))) x :=
          hcont_dom.prodMk continuousAt_const
        simpa [Function.comp] using ContinuousAt.comp h.equiv.continuousAt hcont_pair
      have hcont_extend :
          ContinuousAt ((h.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane)) x :=
        hcont_rhs.congr hEq.symm
      have hcont_chart : ContinuousAt (h.codChart ∘ (Subtype.val : S → Plane)) x := by
        simpa [Function.comp] using (𝓘(ℝ, Plane)).continuousAt_symm.comp hcont_extend
      exact (h.codChart.continuousAt_iff_continuousAt_comp_left hsource).2 hcont_chart
    have hx : x ∈ hImmAt.domChart.source := hImmAt.mem_domChart_source
    have hy : (Subtype.val : S → Plane) x ∈ hImmAt.codChart.source := hImmAt.mem_codChart_source
    -- Rewrite the inclusion in immersion charts and replace it by the linear model map.
    rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ)
      (e := hImmAt.domChart) (e' := hImmAt.codChart) hImmAt.domChart_mem_maximalAtlas
      hImmAt.codChart_mem_maximalAtlas hx hy, continuousWithinAt_univ, Set.preimage_univ,
      Set.univ_inter]
    refine ⟨hcont, ?_⟩
    have hmodel :
        ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) L (Set.range 𝓘(ℝ)) x' := by
      exact L.contDiff.contDiffWithinAt
    have htarget_mem : (hImmAt.domChart.extend 𝓘(ℝ)).target ∈ nhdsWithin x' (Set.range 𝓘(ℝ)) := by
      simpa [x'] using hImmAt.domChart.extend_target_mem_nhdsWithin (I := 𝓘(ℝ)) hx
    have hEq :
        ((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane) ∘
            (hImmAt.domChart.extend 𝓘(ℝ)).symm)
          =ᶠ[nhdsWithin x' (Set.range 𝓘(ℝ))] L := by
      refine Filter.eventuallyEq_of_mem htarget_mem ?_
      intro z hz
      simpa [Function.comp, L] using hImmAt.writtenInCharts hz
    have hx'_target : x' ∈ (hImmAt.domChart.extend 𝓘(ℝ)).target :=
      (hImmAt.domChart.extend 𝓘(ℝ)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hx
    have hx'_range : x' ∈ Set.range 𝓘(ℝ) :=
      hImmAt.domChart.extend_target_subset_range hx'_target
    exact hmodel.congr_of_eventuallyEq hEq <| hEq.eq_of_nhdsWithin hx'_range
  exact hSmoothTop.of_le le_top

/-- Helper for Example 5.45: pulling back the model-space unit tangent through a local chart
produces a genuine nonzero tangent vector on the assumed one-manifold. -/
lemma exists_nonzero_chart_tangent
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (p : S) :
    ∃ w : TangentSpace 𝓘(ℝ) p, w ≠ 0 := by
  let x : ℝ := extChartAt 𝓘(ℝ) p p
  let u : TangentSpace 𝓘(ℝ) x := (NormedSpace.fromTangentSpace x).symm 1
  obtain ⟨w, hw⟩ :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ)) (x := p) (y := p)
      (mem_extChartAt_source p)).surjective u
  refine ⟨w, ?_⟩
  intro hw0
  have hu_zero : u = 0 := by
    calc
      u = (mfderiv 𝓘(ℝ) 𝓘(ℝ) (extChartAt 𝓘(ℝ) p) p) 0 := by
        simpa [hw0] using hw.symm
      _ = 0 := by
        simpa using (mfderiv 𝓘(ℝ) 𝓘(ℝ) (extChartAt 𝓘(ℝ) p) p).map_zero
  have hone_zero : (1 : ℝ) = 0 := by
    simpa [u] using congrArg (NormedSpace.fromTangentSpace x) hu_zero
  exact one_ne_zero hone_zero

/-- Helper for Example 5.45: every tangent vector on a smooth curve-type manifold is realized by
some based smooth curve through the base point. -/
lemma exists_smoothCurveAt_tangentVector_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold 𝓘(ℝ) ∞ M]
    (p : M) (w : TangentSpace 𝓘(ℝ) p) :
    ∃ γ : SmoothCurveAt 𝓘(ℝ) p, γ.tangentVector = w := by
  -- Choose a representative of the smooth-curve velocity class corresponding to `w`.
  rcases Quotient.exists_rep ((curveVelocityClassEquivTangentSpace 𝓘(ℝ) p).symm w) with
    ⟨γ, hγ⟩
  refine ⟨γ, ?_⟩
  -- Evaluating the canonical equivalence on that class recovers the target tangent vector.
  have hclass := congrArg (curveVelocityClassEquivTangentSpace 𝓘(ℝ) p) hγ
  simpa [curveVelocityClassEquivTangentSpace_apply, curveVelocityClassToTangentSpace] using hclass

/-- Helper for Example 5.45: an `ω`-immersion remains an `∞`-immersion after lowering the atlas
regularity. -/
lemma isImmersion_infty_of_isImmersion_top {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane)) :
    IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ (Subtype.val : S → Plane) := by
  letI : IsManifold 𝓘(ℝ) ∞ S := IsManifold.of_le le_top
  let hImmTop := hImm.isImmersionOfComplement_complement
  let hImmInf :
      IsImmersionOfComplement hImm.complement 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
        (Subtype.val : S → Plane) := by
    intro p
    let hAt := hImmTop p
    refine Manifold.IsImmersionAtOfComplement.mk_of_charts
      hAt.equiv hAt.domChart hAt.codChart hAt.mem_domChart_source hAt.mem_codChart_source ?_ ?_
      hAt.source_subset_preimage_source hAt.writtenInCharts
    · exact IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ)) (M := S)
        (m := (∞ : ℕ∞ω)) (n := (⊤ : ℕ∞ω)) (by simp) hAt.domChart_mem_maximalAtlas
    · exact IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ, Plane)) (M := Plane)
        (m := (∞ : ℕ∞ω)) (n := (⊤ : ℕ∞ω)) (by simp) hAt.codChart_mem_maximalAtlas
  exact hImmInf.isImmersion

/-- Helper for Example 5.45: differentiating the immersion normal form on the source manifold
itself gives the chart-level tangent-vector identity needed for the cusp contradiction. -/
lemma subtype_val_chart_pushforward_eq_model {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    (p : S) (w : TangentSpace 𝓘(ℝ) p) :
    let hImmAt := hImm.isImmersionAt p
    let L : ℝ →L[ℝ] Plane :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ ℝ hImmAt.complement)
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (hImmAt.codChart.extend 𝓘(ℝ, Plane))
        ((Subtype.val : S → Plane) p))
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w) =
      L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w) := by
  let hImmAt := hImm.isImmersionAt p
  let L : ℝ →L[ℝ] Plane :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ ℝ hImmAt.complement)
  have hdomChart_source : hImmAt.domChart.source ∈ nhds p :=
    IsOpen.mem_nhds hImmAt.domChart.open_source hImmAt.mem_domChart_source
  have hEqOn :
      Set.EqOn ((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane))
        (L ∘ (hImmAt.domChart.extend 𝓘(ℝ))) hImmAt.domChart.source := by
    intro y hy
    -- Read the immersion normal form directly on the source chart neighborhood.
    have hy_target :
        hImmAt.domChart.extend 𝓘(ℝ) y ∈ (hImmAt.domChart.extend 𝓘(ℝ)).target :=
      (hImmAt.domChart.extend 𝓘(ℝ)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, L, OpenPartialHomeomorph.extend_coe,
      hImmAt.domChart.left_inv hy, ContinuousLinearMap.comp_apply] using
      hImmAt.writtenInCharts hy_target
  have hEq :
      ((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane)) =ᶠ[nhds p]
        L ∘ (hImmAt.domChart.extend 𝓘(ℝ)) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hsub :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p := by
    -- The immersed inclusion is already smooth by the earlier chart-normal-form argument.
    exact
      (subtype_val_contMDiff_of_isImmersedCurve hImm).mdifferentiableAt
        (by simp : (⊤ : ℕ∞ω) ≠ 0)
  have hdomChart_mem_maximalAtlas_one :
      hImmAt.domChart ∈ IsManifold.maximalAtlas 𝓘(ℝ) 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ)) (M := S)
      (m := 1) (n := (⊤ : ℕ∞ω)) (by simp) hImmAt.domChart_mem_maximalAtlas
  have hcodChart_mem_maximalAtlas_one :
      hImmAt.codChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) 1 Plane :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ, Plane)) (M := Plane)
      (m := 1) (n := (⊤ : ℕ∞ω)) (by simp) hImmAt.codChart_mem_maximalAtlas
  have hdom :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p := by
    -- Maximal-atlas charts are smooth when viewed in model coordinates.
    exact
      (contMDiffAt_extend (I := 𝓘(ℝ)) (e := hImmAt.domChart)
        hdomChart_mem_maximalAtlas_one hImmAt.mem_domChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hcod :
      MDifferentiableAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
        (hImmAt.codChart.extend 𝓘(ℝ, Plane)) ((Subtype.val : S → Plane) p) := by
    -- The same chart-smoothness fact applies to the ambient chart.
    exact
      (contMDiffAt_extend (I := 𝓘(ℝ, Plane)) (e := hImmAt.codChart)
        hcodChart_mem_maximalAtlas_one hImmAt.mem_codChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hL :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) L (hImmAt.domChart.extend 𝓘(ℝ) p) := by
    -- The linear model map has the expected model-space derivative.
    exact L.contMDiffAt.mdifferentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hmfderiv_eq :
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
        (((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane))) p =
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (L ∘ (hImmAt.domChart.extend 𝓘(ℝ))) p := by
    -- Differentiate the two eventually equal source-side expressions at the base point.
    exact hEq.mfderiv_eq
  have hleft :
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (hImmAt.codChart.extend 𝓘(ℝ, Plane))
          ((Subtype.val : S → Plane) p))
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w) =
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
        (((hImmAt.codChart.extend 𝓘(ℝ, Plane)) ∘ (Subtype.val : S → Plane))) p w := by
    symm
    exact mfderiv_comp_apply (x := p) hcod hsub w
  have hright :
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (L ∘ (hImmAt.domChart.extend 𝓘(ℝ))) p w =
        L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w) := by
    simpa [Function.comp, mfderiv_eq_fderiv] using
      (mfderiv_comp_apply (x := p) (g := L) (f := hImmAt.domChart.extend 𝓘(ℝ))
        hL hdom w)
  -- Apply the chain rule on both sides of the source-side equality.
  exact hleft.trans <| hmfderiv_eq ▸ hright

/-- Helper for Example 5.45: the derivative of a maximal-atlas chart is injective because the
chart inverse cancels it on the chart source. -/
lemma chart_extend_symm_mdifferentiableWithin_range {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    {e : OpenPartialHomeomorph S ℝ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) ⊤ S) {p : S} (hp : p ∈ e.source) :
    MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)).symm (Set.range 𝓘(ℝ))
      (e.extend 𝓘(ℝ) p) := by
  letI : IsManifold 𝓘(ℝ) 1 S :=
    IsManifold.of_le (m := 1) (n := (⊤ : ℕ∞ω)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ)) (M := S)
      (m := 1) (n := (⊤ : ℕ∞ω)) (by simp) he
  have hid :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (id : S → S) Set.univ p := by
    -- The inverse-chart derivative bridge starts from the trivial differentiability of `id`.
    simpa using (mdifferentiableWithinAt_id (I := 𝓘(ℝ)) (s := Set.univ) (x := p) :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (id : S → S) Set.univ p)
  -- Re-express `id` in chart coordinates to read off differentiability of the inverse chart.
  simpa [Function.comp] using
    (mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
      (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (e := e) (f := id) (s := Set.univ) he_one hp).mp hid

/-- Helper for Example 5.45: differentiating the chart left-inverse identity on `e.source`
produces a concrete left inverse for the derivative of `e.extend`. -/
lemma chart_extend_mfderiv_left_inverse {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    {e : OpenPartialHomeomorph S ℝ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) ⊤ S) {p : S} (hp : p ∈ e.source) :
    (mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)).symm (Set.range 𝓘(ℝ))
        (e.extend 𝓘(ℝ) p)).comp
      (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ) p) := by
  letI : IsManifold 𝓘(ℝ) 1 S :=
    IsManifold.of_le (m := 1) (n := (⊤ : ℕ∞ω)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℝ)) (M := S)
      (m := 1) (n := (⊤ : ℕ∞ω)) (by simp) he
  have hsource_unique : UniqueMDiffWithinAt 𝓘(ℝ) e.source p :=
    e.open_source.uniqueMDiffWithinAt hp
  have hchart :
      MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p := by
    -- Maximal-atlas charts are differentiable at every source point.
    exact
      (contMDiffAt_extend (I := 𝓘(ℝ)) (e := e) he_one hp).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hrange :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)).symm (Set.range 𝓘(ℝ))
        (e.extend 𝓘(ℝ) p) :=
    chart_extend_symm_mdifferentiableWithin_range he hp
  have hchart_within :
      mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p =
        mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) e.source p := by
    -- On the open chart source, the within derivative agrees with the ordinary derivative.
    symm
    exact mfderivWithin_eq_mfderiv hsource_unique hchart
  rw [hchart_within, ← mfderivWithin_comp_of_eq]
  · -- Route correction: differentiate the left-inverse identity on `e.source`, not on the
    -- chart target, so the source-side `UniqueMDiffWithinAt` applies directly.
    rw [← mfderivWithin_id hsource_unique]
    apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
    · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro z hz
      simpa [Function.comp] using e.extend_left_inv (I := 𝓘(ℝ)) hz
    · exact hp
  · exact hrange
  · exact hchart.mdifferentiableWithinAt
  · intro z hz
    have hz_target : e.extend 𝓘(ℝ) z ∈ (e.extend 𝓘(ℝ)).target :=
      (e.extend 𝓘(ℝ)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hz
    exact e.extend_target_subset_range hz_target
  · exact hsource_unique
  · rfl

/-- Helper for Example 5.45: the derivative of a maximal-atlas chart is injective because the
chart inverse cancels it on the chart source. -/
lemma chart_extend_mfderiv_injective {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    {e : OpenPartialHomeomorph S ℝ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ) ⊤ S) {p : S} (hp : p ∈ e.source) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p) := by
  let Linv :=
    mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)).symm (Set.range 𝓘(ℝ)) (e.extend 𝓘(ℝ) p)
  intro w₁ w₂ hw
  have hleft := chart_extend_mfderiv_left_inverse he hp
  have hp_left : (e.extend 𝓘(ℝ)).symm (e.extend 𝓘(ℝ) p) = p :=
    e.extend_left_inv (I := 𝓘(ℝ)) hp
  have hw_push : Linv (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p w₁) =
      Linv (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p w₂) := by
    simpa [Linv] using congrArg Linv hw
  have hw₁ :
      ((Linv.comp (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p)) w₁) = w₁ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w₁) hleft
  have hw₂ :
      ((Linv.comp (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p)) w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w₂) hleft
  have hw₁' : w₁ = Linv (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p w₁) := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₁.symm
  have hw₂' : Linv (mfderiv 𝓘(ℝ) 𝓘(ℝ) (e.extend 𝓘(ℝ)) p w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₂
  -- Apply the derivative-level left inverse to both chart-coordinate tangent vectors.
  exact hw₁'.trans (hw_push.trans hw₂')

/-- Helper for Example 5.45: the differential of the immersed subtype inclusion is injective at
every point because the source chart derivative and the linear normal form are both injective. -/
lemma subtype_val_mfderiv_injective_of_isImmersion {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    (p : S) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p) := by
  let hImmAt := hImm.isImmersionAt p
  let L : ℝ →L[ℝ] Plane :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ ℝ hImmAt.complement)
  have hL_injective : Function.Injective L := by
    intro u v huv
    have hpair :
        (u, (0 : hImmAt.complement)) = (v, (0 : hImmAt.complement)) := by
      apply hImmAt.equiv.injective
      simpa [L, ContinuousLinearMap.comp_apply] using huv
    exact (Prod.mk.inj hpair).1
  intro w₁ w₂ hw
  have hw_chart :
      L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₁) =
        L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₂) := by
    have hw₁_model :
        L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₁) =
          (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (hImmAt.codChart.extend 𝓘(ℝ, Plane))
            ((Subtype.val : S → Plane) p))
            (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w₁) := by
      simpa [hImmAt, L] using
        (subtype_val_chart_pushforward_eq_model hImm p w₁).symm
    have hw₂_model :
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (hImmAt.codChart.extend 𝓘(ℝ, Plane))
          ((Subtype.val : S → Plane) p))
          (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w₂) =
        L ((mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₂) := by
      simpa [hImmAt, L] using subtype_val_chart_pushforward_eq_model hImm p w₂
    -- Compare the two vectors after applying the codomain chart derivative.
    exact hw₁_model.trans <| by simpa [hw] using hw₂_model
  have hsource_chart :
      (mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₁ =
        (mfderiv 𝓘(ℝ) 𝓘(ℝ) (hImmAt.domChart.extend 𝓘(ℝ)) p) w₂ :=
    hL_injective hw_chart
  exact
    chart_extend_mfderiv_injective hImmAt.domChart_mem_maximalAtlas hImmAt.mem_domChart_source
      hsource_chart

/-- Helper for Example 5.45: an immersed subtype inclusion sends every nonzero intrinsic tangent
vector to a nonzero ambient tangent vector. -/
lemma immersion_chart_pushforward_nonzero {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    (p : S) {w : TangentSpace 𝓘(ℝ) p} (hw : w ≠ 0) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w ≠ 0 := by
  -- Route correction: the injectivity proof stays on the source-faithful immersion-chart route
  -- and now closes by cancelling the source chart derivative via the chart inverse.
  intro hzero
  have hinj :
      Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p) :=
    subtype_val_mfderiv_injective_of_isImmersion hImm p
  exact hw <| hinj <| by simpa using hzero

/-- Helper for Example 5.45: the ambient velocity of a subtype-valued smooth curve is the
subtype inclusion derivative applied to its intrinsic tangent vector. -/
lemma ambient_curve_velocity_eq_subtype_mfderiv_tangent
    {S : Set Plane} [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    {p : S} (γ : SmoothCurveAt 𝓘(ℝ) p) :
    γ.source ▸ curve_velocityWithin 𝓘(ℝ, Plane) (((↑) : S → Plane) ∘ γ) γ.sourceSet 0 =
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p γ.tangentVector := by
  rcases γ with ⟨r, f, hs, hsm⟩
  have hzero : 0 ∈ Set.Ioo (-(r : ℝ)) (r : ℝ) := by
    constructor
    · exact neg_lt_zero.mpr r.2
    · exact r.2
  have hsourceSet : UniqueMDiffWithinAt 𝓘(ℝ) (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 := by
    exact isOpen_Ioo.uniqueMDiffWithinAt (I := 𝓘(ℝ)) hzero
  have hsub : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) (f 0) := by
    simpa [hs] using
      (subtype_val_contMDiff_of_isImmersedCurve hImm).mdifferentiableAt (by simp : (⊤ : ℕ∞ω) ≠ 0)
  have hγ :
      MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) f (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 := by
    exact (hsm.mdifferentiableOn (by simp)) 0 hzero
  -- Differentiate the ambient curve by applying the chain rule to the subtype inclusion.
  have hcomp :
      curve_velocityWithin 𝓘(ℝ, Plane) (((↑) : S → Plane) ∘ f)
          (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 =
        mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) (f 0)
          (curve_velocityWithin 𝓘(ℝ) f (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0) :=
    composite_curve_velocity
      (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, Plane)) (J := Set.Ioo (-(r : ℝ)) (r : ℝ)) (t₀ := 0)
      (F := (Subtype.val : S → Plane)) (γ := f) hsourceSet hsub hγ
  cases hs
  simpa [SmoothCurveAt.tangentVector, SmoothCurveAt.sourceSet] using hcomp

/-- Helper for Example 5.45: pushing a nonzero tangent vector forward by the immersed subtype
inclusion gives a nonzero ambient tangent vector in the submanifold tangent space. -/
lemma pushforward_nonzero_tangent_mem_submanifold {S : Set Plane}
    [TopologicalSpace S] [ChartedSpace ℝ S] [IsManifold 𝓘(ℝ) ⊤ S]
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : S → Plane))
    (p : S) {w : TangentSpace 𝓘(ℝ) p} (hw : w ≠ 0) :
    let v := mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p w
    v ∈ (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : S → Plane) p).range ∧ v ≠ 0 := by
  -- Unfold the packaged ambient tangent vector and record both the range witness and its
  -- nonvanishing supplied by the immersion derivative.
  dsimp
  constructor
  · exact ⟨w, rfl⟩
  · exact immersion_chart_pushforward_nonzero hImm p hw

/-- Helper for Example 5.45: a smooth ambient curve in the graph of `y = |x|` through the origin
has zero velocity there. -/
lemma ambient_velocity_zero_of_absoluteValueGraph_curve
    {r : Set.Ioi (0 : ℝ)} {g : ℝ → Plane}
    (h0 : g 0 = (0, 0))
    (hgDiff0 : DifferentiableAt ℝ g 0)
    (hgraph : ∀ t ∈ Set.Ioo (-(r : ℝ)) (r : ℝ), g t ∈ absoluteValueGraph) :
    curve_velocityWithin 𝓘(ℝ, Plane) g (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 = 0 := by
  let s : Set ℝ := Set.Ioo (-(r : ℝ)) (r : ℝ)
  let x : ℝ → ℝ := fun t ↦ (g t).1
  let y : ℝ → ℝ := fun t ↦ (g t).2
  have hsOpen : IsOpen s := by
    simpa [s] using isOpen_Ioo
  have hrpos : (0 : ℝ) < r := r.2
  have hzero : (0 : ℝ) ∈ s := by
    constructor
    · exact neg_lt_zero.mpr hrpos
    · exact hrpos
  have hsNhds : s ∈ nhds (0 : ℝ) := hsOpen.mem_nhds hzero
  have hsUnique : UniqueMDiffWithinAt 𝓘(ℝ) s 0 := by
    simpa [s] using hsOpen.uniqueMDiffWithinAt (I := 𝓘(ℝ)) hzero
  have hgMDiff0 : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Plane) g 0 :=
    hgDiff0.mdifferentiableAt
  have hwithin_eq :
      curve_velocityWithin 𝓘(ℝ, Plane) g s 0 = curve_velocity 𝓘(ℝ, Plane) g 0 :=
    curve_velocityWithin_eq_curve_velocity hsUnique hgMDiff0
  have hx0 : x 0 = 0 := by
    simpa [x] using congrArg Prod.fst h0
  have hy0 : y 0 = 0 := by
    simpa [y] using congrArg Prod.snd h0
  have hyMinOn : IsMinOn y s 0 := by
    intro t ht
    have hyabs : y t = |x t| := by
      simpa [x, y] using mem_absoluteValueGraph_iff.mp (hgraph t (by simpa [s] using ht))
    -- Along the graph `y = |x|`, the second coordinate is nonnegative and vanishes at `0`.
    calc
      y 0 = 0 := hy0
      _ ≤ |x t| := abs_nonneg _
      _ = y t := hyabs.symm
  have hyLocalMin : IsLocalMin y 0 := hyMinOn.isLocalMin hsNhds
  have hxDiff0 : DifferentiableAt ℝ x 0 := by
    simpa [x] using hgDiff0.fst
  have hyDiff0 : DifferentiableAt ℝ y 0 := by
    simpa [y] using hgDiff0.snd
  have hyderiv_zero : deriv y 0 = 0 := hyLocalMin.deriv_eq_zero
  have habs :
      y =ᶠ[nhds (0 : ℝ)] fun t ↦ |x t| := by
    filter_upwards [hsNhds] with t ht
    simpa [x, y] using
      mem_absoluteValueGraph_iff.mp (hgraph t (by simpa [s] using ht))
  have hxderiv_zero : deriv x 0 = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hsign :
          ∀ᶠ t in nhds (0 : ℝ), SignType.sign (x t) = SignType.sign (0 - t) := by
        exact eventually_nhdsWithin_sign_eq_of_deriv_neg (f := x) hneg hx0
      have hEqRight :
          y =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] fun t ↦ -x t := by
        filter_upwards [eventually_mem_nhdsWithin, habs.filter_mono nhdsWithin_le_nhds,
          hsign.filter_mono nhdsWithin_le_nhds] with t htIci hyabs hsignt
        have htle : 0 ≤ t := by simpa using htIci
        rcases eq_or_lt_of_le htle with rfl | htpos
        · simp [hx0, hy0]
        · have hxneg : x t < 0 := by
            have : SignType.sign (x t) = -1 := by
              simpa [htpos] using hsignt
            exact sign_eq_neg_one_iff.mp this
          simp [hyabs, abs_of_neg hxneg]
      have hyRight : deriv y 0 = -deriv x 0 := by
        refine (uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _
          hyDiff0.hasDerivAt.hasDerivWithinAt ?_
        exact
          ((hxDiff0.hasDerivAt.neg).hasDerivWithinAt.congr_of_eventuallyEq hEqRight
            (by simp [hx0, hy0]))
      linarith
    · have hsign :
          ∀ᶠ t in nhds (0 : ℝ), SignType.sign (x t) = SignType.sign t := by
        simpa using eventually_nhdsWithin_sign_eq_of_deriv_pos (f := x) hpos hx0
      have hEqRight :
          y =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] x := by
        filter_upwards [eventually_mem_nhdsWithin, habs.filter_mono nhdsWithin_le_nhds,
          hsign.filter_mono nhdsWithin_le_nhds] with t htIci hyabs hsignt
        have htle : 0 ≤ t := by simpa using htIci
        rcases eq_or_lt_of_le htle with rfl | htpos
        · simp [hx0, hy0]
        · have hxpos : 0 < x t := by
            have : SignType.sign (x t) = 1 := by
              simpa [htpos] using hsignt
            exact sign_eq_one_iff.mp this
          simp [hyabs, abs_of_pos hxpos]
      have hyRight : deriv y 0 = deriv x 0 := by
        refine (uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _
          hyDiff0.hasDerivAt.hasDerivWithinAt ?_
        exact
          (hxDiff0.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq hEqRight
            (by simp [hx0, hy0]))
      linarith
  apply (NormedSpace.fromTangentSpace (g 0)).injective
  rw [hwithin_eq]
  have hpair :
      HasDerivAt g (deriv x 0, deriv y 0) 0 := by
    -- The ambient derivative is assembled from the two coordinate derivatives.
    simpa [x, y] using hxDiff0.hasDerivAt.prodMk hyDiff0.hasDerivAt
  have hvelocity :
      NormedSpace.fromTangentSpace (g 0) (curve_velocity 𝓘(ℝ, Plane) g 0) = (0, 0) := by
    have happly :
        fderiv ℝ g 0 1 = (deriv x 0, deriv y 0) := by
      simpa using DFunLike.congr_fun hpair.hasFDerivAt.fderiv 1
    simpa [curve_velocity, mfderiv_eq_fderiv, hxderiv_zero, hyderiv_zero] using happly
  simpa [h0] using hvelocity

/-- Helper for Example 5.45: every ambient tangent vector in the tangent space of the absolute
value graph at the origin must vanish. -/
lemma ambient_tangent_zero_at_absoluteValueGraph_origin
    [TopologicalSpace absoluteValueGraph] [ChartedSpace ℝ absoluteValueGraph]
    [IsManifold 𝓘(ℝ) ⊤ absoluteValueGraph]
    (p0 : absoluteValueGraph) (hp0 : (p0 : Plane) = (0, 0))
    (hImm : IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ⊤ (Subtype.val : absoluteValueGraph → Plane))
    {v : TangentSpace 𝓘(ℝ, Plane) (p0 : Plane)}
    (hv : v ∈ (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
      (Subtype.val : absoluteValueGraph → Plane) p0).range) :
    v = 0 := by
  letI : IsManifold 𝓘(ℝ) ∞ absoluteValueGraph := IsManifold.of_le le_top
  rcases hv with ⟨w, rfl⟩
  rcases exists_smoothCurveAt_tangentVector_eq (p := p0) w with ⟨γ, hγ⟩
  rcases γ with ⟨r, f, hsource, hsm⟩
  let γ0 : SmoothCurveAt 𝓘(ℝ) p0 := ⟨r, f, hsource, hsm⟩
  let g : ℝ → Plane := fun t ↦ (f t : Plane)
  cases hsource
  have hγv' :
      curve_velocityWithin 𝓘(ℝ, Plane) g (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 =
        mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : absoluteValueGraph → Plane) (f 0) w := by
    simpa [γ0, g, hγ, SmoothCurveAt.sourceSet, Function.comp] using
      ambient_curve_velocity_eq_subtype_mfderiv_tangent (hImm := hImm) (γ := γ0)
  have hzero : (0 : ℝ) ∈ Set.Ioo (-(r : ℝ)) (r : ℝ) := by
    constructor
    · exact neg_lt_zero.mpr r.2
    · exact r.2
  have hsNhds : Set.Ioo (-(r : ℝ)) (r : ℝ) ∈ nhds (0 : ℝ) := by
    exact isOpen_Ioo.mem_nhds hzero
  have hgSmooth :
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ g (Set.Ioo (-(r : ℝ)) (r : ℝ)) := by
    have hIncl :
        ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
          (Subtype.val : absoluteValueGraph → Plane) :=
      (subtype_val_contMDiff_of_isImmersedCurve hImm).of_le le_top
    -- The ambient curve is just the subtype curve followed by the smooth inclusion.
    simpa [g] using
      hIncl.comp_contMDiffOn hsm
  have hgDiff0 : DifferentiableAt ℝ g 0 := by
    have hgContDiffOn : ContDiffOn ℝ ∞ g (Set.Ioo (-(r : ℝ)) (r : ℝ)) := by
      rw [← contMDiffOn_iff_contDiffOn]
      exact hgSmooth
    exact (hgContDiffOn.contDiffAt hsNhds).differentiableAt (by simp)
  have hg0 : g 0 = (0, 0) := by
    simpa [g] using hp0
  have hgraph : ∀ t ∈ Set.Ioo (-(r : ℝ)) (r : ℝ), g t ∈ absoluteValueGraph := by
    intro t ht
    exact (f t).property
  have hzero_velocity :
      curve_velocityWithin 𝓘(ℝ, Plane) g (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 = 0 :=
    ambient_velocity_zero_of_absoluteValueGraph_curve
      (r := r) (g := g) hg0 hgDiff0 hgraph
  -- Lee's contradiction closes because the ambient velocity of any such curve is forced to be
  -- zero by the cusp computation above.
  have hv_zero :
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : absoluteValueGraph → Plane) (f 0) w = 0 := by
    calc
      mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : absoluteValueGraph → Plane) (f 0) w =
          curve_velocityWithin 𝓘(ℝ, Plane) g (Set.Ioo (-(r : ℝ)) (r : ℝ)) 0 := by
        simpa using hγv'.symm
      _ = 0 := hzero_velocity
  simpa using hv_zero

-- Proof sketch: if the whole absolute-value graph admitted an immersed-curve structure, then
-- Proposition 5.35 would provide a smooth curve through the origin with nonzero velocity in the
-- image. Writing the curve as `(x(t), y(t))` and using `y = |x|` forces `y'(0) = 0` and then,
-- after differentiating `x(t)^2 = y(t)^2` twice, also `x'(0) = 0`, contradicting immersion.
/-- Example 5.45 (2): the full set `S = {(x,y) : y = |x|}` admits no topology and smooth
one-manifold structure making its subtype inclusion into `ℝ²` an immersed submanifold. -/
theorem absoluteValueGraph_no_immersed_curve_structure :
    ¬ absoluteValueGraph.AdmitsImmersedCurveStructure := by
  intro hCurve
  rcases hCurve with ⟨t, hCurve⟩
  letI : TopologicalSpace ↥absoluteValueGraph := t
  rcases hCurve with ⟨cs, hMan, hImm⟩
  letI : ChartedSpace ℝ ↥absoluteValueGraph := cs
  letI : IsManifold 𝓘(ℝ) ⊤ ↥absoluteValueGraph := hMan
  letI : IsManifold 𝓘(ℝ) ∞ ↥absoluteValueGraph := IsManifold.of_le le_top
  let p0 : absoluteValueGraph := ⟨(0, 0), by simp [mem_absoluteValueGraph_iff]⟩
  have hp0 : (p0 : Plane) = (0, 0) := rfl
  obtain ⟨w, hw_ne⟩ := exists_nonzero_chart_tangent (p := p0)
  -- Route correction: the endgame is now isolated in
  -- `ambient_tangent_zero_at_absoluteValueGraph_origin`. The only remaining missing bridge is the
  -- chart-level proof that the immersed inclusion sends the intrinsic `w ≠ 0` to a nonzero
  -- ambient tangent vector at `p0`.
  let v : TangentSpace 𝓘(ℝ, Plane) (p0 : Plane) :=
    mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) (Subtype.val : absoluteValueGraph → Plane) p0 w
  have hv :
      v ∈ (mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane)
        (Subtype.val : absoluteValueGraph → Plane) p0).range ∧ v ≠ 0 :=
    pushforward_nonzero_tangent_mem_submanifold hImm p0 hw_ne
  have hv_zero : v = 0 :=
    ambient_tangent_zero_at_absoluteValueGraph_origin p0 hp0 hImm hv.1
  -- The cusp computation forces every ambient tangent at the origin to vanish, contradicting the
  -- nonzero tangent vector produced from the intrinsic one-manifold chart.
  exact hv.2 hv_zero
