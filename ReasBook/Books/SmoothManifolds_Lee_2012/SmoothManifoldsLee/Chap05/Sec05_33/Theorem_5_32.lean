import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Immersion

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe u𝕜 uE uH uM uN uE' uH' uE'' uH''

section UniquenessOfImmersedSubmanifoldStructures

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H}
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'}
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {K : ModelWithCorners 𝕜 E'' H''}
variable {N : Type uN} [TopologicalSpace N]
variable {ι : N → M}

-- Semantic search hit: `Diffeomorph.refl` and `Diffeomorph.refl_toEquiv`.
-- Local analogue: `exists_diffeomorph_of_submersion_characteristic_property` packages uniqueness
-- for a fixed carrier through an identity-on-points diffeomorphism.
/-- Helper for Theorem 5.32: on points where both source charts are valid, the identity map
between the two manifold structures is obtained by taking the first coordinate after the ambient
chart transition between the two immersion normal forms. -/
lemma id_writtenInImmersionCharts
    [ChartedSpace H' N] [IsManifold J (⊤ : WithTop ℕ∞) N]
    [ChartedSpace H'' N] [IsManifold K (⊤ : WithTop ℕ∞) N]
    {x : N}
    (hJx : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) ι x)
    (hKx : Manifold.IsImmersionAt K I (⊤ : WithTop ℕ∞) ι x) :
    Set.EqOn
      (((hKx.domChart.extend K) ∘ (id : N → N) ∘ (hJx.domChart.extend J).symm))
      (fun y : E' ↦
        Prod.fst
          (hKx.equiv.symm
            (I.extendCoordChange hJx.codChart hKx.codChart
              (hJx.equiv (y, (0 : hJx.complement))))))
      ((hJx.domChart.extend J).target ∩ (hJx.domChart.extend J).symm ⁻¹' hKx.domChart.source) := by
  intro y hy
  rcases hy with ⟨hyJtarget, hyKsource⟩
  -- Rewrite both immersion normal forms at the same point in the underlying topological space.
  have hyJsource : (hJx.domChart.extend J).symm y ∈ hJx.domChart.source := by
    simpa [hJx.domChart.extend_source (I := J)] using (hJx.domChart.extend J).map_target hyJtarget
  have hyCodSource : ι ((hJx.domChart.extend J).symm y) ∈ hJx.codChart.source :=
    hJx.source_subset_preimage_source hyJsource
  have hJchart :
      hJx.codChart.extend I (ι ((hJx.domChart.extend J).symm y)) =
        hJx.equiv (y, (0 : hJx.complement)) := by
    simpa [Function.comp] using hJx.writtenInCharts hyJtarget
  have hTransition :
      I.extendCoordChange hJx.codChart hKx.codChart (hJx.equiv (y, (0 : hJx.complement))) =
        hKx.codChart.extend I (ι ((hJx.domChart.extend J).symm y)) := by
    -- The ambient chart-change map is exactly `codChart.extend ∘ codChart.extend.symm`.
    have hyCodExtendSource :
        ι ((hJx.domChart.extend J).symm y) ∈ (hJx.codChart.extend I).source := by
      simpa [hJx.codChart.extend_source (I := I)] using hyCodSource
    have hyCodExtendTarget :
        hJx.codChart.extend I (ι ((hJx.domChart.extend J).symm y)) ∈
          (hJx.codChart.extend I).target := by
      exact (hJx.codChart.extend I).map_source hyCodExtendSource
    have hJchartSymm :
        (hJx.codChart.extend I).symm (hJx.equiv (y, (0 : hJx.complement))) =
          ι ((hJx.domChart.extend J).symm y) := by
      rw [← hJchart]
      exact (hJx.codChart.extend I).left_inv hyCodExtendSource
    simpa [ModelWithCorners.extendCoordChange] using
      congrArg (hKx.codChart.extend I) hJchartSymm
  have hyKdomSource : (hJx.domChart.extend J).symm y ∈ hKx.domChart.source := by
    simpa using hyKsource
  have hyKdomExtendSource :
      (hJx.domChart.extend J).symm y ∈ (hKx.domChart.extend K).source := by
    simpa [hKx.domChart.extend_source (I := K)] using hyKdomSource
  have hyKtarget :
      hKx.domChart.extend K ((hJx.domChart.extend J).symm y) ∈ (hKx.domChart.extend K).target := by
    exact (hKx.domChart.extend K).map_source hyKdomExtendSource
  have hKchart :
      hKx.codChart.extend I (ι ((hJx.domChart.extend J).symm y)) =
        hKx.equiv
          (hKx.domChart.extend K ((hJx.domChart.extend J).symm y), (0 : hKx.complement)) := by
    have hKwritten :
        hKx.codChart.extend I
            (ι (hKx.domChart.symm (hKx.domChart ((hJx.domChart.extend J).symm y)))) =
          hKx.equiv
            (hKx.domChart.extend K ((hJx.domChart.extend J).symm y), (0 : hKx.complement)) := by
      simpa [Function.comp] using hKx.writtenInCharts hyKtarget
    rw [hKx.domChart.left_inv hyKdomSource] at hKwritten
    exact hKwritten
  -- After applying the inverse linear equivalence, the first coordinate recovers the `K`-chart.
  calc
    ((hKx.domChart.extend K) ∘ (id : N → N) ∘ (hJx.domChart.extend J).symm) y
        = hKx.domChart.extend K ((hJx.domChart.extend J).symm y) := by
            simp
    _ = Prod.fst
          (hKx.equiv.symm
            (hKx.equiv
              (hKx.domChart.extend K ((hJx.domChart.extend J).symm y), (0 : hKx.complement)))) := by
            simp
    _ = Prod.fst
          (hKx.equiv.symm
            (hKx.codChart.extend I (ι ((hJx.domChart.extend J).symm y)))) := by
            rw [hKchart]
    _ = Prod.fst
          (hKx.equiv.symm
            (I.extendCoordChange hJx.codChart hKx.codChart
              (hJx.equiv (y, (0 : hJx.complement))))) := by
            rw [hTransition.symm]

/-- Helper for Theorem 5.32: the explicit ambient chart comparison map coming from the two
immersion normal forms is smooth on the source chart target. -/
lemma immersionChartComparison_contDiffWithinAt
    [ChartedSpace H' N] [IsManifold J (⊤ : WithTop ℕ∞) N]
    [ChartedSpace H'' N] [IsManifold K (⊤ : WithTop ℕ∞) N]
    {x : N}
    (hJx : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) ι x)
    (hKx : Manifold.IsImmersionAt K I (⊤ : WithTop ℕ∞) ι x) :
    let xJ := hJx.domChart.extend J x
    let comparison :=
      (((ContinuousLinearMap.fst 𝕜 E'' hKx.complement).comp
          hKx.equiv.symm.toContinuousLinearMap) ∘
        I.extendCoordChange hJx.codChart hKx.codChart ∘
        fun y : E' ↦ hJx.equiv (y, (0 : hJx.complement)))
    ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞) comparison (hJx.domChart.extend J).target xJ := by
  let xJ := hJx.domChart.extend J x
  let frontL : E' →L[𝕜] E :=
    hJx.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E' hJx.complement)
  let backL : E →L[𝕜] E'' :=
    (ContinuousLinearMap.fst 𝕜 E'' hKx.complement).comp hKx.equiv.symm.toContinuousLinearMap
  let comparison :
      E' → E'' :=
    backL ∘ I.extendCoordChange hJx.codChart hKx.codChart ∘ frontL
  have hxJsource : x ∈ (hJx.domChart.extend J).source := by
    simpa [xJ, hJx.domChart.extend_source (I := J)] using hJx.mem_domChart_source
  have hxJtarget : xJ ∈ (hJx.domChart.extend J).target := by
    exact (hJx.domChart.extend J).map_source hxJsource
  have hFront :
      ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞)
        (fun y : E' ↦ hJx.equiv (y, (0 : hJx.complement)))
        (hJx.domChart.extend J).target xJ := by
    -- The source-side normal form is a continuous linear map.
    simpa [frontL, ContinuousLinearMap.comp_apply, Function.comp] using
      (frontL.contDiff.contDiffWithinAt :
        ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞)
          (frontL : E' → E)
          (hJx.domChart.extend J).target xJ)
  have hFrontMaps :
      Set.MapsTo
        (fun y : E' ↦ hJx.equiv (y, (0 : hJx.complement)))
        (hJx.domChart.extend J).target (Set.range I) := by
    intro y hy
    exact (hJx.codChart.extend_target_subset_range (I := I)) <|
      hJx.target_subset_preimage_target hy
  have hxJsymm : (hJx.domChart.extend J).symm xJ = x := by
    simpa [xJ] using hJx.domChart.extend_left_inv (I := J) hJx.mem_domChart_source
  have hFrontAt :
      (fun y : E' ↦ hJx.equiv (y, (0 : hJx.complement))) xJ =
        hJx.codChart.extend I (ι x) := by
    -- Evaluate the `J`-immersion chart formula at the base point.
    calc
      (fun y : E' ↦ hJx.equiv (y, (0 : hJx.complement))) xJ
          = hJx.codChart.extend I (ι ((hJx.domChart.extend J).symm xJ)) := by
              simpa [Function.comp] using (hJx.writtenInCharts hxJtarget).symm
      _ = hJx.codChart.extend I (ι x) := by rw [hxJsymm]
  have hTransition :
      ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞)
        ((I.extendCoordChange hJx.codChart hKx.codChart) ∘
          fun y : E' ↦ hJx.equiv (y, (0 : hJx.complement)))
        (hJx.domChart.extend J).target xJ := by
    -- The only nonlinear piece is the ambient chart transition in `M`.
    exact
      (I.contDiffWithinAt_extendCoordChange'
        hJx.codChart_mem_maximalAtlas hKx.codChart_mem_maximalAtlas
        hJx.mem_codChart_source hKx.mem_codChart_source).comp_of_eq xJ hFront hFrontMaps
        hFrontAt
  -- Postcompose with the inverse linear equivalence and the first-coordinate projection.
  simpa [comparison, backL, frontL, ContinuousLinearMap.comp_apply, Function.comp] using
    (backL.contDiff.contDiffAt.comp_contDiffWithinAt xJ hTransition)

/-- Helper for Theorem 5.32: in the chosen source chart, the identity map agrees near the base
point with the explicit smooth comparison map coming from the two immersion normal forms. -/
lemma immersionChartedIdentity_contDiffWithinAt
    [ChartedSpace H' N] [IsManifold J (⊤ : WithTop ℕ∞) N]
    [ChartedSpace H'' N] [IsManifold K (⊤ : WithTop ℕ∞) N]
    {x : N}
    (hJx : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) ι x)
    (hKx : Manifold.IsImmersionAt K I (⊤ : WithTop ℕ∞) ι x) :
    let xJ := hJx.domChart.extend J x
    let chartedId :=
      (hKx.domChart.extend K) ∘ (id : N → N) ∘ (hJx.domChart.extend J).symm
    ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞) chartedId (hJx.domChart.extend J).target xJ := by
  let xJ := hJx.domChart.extend J x
  let chartedId :
      E' → E'' :=
    (hKx.domChart.extend K) ∘ (id : N → N) ∘ (hJx.domChart.extend J).symm
  let comparison :
      E' → E'' :=
    (((ContinuousLinearMap.fst 𝕜 E'' hKx.complement).comp
        hKx.equiv.symm.toContinuousLinearMap) ∘
      I.extendCoordChange hJx.codChart hKx.codChart ∘
      fun y : E' ↦ hJx.equiv (y, (0 : hJx.complement)))
  have hComparison :
      ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞) comparison (hJx.domChart.extend J).target xJ := by
    simpa [xJ, comparison] using immersionChartComparison_contDiffWithinAt (I := I) hJx hKx
  have hOverlap :
      (hJx.domChart.extend J).target ∩ (hJx.domChart.extend J).symm ⁻¹' hKx.domChart.source ∈
        nhdsWithin xJ (hJx.domChart.extend J).target := by
    have hPreimage :
        (hJx.domChart.extend J).symm ⁻¹' hKx.domChart.source ∈ nhds xJ := by
      exact (hJx.domChart.extend_preimage_mem_nhds (I := J) hJx.mem_domChart_source
        (hKx.domChart.open_source.mem_nhds hKx.mem_domChart_source))
    exact inter_mem_nhdsWithin _ hPreimage
  have hChartedIdEq :
      chartedId =ᶠ[nhdsWithin xJ (hJx.domChart.extend J).target] comparison := by
    filter_upwards [hOverlap] with y hy
    exact id_writtenInImmersionCharts hJx hKx hy
  have hChartedId :
      ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞) chartedId (hJx.domChart.extend J).target xJ := by
    -- Replace the charted identity map by the explicit comparison map on an overlap neighborhood.
    have hxJsource : x ∈ (hJx.domChart.extend J).source := by
      simpa [xJ, hJx.domChart.extend_source (I := J)] using hJx.mem_domChart_source
    have hxJsymm : (hJx.domChart.extend J).symm xJ = x := by
      simpa [xJ] using hJx.domChart.extend_left_inv (I := J) hJx.mem_domChart_source
    have hxOverlap :
        xJ ∈ (hJx.domChart.extend J).target ∩
          (hJx.domChart.extend J).symm ⁻¹' hKx.domChart.source := by
      refine ⟨(hJx.domChart.extend J).map_source hxJsource, ?_⟩
      change (hJx.domChart.extend J).symm xJ ∈ hKx.domChart.source
      rw [hxJsymm]
      exact hKx.mem_domChart_source
    apply hComparison.congr_of_eventuallyEq hChartedIdEq
    exact id_writtenInImmersionCharts hJx hKx hxOverlap
  simpa [xJ, chartedId] using hChartedId

/-- Helper for Theorem 5.32: the identity map is smooth at a point whenever the same injective map
into `M` is an immersion for both manifold structures there. -/
lemma contMDiffAt_id_of_isImmersionAt_pair
    [ChartedSpace H' N] [IsManifold J (⊤ : WithTop ℕ∞) N]
    [ChartedSpace H'' N] [IsManifold K (⊤ : WithTop ℕ∞) N]
    {x : N}
    (hJx : Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) ι x)
    (hKx : Manifold.IsImmersionAt K I (⊤ : WithTop ℕ∞) ι x) :
    ContMDiffAt J K (⊤ : WithTop ℕ∞) (id : N → N) x := by
  let xJ := hJx.domChart.extend J x
  have hChartedId :
      ContDiffWithinAt 𝕜 (⊤ : WithTop ℕ∞)
        (((hKx.domChart.extend K) ∘ (id : N → N) ∘ (hJx.domChart.extend J).symm))
        (hJx.domChart.extend J).target xJ := by
    -- Use the isolated chart-comparison lemma instead of redoing the transport-heavy setup here.
    simpa [xJ] using immersionChartedIdentity_contDiffWithinAt (I := I) hJx hKx
  -- Convert the chart-level smoothness statement back to the manifold-level criterion.
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas
    hJx.domChart_mem_maximalAtlas hKx.domChart_mem_maximalAtlas
    hJx.mem_domChart_source hKx.mem_domChart_source]
  refine ⟨continuousWithinAt_id, ?_⟩
  simpa [Set.preimage_univ, Set.inter_univ] using
    hChartedId.congr_set (hJx.domChart.extend_target_eventuallyEq (I := J) hJx.mem_domChart_source)

/-- Helper for Theorem 5.32: if the same topological space carries two immersed-submanifold
structures through the same map `ι`, then the identity map between those structures is smooth. -/
lemma contMDiff_id_of_isImmersion_pair
    [ChartedSpace H' N] [IsManifold J (⊤ : WithTop ℕ∞) N]
    [ChartedSpace H'' N] [IsManifold K (⊤ : WithTop ℕ∞) N]
    (hJ : Manifold.IsImmersion J I (⊤ : WithTop ℕ∞) ι)
    (hK : Manifold.IsImmersion K I (⊤ : WithTop ℕ∞) ι) :
    ContMDiff J K (⊤ : WithTop ℕ∞) (id : N → N) := by
  -- Smoothness is checked pointwise using the two local immersion normal forms.
  intro x
  exact contMDiffAt_id_of_isImmersionAt_pair (hJ.isImmersionAt x) (hK.isImmersionAt x)

/-- Theorem 5.32: if a fixed topological space `N` is identified with an immersed submanifold of
`M` by an injective map `ι : N → M`, and two smooth manifold structures on that same `N` make `ι`
an immersion, then there is a unique diffeomorphism between the two structures whose underlying
equivalence is `Equiv.refl N`. -/
theorem existsUnique_diffeomorph_refl_of_isImmersedSubmanifold
    [ChartedSpace H' N] [IsManifold J (⊤ : WithTop ℕ∞) N]
    [ChartedSpace H'' N] [IsManifold K (⊤ : WithTop ℕ∞) N]
    (hι : Function.Injective ι)
    (hJ : Manifold.IsImmersion J I (⊤ : WithTop ℕ∞) ι)
    (hK : Manifold.IsImmersion K I (⊤ : WithTop ℕ∞) ι) :
    ∃! Φ : N ≃ₘ⟮J, K⟯ N, Φ.toEquiv = Equiv.refl N := by
  let Φ : N ≃ₘ⟮J, K⟯ N := {
    toEquiv := Equiv.refl N
    contMDiff_toFun := by
      simpa using
        (contMDiff_id_of_isImmersion_pair (I := I) hJ hK).of_le (by simp)
    contMDiff_invFun := by
      simpa using
        (contMDiff_id_of_isImmersion_pair (I := I) hK hJ).of_le (by simp) }
  -- Package the identity-on-points diffeomorphism, then use injectivity of `toEquiv`.
  refine ⟨Φ, rfl, ?_⟩
  intro Ψ hΨ
  ext x
  apply hι
  have hΨfun : (Ψ.toEquiv : N → N) = id := by
    simpa using congrArg Equiv.toFun hΨ
  have hx : Ψ.toEquiv x = Φ.toEquiv x := by
    simpa [Φ] using congrFun hΨfun x
  exact congrArg ι hx

end UniquenessOfImmersedSubmanifoldStructures
