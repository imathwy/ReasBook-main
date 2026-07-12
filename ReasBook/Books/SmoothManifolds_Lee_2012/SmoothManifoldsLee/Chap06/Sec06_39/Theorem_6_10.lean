import SmoothManifolds_Lee_2012.Chap05.Sec05_30.Definition_5_30_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_38.Definition_6_38_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_38.Lemma_6_6
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ContDiff Manifold Topology

-- Domain sampling for this refine pass:
-- * source-facing set: `{y : N | IsCriticalValue I J F y}`;
-- * core/canonical owner: `has_measure_zero_in_manifold`;
-- * bridge/view: `has_measure_zero_in_manifold.extChartAt_volume_eq_zero`.

universe uE uE' uH uH' uM uN

section

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable [MeasurableSpace E'] [BorelSpace E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Helper for Theorem 6.10: a `C¹` map from a lower-dimensional finite-dimensional real vector
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

/-- Helper for Theorem 6.10: every critical value is, by definition, a value in the range. -/
private theorem criticalValues_subset_range {F : M → N} :
    {y : N | IsCriticalValue I J F y} ⊆ Set.range F := by
  intro y hy
  -- Unpack a critical value into a critical point lying over it.
  rcases (isCriticalValue_iff_exists_critical_point F y).1 hy with
    ⟨p, rfl, -⟩
  exact ⟨p, rfl⟩

/-- Helper for Theorem 6.10: when the source model dimension is strictly smaller than the target
model dimension, every value in the range is critical. -/
private theorem range_subset_criticalValues_of_model_finrank_lt {F : M → N}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    Set.range F ⊆ {y : N | IsCriticalValue I J F y} := by
  intro y hy
  -- Rewrite a range point as `F p` and invoke the dimension obstruction on surjectivity.
  rcases hy with ⟨p, rfl⟩
  have hcritical : IsCriticalValue I J F (F p) := by
    rw [isCriticalValue_iff_exists_critical_point]
    exact ⟨p, rfl, isCriticalPoint_of_model_finrank_lt hdim p⟩
  exact hcritical

/-- Helper for Theorem 6.10: in the low-dimensional case, the critical values coincide with the
entire range. -/
private theorem criticalValues_eq_range_of_model_finrank_lt {F : M → N}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    {y : N | IsCriticalValue I J F y} = Set.range F := by
  -- Combine the easy inclusion from the definition with the dimension-forcing converse.
  exact Set.Subset.antisymm criticalValues_subset_range
    (range_subset_criticalValues_of_model_finrank_lt hdim)

/-- Helper for Theorem 6.10: in the low-dimensional case, Sard's theorem reduces to the
measure-zero statement for `Set.range F`. -/
private theorem criticalValues_hasMeasureZero_of_rangeHasMeasureZero {F : M → N}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E')
    (hRange : has_measure_zero_in_manifold J (Set.range F)) :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  -- Rewrite the critical-value set as the full range, then reuse the range-nullity input.
  simpa [criticalValues_eq_range_of_model_finrank_lt hdim] using hRange

/-- Helper for Theorem 6.10: for a fixed target chart, the chart image of `Set.range F` has
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
      rcases hy with ⟨x, -, rfl⟩
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

/-- Helper for Theorem 6.10: when `Module.finrank ℝ E < Module.finrank ℝ E'`, it remains to prove
that the smooth image `Set.range F` has measure zero in `N`. -/
private theorem range_hasMeasureZero_inManifold_of_contMDiff_of_model_finrank_lt {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    has_measure_zero_in_manifold J (Set.range F) := by
  -- Work directly with the owner definition of manifold measure zero.
  intro μ hμ e he
  exact
    chartRangeImage_hasMeasureZero_of_model_finrank_lt
      (I := I) (J := J) (F := F) hF hdim μ hμ he

/-- Helper for Theorem 6.10: in equal dimensions, postcomposing a chart operator with the inverse
linear equivalence preserves surjectivity. -/
private theorem surjective_coordinateOperator_of_surjective_linearized
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') {A : E →L[ℝ] E'}
    (hA :
      Function.Surjective
        ((ContinuousLinearEquiv.ofFinrankEq heq).symm.toContinuousLinearMap.comp A)) :
    Function.Surjective A := by
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq heq
  -- Apply surjectivity to the inverse-image of the requested target vector.
  intro z
  obtain ⟨w, hw⟩ := hA (L.symm z)
  refine ⟨w, ?_⟩
  apply L.symm.injective
  simpa [L, ContinuousLinearMap.comp_apply] using hw

/-- Helper for Theorem 6.10: surjectivity of the fixed-chart coordinate operator forces
surjectivity of the manifold derivative. -/
private theorem surjective_mfderiv_of_surjective_coordinateOperator {F : M → N}
    {x₀ x : M} {y₀ : N}
    (hx : x ∈ (extChartAt I x₀).source) (hy : F x ∈ (extChartAt J y₀).source)
    (hA :
      Function.Surjective
        ((mfderiv% (extChartAt J y₀) (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x)))) :
    Function.Surjective (mfderiv I J F x) := by
  -- Solve the target vector in chart coordinates, then cancel the two invertible chart
  -- derivatives on the outside of the coordinate operator.
  intro v
  obtain ⟨w, hw⟩ := hA ((mfderiv% (extChartAt J y₀) (F x)) v)
  refine ⟨(mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x)) w, ?_⟩
  apply (isInvertible_mfderiv_extChartAt (I := J) (x := y₀) (y := F x) hy).injective
  simpa [ContinuousLinearMap.comp_apply] using hw

/-- Helper for Theorem 6.10: a non-surjective endomorphism of a finite-dimensional real vector
space has zero determinant. -/
private theorem det_eq_zero_of_not_surjective_endomorphism {A : E →L[ℝ] E}
    (hA : ¬ Function.Surjective A) : A.det = 0 := by
  -- In finite dimension, non-surjectivity implies non-injectivity, so the kernel is nontrivial.
  have hker : A.ker ≠ ⊥ := by
    intro hker
    apply hA
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (show Module.finrank ℝ E = Module.finrank ℝ E by simp)).1 <|
        LinearMap.ker_eq_bot.1 hker
  simpa [ContinuousLinearMap.det] using
    (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker

/-- Helper for Theorem 6.10: at a critical point, the equal-dimensional linearized coordinate
operator has zero determinant. -/
private theorem linearizedCoordinateOperator_det_eq_zero_of_isCriticalPoint {F : M → N}
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') {x₀ x : M} {y₀ : N}
    (hx : x ∈ (extChartAt I x₀).source) (hy : F x ∈ (extChartAt J y₀).source)
    (hcrit : IsCriticalPoint I J F x) :
    ContinuousLinearMap.det
      ((ContinuousLinearEquiv.ofFinrankEq heq).symm.toContinuousLinearMap.comp
        ((mfderiv% (extChartAt J y₀) (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x)))) = 0 := by
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq heq
  let A : E →L[ℝ] E' :=
    (mfderiv% (extChartAt J y₀) (F x)) ∘L
      (mfderiv I J F x) ∘L
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
  let B : E →L[ℝ] E := L.symm.toContinuousLinearMap.comp A
  -- Route correction: isolate the finite-dimensional algebra from the chart derivative
  -- normalization, so the remaining equal-branch work is only the `HasFDerivWithinAt` assembly.
  have hnotSurj : ¬ Function.Surjective B := by
    intro hB
    have hA : Function.Surjective A :=
      surjective_coordinateOperator_of_surjective_linearized (E := E) (E' := E') heq <| by
        simpa [A, B, L] using hB
    have hmfderiv : Function.Surjective (mfderiv I J F x) :=
      surjective_mfderiv_of_surjective_coordinateOperator (I := I) (J := J)
        (F := F) hx hy <| by
          simpa [A] using hA
    exact
      ((isCriticalPoint_iff_not_isRegularPoint (I := I) (J := J) F x).1 hcrit) <|
        (isRegularPoint_iff_surjective_mfderiv (I := I) (J := J) F x).2 hmfderiv
  -- Apply the endomorphism determinant criterion after the linearization step.
  simpa [A, B, L] using det_eq_zero_of_not_surjective_endomorphism (E := E) hnotSurj

/-- Helper for Theorem 6.10: a source-chart coordinate in the target comes from a point in the
corresponding chart source. -/
private theorem extChartAt_symm_mem_source_of_mem_target {x₀ : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source := by
  -- Unpack target membership by applying the inverse chart map.
  exact (extChartAt I x₀).map_target hz

/-- Helper for Theorem 6.10: applying a source chart after its inverse returns the original
coordinate point on the target. -/
private theorem extChartAt_apply_symm_of_mem_target {x₀ : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀) ((extChartAt I x₀).symm z) = z := by
  -- This is the standard right-inverse identity on the chart target.
  exact (extChartAt I x₀).right_inv hz

/-- Helper for Theorem 6.10: in the equal model-dimension case, each preferred target-chart image
of the critical values has measure zero. -/
private theorem chartCriticalValues_hasMeasureZero_of_model_finrank_eq
    [SecondCountableTopology M] {F : M → N} (hF : ContMDiff I J ∞ F)
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') (μ : Measure E') [μ.IsAddHaarMeasure]
    (y₀ : N) :
    μ ((extChartAt J y₀) '' ({y : N | IsCriticalValue I J F y} ∩ (extChartAt J y₀).source)) = 0 := by
  -- TODO: the equal-dimensional frontier is now reduced to a single preferred-chart transport.
  -- The finished scaffold covers the critical-point locus by source charts and reduces each piece
  -- to the Jacobian theorem for the linearized representative `L.symm ∘ extChartAt J y₀ ∘ F ∘
  -- (extChartAt I p.1).symm`. What remains is a clean target-side `HasMFDerivAt` bridge for
  -- `extChartAt J y₀` in the model codomain, plus the final normalization from
  -- `extChartAt I p.1 ((extChartAt I p.1).symm x)` back to `x`.
  sorry

/-- Helper for Theorem 6.10: the equal-dimension Sard branch is obtained by reducing to the
preferred-chart cover furnished by Lemma 6.6. -/
private theorem criticalValues_hasMeasureZero_of_model_finrank_eq {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  intro μ hμ e he
  let _ : MeasureSpace E' := ⟨μ⟩
  let _ : (volume : Measure E').IsAddHaarMeasure := by
    simpa using hμ
  -- Upgrade the preferred-chart nullity statement to the manifold owner by covering the critical
  -- values with their own preferred target charts.
  have howner :
      has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
    refine
      has_measure_zero_in_manifold_of_chart_cover (I := J)
        (A := {y : N | IsCriticalValue I J F y}) (e := fun y : N ↦ chartAt H' y) ?_ ?_ ?_
    · -- Each preferred chart belongs to the maximal atlas.
      intro y
      simpa using IsManifold.chart_mem_maximalAtlas (I := J) (n := ∞) y
    · -- Every critical value lies in the source of its own preferred chart.
      intro y hy
      exact Set.mem_iUnion.2 ⟨y, mem_chart_source H' y⟩
    · -- Apply the chartwise equal-dimension theorem on each preferred target chart.
      intro y
      simpa using
        chartCriticalValues_hasMeasureZero_of_model_finrank_eq
          (I := I) (J := J) (F := F) hF heq volume y
  exact howner μ hμ e he

/-- Helper for Theorem 6.10: in the strict target-dimension case, each target-chart image of the
critical values should be reduced to the Euclidean Sard core on a coordinate representative. -/
private theorem chartCriticalValues_hasMeasureZero_of_targetFinrank_lt_sourceFinrank
    [SecondCountableTopology M] {F : M → N} (hF : ContMDiff I J ∞ F)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E) (μ : Measure E')
    [μ.IsAddHaarMeasure] {e : OpenPartialHomeomorph N H'} (he : e ∈ IsManifold.maximalAtlas J ∞ N) :
    μ (((e.extend J) '' ({y : N | IsCriticalValue I J F y} ∩ e.source))) = 0 := by
  -- TODO: isolate the Euclidean Sard core for chart representatives `E → E'` with
  -- `Module.finrank ℝ E' < Module.finrank ℝ E`, then use the same source-chart decomposition as in
  -- the equal-dimension branch to lift that nullity statement back to manifolds.
  sorry

/-- Helper for Theorem 6.10: the strict target-dimension branch is reduced to the corresponding
chartwise Euclidean Sard statement. -/
private theorem criticalValues_hasMeasureZero_of_targetFinrank_lt_sourceFinrank {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E) :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  -- Unfold the owner definition and reduce immediately to the chartwise strict branch.
  intro μ hμ e he
  let _ : μ.IsAddHaarMeasure := hμ
  exact
    chartCriticalValues_hasMeasureZero_of_targetFinrank_lt_sourceFinrank
      (I := I) (J := J) (F := F) hF hlt μ (e := e) he

/-- Helper for Theorem 6.10: once the low-dimensional range case is removed, the complementary
dimension regime is an immediate split between the equal-dimension Jacobian branch and the strict
target-dimension Sard branch. -/
private theorem criticalValues_hasMeasureZero_of_targetFinrank_le_sourceFinrank {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (hle : Module.finrank ℝ E' ≤ Module.finrank ℝ E) :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  -- Split the remaining work by whether the model dimensions are equal or strictly ordered.
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · -- The equal-dimension case is the fixed-dimension Jacobian branch.
    exact criticalValues_hasMeasureZero_of_model_finrank_eq hF heq.symm
  · -- The strict target-dimension case is the genuine Euclidean Sard branch.
    exact criticalValues_hasMeasureZero_of_targetFinrank_lt_sourceFinrank hF hlt

/-- Theorem 6.10 (Sard's Theorem): if `F : M → N` is a smooth map between smooth manifolds with
or without boundary, then the set of critical values of `F` has measure zero in `N`. -/
theorem critical_values_has_measure_zero_in_manifold_of_contMDiff {F : M → N}
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    (hF : ContMDiff I J ∞ F) :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  -- Route correction: split first by the model-dimension relation, because the low-dimensional
  -- branch collapses immediately to range-nullity while the complementary branch is genuine Sard.
  by_cases hdim : Module.finrank ℝ E < Module.finrank ℝ E'
  · -- Reduce the low-dimensional branch to the already isolated range-nullity statement.
    exact
      criticalValues_hasMeasureZero_of_rangeHasMeasureZero hdim
        (range_hasMeasureZero_inManifold_of_contMDiff_of_model_finrank_lt hF hdim)
  · -- The complementary branch is exactly the chartwise Euclidean Sard frontier.
    exact
      criticalValues_hasMeasureZero_of_targetFinrank_le_sourceFinrank
        hF (Nat.le_of_not_gt hdim)

end

section

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Preferred-chart formulation of Theorem 6.10, derived from the manifold owner
`critical_values_has_measure_zero_in_manifold_of_contMDiff`. -/
theorem critical_values_volume_extChartAt_eq_zero_of_contMDiff {F : M → N}
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    (hF : ContMDiff I J ∞ F) (x : N) :
    volume ((extChartAt J x) '' ({y : N | IsCriticalValue I J F y} ∩ (extChartAt J x).source)) =
      0 := by
  exact
    has_measure_zero_in_manifold.extChartAt_volume_eq_zero
      J (critical_values_has_measure_zero_in_manifold_of_contMDiff hF) x

end
