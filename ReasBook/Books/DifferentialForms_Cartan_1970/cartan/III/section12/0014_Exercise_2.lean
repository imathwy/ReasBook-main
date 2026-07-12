import Mathlib
import DifferentialForms_Cartan_1970.III.section12.«0014_Exercise_2».Index

-- Semantic search tool `lean_leansearch` was unavailable in this environment; notation was
-- verified locally against mathlib and nearby repository precedent. The holomorphic-neighborhood
-- owner for this file was checked against `AnalyticOnNhd`, `circleMap`, and Euclidean Hausdorff
-- measure on the complex plane.

-- Declarations for this item will be appended below by the statement pipeline.

open Complex MeasureTheory
open scoped MeasureTheory Real Manifold

section

variable {f : ℂ → ℂ} {R : ℝ}
variable (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))

/- 
The next geometric interval-image lemmas are independent of the holomorphic data `hf`.
-/

/-- Helper for Exercise 2: in dimension `1`, Euclidean Hausdorff measure coincides with ordinary
Hausdorff measure. -/
lemma euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] :
    (μHE[1] : Measure X) = (μH[1] : Measure X) := by
  -- Identify the model-space normalization scalar by transporting the one-dimensional Euclidean
  -- model to `ℝ`, where Hausdorff measure already agrees with Lebesgue measure.
  let eIso : EuclideanSpace ℝ (Fin 1) ≃ᵢ ℝ := by
    let e : EuclideanSpace ℝ (Fin 1) ≃ ℝ :=
      (WithLp.equiv 2 (Fin 1 → ℝ)).trans (Equiv.funUnique (Fin 1) ℝ)
    refine IsometryEquiv.mk e ?_
    refine Isometry.of_dist_eq ?_
    intro x y
    change
      dist ((WithLp.equiv 2 (Fin 1 → ℝ) x) 0) ((WithLp.equiv 2 (Fin 1 → ℝ) y) 0) = dist x y
    have hx : x = WithLp.toLp 2 (Pi.single 0 (x.ofLp 0)) := by
      ext i
      have hi : i = 0 := by simpa using (Fin.eq_zero i)
      simp [Pi.single_apply, hi]
    have hy : y = WithLp.toLp 2 (Pi.single 0 (y.ofLp 0)) := by
      ext i
      have hi : i = 0 := by simpa using (Fin.eq_zero i)
      simp [Pi.single_apply, hi]
    rw [hx, hy]
    simp
  have hHausdorffModel : (μH[1] : Measure (EuclideanSpace ℝ (Fin 1))) = volume := by
    let e : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ := eIso.toHomeomorph.toMeasurableEquiv
    refine e.map_measurableEquiv_injective ?_
    have hHausdorffMap :
        Measure.map (fun x ↦ e x) (μH[1] : Measure (EuclideanSpace ℝ (Fin 1))) = volume := by
      -- The explicit isometry transports Hausdorff measure to `ℝ`, where it is already `volume`.
      rw [show Measure.map (fun x ↦ e x) (μH[1] : Measure (EuclideanSpace ℝ (Fin 1))) =
          (μH[1] : Measure ℝ) by
            change Measure.map e (μH[1] : Measure (EuclideanSpace ℝ (Fin 1))) =
              (μH[1] : Measure ℝ)
            exact (eIso.measurePreserving_hausdorffMeasure 1).map_eq,
        MeasureTheory.hausdorffMeasure_real]
    have hZero : eIso 0 = 0 := by
      simp [eIso]
    have hVolumeMap :
        Measure.map (fun x ↦ e x) (volume : Measure (EuclideanSpace ℝ (Fin 1))) = volume := by
      -- The same map is affine-linear and isometric, so it preserves Lebesgue measure as well.
      simpa [e] using
        ((eIso.toRealLinearIsometryEquivOfMapZero hZero).measurePreserving.map_eq)
    rw [hHausdorffMap, hVolumeMap]
  letI : (μH[1] : Measure (EuclideanSpace ℝ (Fin 1))).IsAddHaarMeasure := by
    simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℝ (Fin 1)))
  have hscalar :
      MeasureTheory.Measure.addHaarScalarFactor
          (volume : Measure (EuclideanSpace ℝ (Fin 1)))
          (μH[1] : Measure (EuclideanSpace ℝ (Fin 1))) = 1 := by
    -- Once the model Hausdorff measure is identified with `volume`, the scalar collapses to `1`.
    simpa [hHausdorffModel] using
      (MeasureTheory.Measure.addHaarScalarFactor_self
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 1)))))
  simpa [MeasureTheory.Measure.euclideanHausdorffMeasure_def, hscalar]

/-- Helper for Exercise 2: adjoining closed interval images concatenate exactly. -/
lemma image_Icc_union_image_Icc_eq_image_Icc
    {γ : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    γ '' Set.Icc a b ∪ γ '' Set.Icc b c = γ '' Set.Icc a c := by
  -- Push the standard interval union identity through the map `γ`.
  rw [← Set.image_union]
  congr 1
  exact Set.Icc_union_Icc_eq_Icc hab hbc

/-- Helper for Exercise 2: if `γ` is injective on a larger closed interval, then the images of two
adjacent subintervals meet only at the shared endpoint. -/
lemma image_Icc_inter_image_Icc_subset_shared_endpoint
    {γ : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hinj : Set.InjOn γ (Set.Icc a c)) :
    (γ '' Set.Icc a b) ∩ (γ '' Set.Icc b c) ⊆ {γ b} := by
  intro z hz
  rcases hz with ⟨hzLeft, hzRight⟩
  rcases hzLeft with ⟨x, hx, rfl⟩
  rcases hzRight with ⟨y, hy, hxy⟩
  have hx' : x ∈ Set.Icc a c := ⟨hx.1, hx.2.trans hbc⟩
  have hy' : y ∈ Set.Icc a c := ⟨hab.trans hy.1, hy.2⟩
  have hxy' : x = y := hinj hx' hy' hxy.symm
  have hxb : x = b := by
    refine le_antisymm ?_ ?_
    · exact hx.2
    · simpa [hxy'] using hy.1
  simp [hxb]

/-- Helper for Exercise 2: adjacent subinterval images of an injective curve have zero Euclidean
Hausdorff `1`-measure overlap. -/
lemma image_Icc_adjacent_overlap_measure_zero_of_injOn
    {γ : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hinj : Set.InjOn γ (Set.Icc a c)) :
    μHE[1] ((γ '' Set.Icc a b) ∩ (γ '' Set.Icc b c)) = 0 := by
  -- Reduce the overlap to the singleton shared endpoint and use that Hausdorff measure has no
  -- atoms in dimension `1`.
  have hsubset :
      (γ '' Set.Icc a b) ∩ (γ '' Set.Icc b c) ⊆ {γ b} :=
    image_Icc_inter_image_Icc_subset_shared_endpoint hab hbc hinj
  haveI := MeasureTheory.Measure.noAtoms_hausdorff ℂ (show 0 < (1 : ℝ) by norm_num)
  have hzero : μHE[1] ({γ b} : Set ℂ) = 0 := by
    -- Normalize Euclidean Hausdorff `1`-measure to ordinary Hausdorff measure, then use
    -- atom-freeness.
    rw [euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one]
    simp
  exact le_antisymm ((measure_mono hsubset).trans hzero.le) (by simp)

/-- Helper for Exercise 2: for an injective continuous curve, the Euclidean Hausdorff
`1`-measure of the image of a concatenated interval is the sum of the measures of the adjacent
subarc images. -/
lemma image_Icc_union_measure_eq_of_injOn
    {γ : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcont : ContinuousOn γ (Set.Icc a c)) (hinj : Set.InjOn γ (Set.Icc a c)) :
    μHE[1] (γ '' Set.Icc a c) =
      μHE[1] (γ '' Set.Icc a b) + μHE[1] (γ '' Set.Icc b c) := by
  have hleftCont : ContinuousOn γ (Set.Icc a b) := by
    -- Restrict continuity from the large interval to the left subinterval.
    refine hcont.mono ?_
    intro x hx
    exact ⟨hx.1, hx.2.trans hbc⟩
  have hrightCont : ContinuousOn γ (Set.Icc b c) := by
    -- Restrict continuity from the large interval to the right subinterval.
    refine hcont.mono ?_
    intro x hx
    exact ⟨hab.trans hx.1, hx.2⟩
  have hleftMeas : MeasurableSet (γ '' Set.Icc a b) := by
    -- Continuous images of compact intervals are compact, hence measurable.
    exact (isCompact_Icc.image_of_continuousOn hleftCont).measurableSet
  have hrightMeas : MeasurableSet (γ '' Set.Icc b c) := by
    -- The same compact-image argument handles the right subinterval.
    exact (isCompact_Icc.image_of_continuousOn hrightCont).measurableSet
  have hunion :
      μHE[1] ((γ '' Set.Icc a b) ∪ (γ '' Set.Icc b c)) +
          μHE[1] ((γ '' Set.Icc a b) ∩ (γ '' Set.Icc b c)) =
        μHE[1] (γ '' Set.Icc a b) + μHE[1] (γ '' Set.Icc b c) := by
    simpa using
      (measure_union_add_inter (μ := (μHE[1] : Measure ℂ))
        (γ '' Set.Icc a b) hrightMeas)
  -- Rewrite the union as the full interval image, then collapse the overlap term to zero.
  simpa [image_Icc_union_image_Icc_eq_image_Icc hab hbc,
    image_Icc_adjacent_overlap_measure_zero_of_injOn hab hbc hinj] using hunion

include hf

/-- Helper for Exercise 2: the two closed half-arc images intersect only at the two global
endpoints, so their overlap has Hausdorff `1`-measure zero. -/
lemma boundary_circle_half_image_overlap_measure_zero
    (hR : 0 ≤ R) (hR0 : R ≠ 0)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    μHE[1]
        (((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∩
          ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π))) = 0 := by
  let γ : ℝ → ℂ := fun θ ↦ f (circleMap 0 R θ)
  have hsubset :
      (γ '' Set.Icc (0 : ℝ) π) ∩ (γ '' Set.Icc π (2 * π)) ⊆ {γ 0, γ π} := by
    intro z hz
    rcases hz with ⟨⟨θ, hθ, rfl⟩, φ, hφ, hEq⟩
    have hcircleEq : circleMap 0 R θ = circleMap 0 R φ := by
      apply hinj
      · exact circleMap_mem_sphere (0 : ℂ) hR θ
      · exact circleMap_mem_sphere (0 : ℂ) hR φ
      · exact hEq.symm
    by_cases hendpoint : θ = 0 ∧ φ = 2 * π
    · rcases hendpoint with ⟨rfl, rfl⟩
      simp [γ, boundary_circle_param_endpoint_eq (hf := hf)]
    · have hθleφ : θ ≤ φ := hθ.2.trans hφ.1
      have hθφ_nonneg : 0 ≤ φ - θ := sub_nonneg.mpr hθleφ
      have hθφ_le : φ - θ ≤ 2 * π := by
        nlinarith [hφ.2, hθ.1]
      have habs : |θ - φ| = φ - θ := by
        rw [abs_of_nonpos]
        · ring
        · exact sub_nonpos.mpr hθleφ
      have hneqTop : φ - θ ≠ 2 * π := by
        intro htop
        have hθ0 : θ = 0 := by
          linarith [hφ.2, hθ.1, htop]
        have hφTop : φ = 2 * π := by
          linarith [htop, hθ0]
        exact hendpoint ⟨hθ0, hφTop⟩
      have hdist : |θ - φ| < 2 * π := by
        rw [habs]
        exact lt_of_le_of_ne hθφ_le hneqTop
      have hθφ : θ = φ := eq_of_circleMap_eq hR0 hdist hcircleEq
      have hπ : θ = π := by linarith [hθ.2, hφ.1, hθφ]
      simp [γ, hπ]
  haveI := MeasureTheory.Measure.noAtoms_hausdorff ℂ (show 0 < (1 : ℝ) by norm_num)
  have hzeroHaus : (μH[1] : Measure ℂ) ({γ 0, γ π} : Set ℂ) = 0 := by
    simpa using (Finset.measure_zero ({γ 0, γ π} : Finset ℂ) (μ := μH[1]))
  have hzeroSet : μHE[1] ({γ 0, γ π} : Set ℂ) = 0 := by
    -- The two-dimensional ambient space still uses the same `1`-dimensional normalization.
    rw [euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one]
    exact hzeroHaus
  exact le_antisymm ((measure_mono hsubset).trans hzeroSet.le) (by simp)

omit hf

/-- Helper for Exercise 2: the Euclidean Hausdorff `1`-measure of a closed interval image is
bounded by the total variation of the curve on that interval. -/
lemma image_Icc_euclideanHausdorffMeasure_le_eVariation
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn γ (Set.Icc a b)) :
    μHE[1] (γ '' Set.Icc a b) ≤ eVariationOn γ (Set.Icc a b) := by
  -- Reparameterize by variation and use the `1`-Lipschitz natural parameterization.
  rw [euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one]
  rw [← naturalParameterization_image_eq_interval_image (γ := γ) hab hbv]
  exact hausdorffMeasure_naturalParameterization_image_le_variation (γ := γ) hab hbv

/-- Helper for Exercise 2: the variation of a `C¹` curve on a closed interval is bounded by the
integral of its speed. -/
lemma eVariationOn_Icc_le_integral_norm_deriv
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  have hInt : IntervalIntegrable (fun t : ℝ ↦ ‖deriv γ t‖) volume a b :=
    intervalIntegrable_norm_deriv_of_contDiffOn_Icc hab hγ
  have hnonnegAe :
      0 ≤ᵐ[volume.restrict (Set.Ioc a b)] fun t : ℝ ↦ ‖deriv γ t‖ :=
    Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  -- Unfold the supremum definition and bound every partition chord by the speed integral
  -- on the corresponding cell.
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  have hu0a : a ≤ u 0 := (hus 0).1
  have hunb : u n ≤ b := (hus n).2
  have hcell :
      ∀ k < n,
        edist (γ (u (k + 1))) (γ (u k)) ≤
          ENNReal.ofReal (∫ t in u k..u (k + 1), ‖deriv γ t‖) := by
    intro k hk
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal <| by
      simpa [dist_comm] using
        (dist_le_integral_norm_deriv_of_contDiffOn_Icc
          (hu (Nat.le_succ k)) hγ (hus k) (hus (k + 1)))
  have hsum_le :
      ∑ k ∈ Finset.range n, edist (γ (u (k + 1))) (γ (u k)) ≤
        ∑ k ∈ Finset.range n, ENNReal.ofReal (∫ t in u k..u (k + 1), ‖deriv γ t‖) := by
    exact Finset.sum_le_sum fun k hk ↦ hcell k (Finset.mem_range.mp hk)
  have hsum_int :
      ∑ k ∈ Finset.range n, ∫ t in u k..u (k + 1), ‖deriv γ t‖ =
        ∫ t in u 0..u n, ‖deriv γ t‖ := by
    refine intervalIntegral.sum_integral_adjacent_intervals ?_
    intro k hk
    exact intervalIntegrable_norm_deriv_of_contDiffOn_Icc (hu (Nat.le_succ k)) <|
      hγ.mono fun t ht ↦ ⟨(hus k).1.trans ht.1, ht.2.trans (hus (k + 1)).2⟩
  have hmono :
      ∫ t in u 0..u n, ‖deriv γ t‖ ≤ ∫ t in a..b, ‖deriv γ t‖ := by
    exact intervalIntegral.integral_mono_interval hu0a (hu (Nat.zero_le n)) hunb hnonnegAe hInt
  calc
    ∑ k ∈ Finset.range n, edist (γ (u (k + 1))) (γ (u k)) ≤
        ∑ k ∈ Finset.range n, ENNReal.ofReal (∫ t in u k..u (k + 1), ‖deriv γ t‖) := hsum_le
    _ = ENNReal.ofReal (∑ k ∈ Finset.range n, ∫ t in u k..u (k + 1), ‖deriv γ t‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro k hk
      exact intervalIntegral.integral_nonneg (hu (Nat.le_succ k)) fun t ht ↦ norm_nonneg _
    _ = ENNReal.ofReal (∫ t in u 0..u n, ‖deriv γ t‖) := by rw [hsum_int]
    _ ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := ENNReal.ofReal_le_ofReal hmono

/-- Helper for Exercise 2: a `C¹` curve on `Icc a b` has finite variation on every subinterval of
`Icc a b`. -/
lemma locallyBoundedVariationOn_Icc_of_contDiffOn
    {γ : ℝ → ℂ} {a b : ℝ} (_hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    LocallyBoundedVariationOn γ (Set.Icc a b) := by
  intro x y hx hy
  by_cases hxy : x ≤ y
  · have hinter :
        Set.Icc a b ∩ Set.Icc x y = Set.Icc x y := by
      apply Set.inter_eq_right.mpr
      intro t ht
      exact ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    have hsub :
        ContDiffOn ℝ 1 γ (Set.Icc x y) := by
      refine hγ.mono ?_
      intro t ht
      exact ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    obtain ⟨K, hK⟩ :=
      hsub.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
    -- On each compact subinterval, `C¹` regularity yields a Lipschitz bound, hence bounded
    -- variation.
    simpa [hinter] using
      (hK.locallyBoundedVariationOn (s := Set.Icc x y)) x y
        (by simp [hxy]) (by simp [hxy])
  · have hyx : y < x := lt_of_not_ge hxy
    -- If the ordered cell is empty, its variation is trivially finite.
    simp [BoundedVariationOn, Set.Icc_eq_empty_of_lt hyx]

/-- Helper for Exercise 2: on a `C¹` interval, the speed integral can be rewritten using the
interval derivative on that same interval. -/
lemma integral_norm_deriv_eq_integral_norm_derivWithin_Icc
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    ∫ t in a..b, ‖deriv γ t‖ = ∫ t in a..b, ‖derivWithin γ (Set.Icc a b) t‖ := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  -- Off the endpoints, the interval derivative and the ordinary derivative coincide.
  have hAe :
      (fun t : ℝ ↦ ‖deriv γ t‖) =ᵐ[volume.restrict (Set.uIoc a b)]
        fun t : ℝ ↦ ‖derivWithin γ (Set.Icc a b) t‖ := by
    simp only [hab, Set.uIoc_of_le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  refine intervalIntegral.integral_congr_ae ?_
  exact (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).1 hAe

/-- Helper for Exercise 2: an injective `C¹` interval curve carries at least its variation as
Euclidean Hausdorff `1`-measure. -/
lemma eVariationOn_Icc_le_euclideanHausdorffMeasure_image
    {γ : ℝ → ℂ} {a b : ℝ} (_hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ μHE[1] (γ '' Set.Icc a b) := by
  have hcont : ContinuousOn γ (Set.Icc a b) := hγ.continuousOn
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  have hu0a : a ≤ u 0 := (hus 0).1
  have hunb : u n ≤ b := (hus n).2
  have hcell :
      ∀ k < n,
        edist (γ (u (k + 1))) (γ (u k)) ≤ μHE[1] (γ '' Set.Icc (u k) (u (k + 1))) := by
    intro k hk
    have hcontCell : ContinuousOn γ (Set.Icc (u k) (u (k + 1))) := by
      -- Restrict continuity to the current partition cell.
      refine hcont.mono ?_
      intro t ht
      exact ⟨(hus k).1.trans ht.1, ht.2.trans (hus (k + 1)).2⟩
    have hpre :
        IsPreconnected (γ '' Set.Icc (u k) (u (k + 1))) :=
      isPreconnected_Icc.image γ hcontCell
    have hk_mem : γ (u k) ∈ γ '' Set.Icc (u k) (u (k + 1)) :=
      ⟨u k, ⟨le_rfl, hu (Nat.le_succ k)⟩, rfl⟩
    have hk1_mem : γ (u (k + 1)) ∈ γ '' Set.Icc (u k) (u (k + 1)) :=
      ⟨u (k + 1), ⟨hu (Nat.le_succ k), le_rfl⟩, rfl⟩
    -- The chord of the cell cannot exceed the Hausdorff length of the cell image.
    rw [euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one, edist_dist]
    exact hausdorffMeasure_ge_dist_of_isPreconnected hpre hk1_mem hk_mem
  have hsum_image :
      ∀ m,
        (∀ k < m,
            edist (γ (u (k + 1))) (γ (u k)) ≤ μHE[1] (γ '' Set.Icc (u k) (u (k + 1)))) →
          ∑ k ∈ Finset.range m, μHE[1] (γ '' Set.Icc (u k) (u (k + 1))) =
            μHE[1] (γ '' Set.Icc (u 0) (u m)) := by
    intro m
    induction m with
    | zero =>
        intro _
        haveI := MeasureTheory.Measure.noAtoms_hausdorff ℂ (show 0 < (1 : ℝ) by norm_num)
        have hzero : μHE[1] ({γ (u 0)} : Set ℂ) = 0 := by
          rw [euclideanHausdorffMeasure_one_eq_hausdorffMeasure_one]
          simp
        simpa [Set.Icc_self] using hzero.symm
    | succ m hm =>
        intro hcellBound
        have hm_le : u 0 ≤ u m := hu (Nat.zero_le m)
        have hcontPrefix : ContinuousOn γ (Set.Icc (u 0) (u (m + 1))) := by
          -- Restrict continuity to the prefix interval cut off by the partition.
          refine hcont.mono ?_
          intro t ht
          exact ⟨hu0a.trans ht.1, ht.2.trans (hus (m + 1)).2⟩
        have hinjPrefix : Set.InjOn γ (Set.Icc (u 0) (u (m + 1))) := by
          -- Injectivity on the big interval restricts to the current prefix.
          intro x hx y hy hxy
          exact hinj
            ⟨hu0a.trans hx.1, hx.2.trans (hus (m + 1)).2⟩
            ⟨hu0a.trans hy.1, hy.2.trans (hus (m + 1)).2⟩
            hxy
        calc
          ∑ k ∈ Finset.range (m + 1), μHE[1] (γ '' Set.Icc (u k) (u (k + 1))) =
              (∑ k ∈ Finset.range m, μHE[1] (γ '' Set.Icc (u k) (u (k + 1)))) +
                μHE[1] (γ '' Set.Icc (u m) (u (m + 1))) := by
                  rw [Finset.sum_range_succ]
          _ = μHE[1] (γ '' Set.Icc (u 0) (u m)) +
                μHE[1] (γ '' Set.Icc (u m) (u (m + 1))) := by
                  rw [hm fun k hk ↦ hcellBound k (lt_trans hk (Nat.lt_succ_self _))]
          _ = μHE[1] (γ '' Set.Icc (u 0) (u (m + 1))) := by
                symm
                exact image_Icc_union_measure_eq_of_injOn
                  hm_le (hu (Nat.le_succ m)) hcontPrefix hinjPrefix
  have hsum_le :
      ∑ k ∈ Finset.range n, edist (γ (u (k + 1))) (γ (u k)) ≤
        ∑ k ∈ Finset.range n, μHE[1] (γ '' Set.Icc (u k) (u (k + 1))) := by
    exact Finset.sum_le_sum fun k hk ↦ hcell k (Finset.mem_range.mp hk)
  have hsubset : γ '' Set.Icc (u 0) (u n) ⊆ γ '' Set.Icc a b := by
    -- The interval cut out by the partition stays inside `[a, b]`.
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, ⟨hu0a.trans ht.1, ht.2.trans hunb⟩, rfl⟩
  calc
    ∑ k ∈ Finset.range n, edist (γ (u (k + 1))) (γ (u k)) ≤
        ∑ k ∈ Finset.range n, μHE[1] (γ '' Set.Icc (u k) (u (k + 1))) := hsum_le
    _ = μHE[1] (γ '' Set.Icc (u 0) (u n)) := hsum_image n hcell
    _ ≤ μHE[1] (γ '' Set.Icc a b) := measure_mono hsubset

/-- Helper for Exercise 2: the speed integral of a `C¹` interval curve is bounded above by its
variation. -/
lemma integral_norm_deriv_Icc_le_eVariation
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) ≤ eVariationOn γ (Set.Icc a b) := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hcontDerivWithin :
      ContinuousOn (derivWithin γ (Set.Icc a b)) (Set.Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have huc :
      UniformContinuousOn (derivWithin γ (Set.Icc a b)) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcontDerivWithin
  have hbv : LocallyBoundedVariationOn γ (Set.Icc a b) :=
    locallyBoundedVariationOn_Icc_of_contDiffOn hab hγ
  have hvarFinite : eVariationOn γ (Set.Icc a b) ≠ ⊤ := by
    simpa [BoundedVariationOn, Set.inter_self] using
      hbv a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  refine (ENNReal.ofReal_le_iff_le_toReal hvarFinite).2 ?_
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  let osc : ℝ := ε / (2 * (b - a))
  have hba : 0 < b - a := sub_pos.mpr hlt
  have hosc : 0 < osc := by
    dsimp [osc]
    positivity
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp huc) osc hosc
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < δ / (b - a) by positivity)
  let M : ℕ := N + 1
  let u : ℕ → ℝ := fun k ↦ a + (b - a) * k / M
  have hMposNat : 0 < M := Nat.succ_pos _
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hMposNat
  have hMne : (M : ℝ) ≠ 0 := by positivity
  have hstep_lt : (b - a) / M < δ := by
    have hone : (1 : ℝ) / M < δ / (b - a) := by simpa [M] using hN
    have hmul := mul_lt_mul_of_pos_left hone hba
    have hcancel : (b - a) * (δ / (b - a)) = δ := by
      field_simp [hba.ne']
    have hmul' : (b - a) * ((1 : ℝ) / M) < δ := by
      calc
        (b - a) * ((1 : ℝ) / M) < (b - a) * (δ / (b - a)) := hmul
        _ = δ := hcancel
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul'
  have hu : Monotone u := by
    intro i j hij
    dsimp [u]
    gcongr
  have hu0 : u 0 = a := by simp [u]
  have huM : u M = b := by
    calc
      u M = a + (b - a) * M / M := by simp [u]
      _ = a + (b - a) := by field_simp [hMne]
      _ = b := by ring
  have hus :
      ∀ k ∈ Set.Icc (0 : ℕ) M, u k ∈ Set.Icc a b := by
    intro k hk
    constructor
    · simpa [hu0] using hu hk.1
    · simpa [huM] using hu hk.2
  have hstep_eq :
      ∀ k, u (k + 1) - u k = (b - a) / M := by
    intro k
    calc
      u (k + 1) - u k = (a + (b - a) * (k + 1) / M) - (a + (b - a) * k / M) := by
        simp [u]
      _ = (b - a) / M := by ring
  have hcell :
      ∀ k < M,
        ∫ t in u k..u (k + 1), ‖deriv γ t‖ ≤
          dist (γ (u k)) (γ (u (k + 1))) + 2 * osc * (u (k + 1) - u k) := by
    intro k hk
    have huk : u k ∈ Set.Icc a b := hus k ⟨Nat.zero_le _, Nat.le_of_lt hk⟩
    have huk1 : u (k + 1) ∈ Set.Icc a b := hus (k + 1) ⟨Nat.zero_le _, Nat.succ_le_of_lt hk⟩
    have hsub :
        ContDiffOn ℝ 1 γ (Set.Icc (u k) (u (k + 1))) := by
      refine hγ.mono ?_
      intro t ht
      exact ⟨huk.1.trans ht.1, ht.2.trans huk1.2⟩
    have hcellEq :
        ∫ t in u k..u (k + 1), ‖deriv γ t‖ =
          ∫ t in u k..u (k + 1), ‖derivWithin γ (Set.Icc (u k) (u (k + 1))) t‖ :=
      integral_norm_deriv_eq_integral_norm_derivWithin_Icc (hu (Nat.le_succ k)) hsub
    have hoscCell :
        ∀ t ∈ Set.Icc (u k) (u (k + 1)),
          ‖derivWithin γ (Set.Icc (u k) (u (k + 1))) t - derivWithin γ (Set.Icc a b) (u k)‖ ≤
            osc := by
      intro t ht
      have htGlobal : t ∈ Set.Icc a b := ⟨huk.1.trans ht.1, ht.2.trans huk1.2⟩
      have hltCell : u k < u (k + 1) := by
        rw [← sub_pos, hstep_eq]
        positivity
      have hstepAdd : u (k + 1) = u k + (b - a) / M := by
        nlinarith [hstep_eq k]
      have hdist_le : dist t (u k) ≤ (b - a) / M := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
        nlinarith [ht.2, hstepAdd]
      have hdist_lt : dist t (u k) < δ := lt_of_le_of_lt hdist_le hstep_lt
      have hclose :
          dist (derivWithin γ (Set.Icc a b) t) (derivWithin γ (Set.Icc a b) (u k)) < osc :=
        hδ t htGlobal (u k) huk hdist_lt
      have hderiv_eq :
          derivWithin γ (Set.Icc (u k) (u (k + 1))) t = derivWithin γ (Set.Icc a b) t := by
        exact derivWithin_subset
          (fun x hx ↦ ⟨huk.1.trans hx.1, hx.2.trans huk1.2⟩)
          ((uniqueDiffOn_Icc hltCell).uniqueDiffWithinAt ht)
          ((hγ t htGlobal).differentiableWithinAt one_ne_zero)
      simpa [dist_eq_norm, hderiv_eq] using le_of_lt hclose
    calc
      ∫ t in u k..u (k + 1), ‖deriv γ t‖ =
          ∫ t in u k..u (k + 1), ‖derivWithin γ (Set.Icc (u k) (u (k + 1))) t‖ := hcellEq
      _ ≤ dist (γ (u k)) (γ (u (k + 1))) + 2 * osc * (u (k + 1) - u k) := by
            exact single_cell_speed_le_chord_add_derivWithin_oscillation
              (hu (Nat.le_succ k)) hsub hoscCell
  have hsumInt :
      ∑ k ∈ Finset.range M, ∫ t in u k..u (k + 1), ‖deriv γ t‖ = ∫ t in a..b, ‖deriv γ t‖ := by
    calc
      ∑ k ∈ Finset.range M, ∫ t in u k..u (k + 1), ‖deriv γ t‖ =
          ∫ t in u 0..u M, ‖deriv γ t‖ := by
            refine intervalIntegral.sum_integral_adjacent_intervals ?_
            intro k hk
            exact intervalIntegrable_norm_deriv_of_contDiffOn_Icc (hu (Nat.le_succ k)) <|
              hγ.mono fun t ht ↦
                ⟨(hus k ⟨Nat.zero_le _, Nat.le_of_lt hk⟩).1.trans ht.1,
                  ht.2.trans
                    (hus (k + 1) ⟨Nat.zero_le _, Nat.succ_le_of_lt hk⟩).2⟩
      _ = ∫ t in a..b, ‖deriv γ t‖ := by simp [hu0, huM]
  have hsumBound :
      ∑ k ∈ Finset.range M, ∫ t in u k..u (k + 1), ‖deriv γ t‖ ≤
        (∑ k ∈ Finset.range M, dist (γ (u k)) (γ (u (k + 1)))) +
          ∑ k ∈ Finset.range M, (2 * osc * (u (k + 1) - u k)) := by
    simpa [Finset.sum_add_distrib] using
      Finset.sum_le_sum fun k hk ↦ hcell k (Finset.mem_range.mp hk)
  have hpartition :
      ENNReal.ofReal (∑ k ∈ Finset.range M, dist (γ (u k)) (γ (u (k + 1)))) ≤
        eVariationOn γ (Set.Icc a b) := by
    simpa [edist_dist, dist_comm, ENNReal.ofReal_sum_of_nonneg] using
      (eVariationOn.sum_le_of_monotoneOn_Iic (f := γ) (s := Set.Icc a b) (n := M)
        (u := u) (show MonotoneOn u (Set.Iic M) from hu.monotoneOn _)
        fun k hk ↦ hus k ⟨Nat.zero_le _, hk⟩)
  have hpartitionReal :
      ∑ k ∈ Finset.range M, dist (γ (u k)) (γ (u (k + 1))) ≤
        (eVariationOn γ (Set.Icc a b)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hvarFinite).1 hpartition
  have herror :
      ∑ k ∈ Finset.range M, (2 * osc * (u (k + 1) - u k)) = ε := by
    simp_rw [hstep_eq]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hMcancel : (M : ℝ) * ((b - a) / M) = b - a := by
      field_simp [hMne]
    calc
      (M : ℝ) * (2 * osc * ((b - a) / M)) = 2 * osc * ((M : ℝ) * ((b - a) / M)) := by ring
      _ = 2 * osc * (b - a) := by rw [hMcancel]
      _ = ε := by
            dsimp [osc]
            field_simp [hba.ne']
  calc
    ∫ t in a..b, ‖deriv γ t‖ = ∑ k ∈ Finset.range M, ∫ t in u k..u (k + 1), ‖deriv γ t‖ := by
      rw [hsumInt]
    _ ≤ (∑ k ∈ Finset.range M, dist (γ (u k)) (γ (u (k + 1)))) +
          ∑ k ∈ Finset.range M, (2 * osc * (u (k + 1) - u k)) := hsumBound
    _ = (∑ k ∈ Finset.range M, dist (γ (u k)) (γ (u (k + 1)))) + ε := by rw [herror]
    _ ≤ (eVariationOn γ (Set.Icc a b)).toReal + ε := by gcongr

/-- Helper for Exercise 2: the remaining geometric blocker is the reverse inequality from the speed
integral of an injective `C¹` interval image to its Euclidean Hausdorff `1`-measure. -/
lemma integral_norm_deriv_Icc_le_euclideanHausdorffMeasure_image
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) ≤ μHE[1] (γ '' Set.Icc a b) := by
  -- Route correction: instead of comparing the integral directly to Hausdorff measure cell by
  -- cell, first bound the integral by variation and then bound variation by the injective image
  -- measure.
  exact (integral_norm_deriv_Icc_le_eVariation hab hγ).trans
    (eVariationOn_Icc_le_euclideanHausdorffMeasure_image hab hγ hinj)

/-- Helper for Exercise 2: for an injective `C¹` curve on a closed interval, the Euclidean
Hausdorff `1`-measure of its image equals the speed integral. -/
lemma image_Icc_euclideanHausdorffMeasure_eq_integral_norm_deriv
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    μHE[1] (γ '' Set.Icc a b) = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  have hbv : LocallyBoundedVariationOn γ (Set.Icc a b) :=
    locallyBoundedVariationOn_Icc_of_contDiffOn hab hγ
  -- Combine the easy upper bound with the single remaining reverse inequality.
  refine le_antisymm ?_ (integral_norm_deriv_Icc_le_euclideanHausdorffMeasure_image hab hγ hinj)
  calc
    μHE[1] (γ '' Set.Icc a b) ≤ eVariationOn γ (Set.Icc a b) :=
      image_Icc_euclideanHausdorffMeasure_le_eVariation hab hbv
    _ ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) :=
      eVariationOn_Icc_le_integral_norm_deriv hab hγ

include hf

/-- Helper for Exercise 2: the remaining source-faithful blocker is the geometric identification
of the simple boundary image length with the boundary speed integral. -/
lemma boundary_circle_param_image_length_eq
    (hR : 0 ≤ R) (hR0 : R ≠ 0)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
      ENNReal.ofReal
        (R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) := by
  -- TODO: prove this by the source route: transfer injectivity to the angular parametrization,
  -- identify the Hausdorff length of the resulting simple closed `C¹` curve, then rewrite the
  -- speed using `boundary_circle_param_speed`.
  have hinjParam :
      Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Ioc (0 : ℝ) (2 * π)) :=
    boundary_circle_param_injOn (f := f) hR hR0 hinj
  have hcont :
      ContDiffOn ℝ 1 (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) (2 * π)) :=
    boundary_circle_param_contDiffOn (hf := hf) hR
  have hclosed :
      (fun θ : ℝ ↦ f (circleMap 0 R θ)) (0 : ℝ) =
        (fun θ : ℝ ↦ f (circleMap 0 R θ)) (2 * π) :=
    boundary_circle_param_endpoint_eq (hf := hf)
  have hspeedIntegral :
      ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
        R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ :=
    boundary_circle_param_integral_speed_eq (hf := hf) hR
  have hhalfInj :
      Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) π) ∧
        Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc π (2 * π)) :=
    boundary_circle_param_half_injOn (hf := hf) (f := f) hR hR0 hinj
  have hhalfOverlap :
      μHE[1]
          (((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∩
            ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π))) = 0 :=
    boundary_circle_half_image_overlap_measure_zero (hf := hf) (f := f) hR hR0 hinj
  have himageSplit :
      (fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π) =
        ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∪
          ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) :=
    boundary_circle_param_image_eq_half_union (hf := hf) (f := f) (R := R)
  have hmeasureSplit :
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
        μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) +
          μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) := by
    -- Rewrite the full image as a union, then use zero-overlap additivity.
    rw [himageSplit]
    exact boundary_circle_param_half_union_measure_eq (hf := hf) (f := f) (R := R) hR hhalfOverlap
  have hleftCont :
      ContDiffOn ℝ 1 (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) π) := by
    -- Restrict the `C¹` regularity to the left half-arc.
    refine hcont.mono ?_
    intro θ hθ
    exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hrightCont :
      ContDiffOn ℝ 1 (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc π (2 * π)) := by
    -- Restrict the `C¹` regularity to the right half-arc.
    refine hcont.mono ?_
    intro θ hθ
    exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hleftLength :
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) =
        ENNReal.ofReal
          (∫ θ in (0 : ℝ)..π, ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
    exact image_Icc_euclideanHausdorffMeasure_eq_integral_norm_deriv
      (show (0 : ℝ) ≤ π by linarith [Real.pi_pos]) hleftCont hhalfInj.1
  have hrightLength :
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) =
        ENNReal.ofReal
          (∫ θ in π..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
    exact image_Icc_euclideanHausdorffMeasure_eq_integral_norm_deriv
      (show π ≤ 2 * π by linarith [Real.pi_pos]) hrightCont hhalfInj.2
  have hderivInt_left :
      IntervalIntegrable
        (fun θ : ℝ ↦ ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) volume 0 π :=
    intervalIntegrable_norm_deriv_of_contDiffOn_Icc
      (show (0 : ℝ) ≤ π by linarith [Real.pi_pos]) hleftCont
  have hderivInt_right :
      IntervalIntegrable
        (fun θ : ℝ ↦ ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) volume π (2 * π) :=
    intervalIntegrable_norm_deriv_of_contDiffOn_Icc
      (show π ≤ 2 * π by linarith [Real.pi_pos]) hrightCont
  have hnonneg_left :
      0 ≤ ∫ θ in (0 : ℝ)..π, ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ := by
    exact intervalIntegral.integral_nonneg (show (0 : ℝ) ≤ π by linarith [Real.pi_pos])
      (fun θ hθ ↦ norm_nonneg _)
  have hnonneg_right :
      0 ≤ ∫ θ in π..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ := by
    exact intervalIntegral.integral_nonneg (show π ≤ 2 * π by linarith [Real.pi_pos])
      (fun θ hθ ↦ norm_nonneg _)
  have hgeom :
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
        ENNReal.ofReal
          (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
    -- Route correction: the boundary proof now reduces to the generic interval theorem on the
    -- two closed half-arcs and then recombines them by adjacent-interval additivity.
    calc
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
          μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) +
            μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) := hmeasureSplit
      _ =
          ENNReal.ofReal (∫ θ in (0 : ℝ)..π, ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) +
            ENNReal.ofReal (∫ θ in π..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
              rw [hleftLength, hrightLength]
      _ = ENNReal.ofReal
            ((∫ θ in (0 : ℝ)..π, ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) +
              ∫ θ in π..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
              rw [← ENNReal.ofReal_add hnonneg_left hnonneg_right]
      _ = ENNReal.ofReal
            (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := by
              congr 1
              exact intervalIntegral.integral_add_adjacent_intervals hderivInt_left hderivInt_right
  calc
    μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π)) =
        ENNReal.ofReal
          (∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖) := hgeom
    _ = ENNReal.ofReal
          (R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) := by
            rw [hspeedIntegral]

/-- Cartan section12 0014_Exercise_2: if `f` is holomorphic on a neighborhood of the closed disc
`|z| ≤ R` and
injective on the boundary circle `|z| = R`, then the Euclidean Hausdorff length of the boundary
image `f '' sphere 0 R` is `R ∫_0^{2π} ‖f'(R e^{iθ})‖ dθ`. -/
theorem boundary_image_length_eq
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    μHE[1] (f '' Metric.sphere (0 : ℂ) R) =
      ENNReal.ofReal
        (R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) := by
  -- Route correction: first rewrite the boundary as the angular image and transfer injectivity to
  -- that parametrization. The remaining work is now isolated to the simple-closed-curve
  -- Hausdorff-length bridge; the path-length-to-speed rewrite is handled separately above.
  by_cases hR0 : R = 0
  · haveI := MeasureTheory.Measure.noAtoms_hausdorff ℂ (show 0 < (1 : ℝ) by norm_num)
    simp [hR0, MeasureTheory.Measure.euclideanHausdorffMeasure_def]
  have himage :
      f '' Metric.sphere (0 : ℂ) R =
        (fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π) :=
    boundary_image_eq_circle_param_image (f := f) hR
  -- The unresolved part is now packaged as the single boundary-parametrization length theorem.
  rw [himage]
  exact boundary_circle_param_image_length_eq (hf := hf) hR hR0 hinj

/-- Exercise 2 (2): under the same hypotheses, the boundary-image length is bounded below by
`2 π R ‖f'(0)‖`. -/
theorem boundary_image_length_ge
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    ENNReal.ofReal (2 * π * R * ‖deriv f 0‖) ≤
      μHE[1] (f '' Metric.sphere (0 : ℂ) R) := by
  -- Rewrite the boundary length using the already-established arc-length formula.
  rw [boundary_image_length_eq (hf := hf) hR hinj]
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hR0 : R = 0
  · -- The degenerate circle has zero radius, so both sides vanish.
    simp [hR0]
  have hRpos : 0 < R := lt_of_le_of_ne hR (by simpa [eq_comm] using hR0)
  have hderivDiffCont : DiffContOnCl ℂ (deriv f) (Metric.ball 0 |R|) := by
    simpa [abs_of_nonneg hR] using
      (hf.deriv.differentiableOn).diffContOnCl_ball (c := (0 : ℂ)) (R := R) subset_rfl
  have hmean : Real.circleAverage (deriv f) 0 R = deriv f 0 :=
    hderivDiffCont.circleAverage
  have hnorm :
      ‖deriv f 0‖ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
    -- Take norms in the mean-value identity and bound the norm of the integral by the integral
    -- of the norm.
    calc
      ‖deriv f 0‖ =
          ‖(2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), deriv f (circleMap 0 R θ)‖ := by
            rw [← hmean, Real.circleAverage_def]
      _ = (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), deriv f (circleMap 0 R θ)‖ := by
            have hnonneg : 0 ≤ (2 * π)⁻¹ := by positivity
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
            exact mul_le_mul_of_nonneg_left
              (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le)
              (by positivity)
  have hmain :
      2 * π * R * ‖deriv f 0‖ ≤
        R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
    calc
      2 * π * R * ‖deriv f 0‖ ≤ (2 * π * R) * ((2 * π)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) := by
            exact mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
            field_simp [Real.two_pi_pos.ne', hRpos.ne']
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Exercise 2 (3): if `f` is holomorphic on a neighborhood of the closed disc `|z| ≤ R` and
injective on that closed disc, then the area of its image is the integral of `‖f'‖²` over the
disc. -/
theorem closed_disc_image_area_eq
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.closedBall (0 : ℂ) R)) :
    volume (f '' Metric.closedBall (0 : ℂ) R) =
      ENNReal.ofReal
        (∫ z in Metric.closedBall (0 : ℂ) R, ‖deriv f z‖ ^ 2 ∂volume) := by
  let _ := hR
  let s : Set ℂ := Metric.closedBall (0 : ℂ) R
  have hs : MeasurableSet s := measurableSet_closedBall
  have hderivWithin :
      ∀ z ∈ s, HasFDerivWithinAt f ((deriv f z) • (1 : ℂ →L[ℝ] ℂ)) s z := by
    intro z hz
    exact ((hf z hz).differentiableAt.hasDerivAt.complexToReal_fderiv).hasFDerivWithinAt
  have hlintegral :
      volume (f '' s) =
        ∫⁻ z in s, ENNReal.ofReal |(((deriv f z) • (1 : ℂ →L[ℝ] ℂ)).det)| ∂volume := by
    -- The change-of-variables formula computes the area of the injective image.
    simpa [s] using
      (MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hs
        hderivWithin hinj (fun _ : ℂ ↦ 1))
  have hdet :
      ∀ z : ℂ,
        ENNReal.ofReal |(((deriv f z) • (1 : ℂ →L[ℝ] ℂ)).det)| =
          ENNReal.ofReal (‖deriv f z‖ ^ 2) := by
    intro z
    rw [complex_abs_det_smul_id_eq_sq_norm]
  have hderivAnalytic : AnalyticOnNhd ℂ (deriv f) s := by
    simpa [s] using
      (AnalyticOnNhd.deriv (𝕜 := ℂ) (F := ℂ) (f := f) (s := s) hf)
  have hcontDeriv : ContinuousOn (deriv f) s := hderivAnalytic.continuousOn
  have hcont :
      ContinuousOn (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) s := by
    simpa using hcontDeriv.norm.pow 2
  have hscompact : IsCompact s := by
    simpa [s] using isCompact_closedBall (x := (0 : ℂ)) (r := R)
  have hint :
      IntegrableOn (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) s volume :=
    hcont.integrableOn_compact hscompact
  -- Convert the nonnegative `lintegral` back to the ordinary real integral.
  calc
    volume (f '' s) =
        ∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖ ^ 2) ∂volume := by
          rw [hlintegral]
          refine setLIntegral_congr_fun hs ?_
          intro z hz
          exact hdet z
    _ = ENNReal.ofReal (∫ z in s, ‖deriv f z‖ ^ 2 ∂volume) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint]
          exact Filter.Eventually.of_forall fun z ↦ sq_nonneg ‖deriv f z‖
    _ = ENNReal.ofReal (∫ z in Metric.closedBall (0 : ℂ) R, ‖deriv f z‖ ^ 2 ∂volume) := by
          rfl

/-- Exercise 2 (4): under the same hypotheses, the image area is bounded below by
`π R² ‖f'(0)‖²`. -/
theorem closed_disc_image_area_ge
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.closedBall (0 : ℂ) R)) :
    ENNReal.ofReal (π * R ^ 2 * ‖deriv f 0‖ ^ 2) ≤
      volume (f '' Metric.closedBall (0 : ℂ) R) := by
  have hderivAnalytic : AnalyticOnNhd ℂ (deriv f) (Metric.closedBall (0 : ℂ) R) := by
    simpa using
      (AnalyticOnNhd.deriv (𝕜 := ℂ) (F := ℂ) (f := f) (s := Metric.closedBall (0 : ℂ) R) hf)
  have hcontDeriv : ContinuousOn (deriv f) (Metric.closedBall (0 : ℂ) R) :=
    hderivAnalytic.continuousOn
  have hsqCont : ContinuousOn (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) (Metric.closedBall (0 : ℂ) R) := by
    simpa using hcontDeriv.norm.pow 2
  have hcircleAverageCont :
      ContinuousOn (Real.circleAverage (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) 0) (Set.Icc (0 : ℝ) R) := by
    -- The circle average varies continuously with the radius on the closed interval `[0, R]`.
    have hsqCont' :
        ContinuousOn (fun z : ℂ ↦ ‖deriv f z‖ ^ 2)
          {z : ℂ | ‖z - (0 : ℂ)‖ ∈ Set.Icc (0 : ℝ) R} := by
      simpa [Metric.closedBall, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hsqCont
    exact Real.ContinuousOn.circleAverage (s := Set.Icc (0 : ℝ) R) (c := (0 : ℂ))
      hsqCont' fun r hr ↦ hr.1
  let avg : ℝ → ℝ := fun r ↦ Real.circleAverage (fun z : ℂ ↦ ‖deriv f z‖ ^ 2) 0 r
  have havgInt :
      ContinuousOn (fun r : ℝ ↦ (2 * π) * (r * avg r)) (Set.Icc (0 : ℝ) R) := by
    -- Repackage the angular integral through the continuous circle average.
    intro r hr
    exact continuousAt_const.continuousWithinAt.mul ((continuousOn_id.mul hcircleAverageCont) r hr)
  have hleftInt :
      IntervalIntegrable (fun r : ℝ ↦ (2 * π) * (r * ‖deriv f 0‖ ^ 2)) volume 0 R :=
    (continuous_const.mul (continuous_id.mul continuous_const)).intervalIntegrable _ _
  have hrightInt :
      IntervalIntegrable
        (fun r : ℝ ↦ r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2) volume 0 R := by
    have hEq :
        Set.EqOn
          (fun r : ℝ ↦ r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2)
          (fun r : ℝ ↦ (2 * π) * (r * avg r))
          (Set.Icc (0 : ℝ) R) := by
      intro r hr
      -- Rewrite the angular integral through `circleAverage`.
      change r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 =
        (2 * π) *
          (r * ((2 * π)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2))
      field_simp [Real.pi_ne_zero]
    exact (havgInt.congr hEq).intervalIntegrable_of_Icc hR
  have hmono :
      ∫ r in (0 : ℝ)..R, (2 * π) * (r * ‖deriv f 0‖ ^ 2) ≤
        ∫ r in (0 : ℝ)..R, r * ∫ θ in (0 : ℝ)..(2 * π),
          ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
    -- Integrate the radiuswise Cauchy-Schwarz bound over `0 ≤ r ≤ R`.
    apply intervalIntegral.integral_mono_on_of_le_Ioo hR hleftInt hrightInt
    intro r hr
    have hsquare :
        ‖deriv f 0‖ ^ 2 ≤
          (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 :=
      sq_norm_deriv_zero_le_circle_average_sq_norm_deriv (hf := hf) hr.1.le hr.2.le
    have hr_nonneg : 0 ≤ r := hr.1.le
    have hfactor :
        (2 * π) * (r * ‖deriv f 0‖ ^ 2) ≤
          (2 * π) * (r * ((2 * π)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsquare hr_nonneg)
        (by positivity)
    calc
      (2 * π) * (r * ‖deriv f 0‖ ^ 2) ≤
          (2 * π) * (r * ((2 * π)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2)) := hfactor
      _ = r * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 r θ)‖ ^ 2 := by
            ring_nf
            field_simp [Real.two_pi_pos.ne']
  have hleft :
      ∫ r in (0 : ℝ)..R, (2 * π) * (r * ‖deriv f 0‖ ^ 2) =
        π * R ^ 2 * ‖deriv f 0‖ ^ 2 := by
    -- The radial weight integrates to `R² / 2`.
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_mul_const]
    rw [show ∫ r in (0 : ℝ)..R, r = ∫ r in (0 : ℝ)..R, r ^ 1 by
      congr with r
      simp]
    rw [integral_pow]
    ring
  rw [closed_disc_image_area_eq (hf := hf) hR hinj]
  apply ENNReal.ofReal_le_ofReal
  rw [closedBall_integral_sq_norm_deriv_eq_polar (f := f) (R := R) hR]
  rw [polar_sq_norm_deriv_setIntegral_eq_radius_angleIntegral (hf := hf) (f := f) (R := R) hR]
  exact hleft.symm.le.trans hmono

/-- Summary for Cartan section12 0014_Exercise_2: if `f` is holomorphic on a neighborhood of the
closed disc
`|z| ≤ R` and injective on that disc, then the boundary-image length and closed-disc image area are
given by the expected speed and Jacobian integrals, and they satisfy the sharp lower bounds coming
from `f'(0)`. -/
theorem simple_holomorphic_closedDisc_boundary_length_and_area
    (hR : 0 ≤ R)
    (hinj : Set.InjOn f (Metric.closedBall (0 : ℂ) R)) :
    μHE[1] (f '' Metric.sphere (0 : ℂ) R) =
        ENNReal.ofReal
          (R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖) ∧
      ENNReal.ofReal (2 * π * R * ‖deriv f 0‖) ≤
        μHE[1] (f '' Metric.sphere (0 : ℂ) R) ∧
      volume (f '' Metric.closedBall (0 : ℂ) R) =
        ENNReal.ofReal
          (∫ z in Metric.closedBall (0 : ℂ) R, ‖deriv f z‖ ^ 2 ∂volume) ∧
      ENNReal.ofReal (π * R ^ 2 * ‖deriv f 0‖ ^ 2) ≤
        volume (f '' Metric.closedBall (0 : ℂ) R) := by
  have hboundaryInj : Set.InjOn f (Metric.sphere (0 : ℂ) R) := by
    intro z hz w hw hEq
    exact hinj
      (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hz)))
      (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hw)))
      hEq
  -- Combine the four already-established formulas under the textbook's global injectivity
  -- hypothesis on the closed disc.
  refine ⟨boundary_image_length_eq (hf := hf) hR hboundaryInj, ?_⟩
  refine ⟨boundary_image_length_ge (hf := hf) hR hboundaryInj, ?_⟩
  refine ⟨closed_disc_image_area_eq (hf := hf) hR hinj, ?_⟩
  exact closed_disc_image_area_ge (hf := hf) hR hinj

end
