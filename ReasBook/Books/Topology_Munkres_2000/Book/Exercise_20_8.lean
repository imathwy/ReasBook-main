module

public import Topology_Munkres_2000.Book.Exercise_20_8.Witnesses
public import Topology_Munkres_2000.Book.Theorem_20_4
public import Mathlib.Analysis.PSeries

public section

open scoped lp

/-- The topology on square-summable real sequences induced by the ambient box topology. -/
@[implicit_reducible]
noncomputable def l2BoxTopology : TopologicalSpace (ℓ²(ℕ, ℝ)) :=
  TopologicalSpace.induced (fun x n ↦ x n)
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))

/-- The topology on square-summable real sequences induced by the ambient uniform topology. -/
@[implicit_reducible]
noncomputable def l2UniformTopology : TopologicalSpace (ℓ²(ℕ, ℝ)) :=
  TopologicalSpace.induced (fun x n ↦ x n) (UniformMetric.topology ℕ)

/-- The Hilbert cube of sequences whose `n`th coordinate lies in `[0, 1 / (n + 1)]`. -/
def hilbertCube : Set (ℕ → ℝ) :=
  {x | ∀ n : ℕ, x n ∈ Set.Icc 0 (1 / (n + 1 : ℝ))}

/-- Every sequence in the Hilbert cube is square-summable. -/
theorem hilbertCube_memL2 (x : ℕ → ℝ) (hx : x ∈ hilbertCube) :
    Memℓp x 2 := by
  -- Dominate the squared coordinates by the convergent reciprocal-square series.
  apply memℓp_gen
  have hs : Summable (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ) ^ 2) := by
    have hs' := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
    convert hs' using 1
    funext n
    rw [abs_of_pos (by positivity), Real.rpow_two]
  refine hs.of_nonneg_of_le (fun n ↦ by positivity) ?_
  intro n
  have hx_nonneg : 0 ≤ x n := (hx n).1
  have hx_le : x n ≤ 1 / (n + 1 : ℝ) := (hx n).2
  rw [show (2 : ENNReal).toReal = 2 by norm_num, Real.rpow_two]
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx_nonneg, one_div, inv_pow] using
    (sq_le_sq₀ hx_nonneg (by positivity)).2 hx_le

/-- The canonical inclusion of the Hilbert cube into `ℓ²(ℕ, ℝ)`. -/
def hilbertCubeToL2 (x : hilbertCube) : ℓ²(ℕ, ℝ) :=
  ⟨fun n ↦ x.1 n, hilbertCube_memL2 x.1 x.property⟩

/-- The topology on the Hilbert cube induced by the box topology. -/
@[reducible, expose]
def hilbertCubeBoxTopology : TopologicalSpace hilbertCube :=
  TopologicalSpace.induced Subtype.val (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))

/-- The topology on the Hilbert cube induced by its inclusion into `ℓ²`. -/
@[reducible, expose]
noncomputable def hilbertCubeL2Topology : TopologicalSpace hilbertCube :=
  TopologicalSpace.induced hilbertCubeToL2 inferInstance

/-- The topology on the Hilbert cube induced by the uniform topology. -/
@[reducible, expose]
noncomputable def hilbertCubeUniformTopology : TopologicalSpace hilbertCube :=
  TopologicalSpace.induced Subtype.val (UniformMetric.topology ℕ)

/-- Part (1) of Exercise 20.8: the box topology on square-summable sequences is finer than the
`ℓ²` topology. -/
theorem box_le_l2 :
    l2BoxTopology ≤ (inferInstance : TopologicalSpace (ℓ²(ℕ, ℝ))) := by
  -- Prove continuity of the identity by placing a geometric coordinate box in each ball.
  apply (@continuous_id_iff_le (ℓ²(ℕ, ℝ)) l2BoxTopology inferInstance).1
  rw [@continuous_def (ℓ²(ℕ, ℝ)) (ℓ²(ℕ, ℝ)) l2BoxTopology inferInstance]
  intro U hU
  rw [@isOpen_iff_mem_nhds (ℓ²(ℕ, ℝ)) l2BoxTopology]
  intro x hx
  obtain ⟨ε, hε, hballU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let V : ℕ → Set ℝ := fun n ↦ Metric.ball (x n) (ε / 2 ^ (n + 2))
  have hVopen : ∀ n, IsOpen (V n) := fun n ↦ Metric.isOpen_ball
  have hxV : (fun n ↦ x n) ∈ Set.pi Set.univ V := by
    intro n hn
    simp only [V, Metric.mem_ball, dist_self]
    positivity
  have hboxNhds : Set.pi Set.univ V ∈
      @nhds (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) (fun n ↦ x n) := by
    have hopen : @IsOpen (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
        (Set.pi Set.univ V) := Pi.isOpen_box V hVopen
    exact @IsOpen.mem_nhds (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
      _ _ hopen hxV
  refine Filter.mem_of_superset
    ((@mem_nhds_induced (ℕ → ℝ) (ℓ²(ℕ, ℝ))
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) (fun z n ↦ z n) x
      ((fun z : ℓ²(ℕ, ℝ) ↦ fun n ↦ z n) ⁻¹' Set.pi Set.univ V)).2
      ⟨Set.pi Set.univ V, hboxNhds, Set.Subset.rfl⟩) ?_
  intro y hy
  apply hballU
  rw [Metric.mem_ball, dist_eq_norm]
  have hboundSummable : Summable (fun i : ℕ ↦ ε ^ 2 / 16 * (1 / 4 : ℝ) ^ i) := by
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num) :
      Summable (fun i : ℕ ↦ (1 / 4 : ℝ) ^ i)).mul_left _
  have hnorm : ‖y - x‖ ≤ ε / 2 := by
    apply lp.norm_le_of_tsum_le (p := (2 : ENNReal)) (by norm_num) (by positivity)
    calc
      ∑' i : ℕ, ‖(y - x) i‖ ^ (2 : ℝ)
          ≤ ∑' i : ℕ, ε ^ 2 / 16 * (1 / 4 : ℝ) ^ i := by
            apply Summable.tsum_le_tsum
            · intro i
              have hcoord : ‖(y - x) i‖ < ε / 2 ^ (i + 2) := by
                simpa only [V, Metric.mem_ball, dist_eq_norm, ← Pi.sub_apply,
                  ← lp.coeFn_sub] using hy i (Set.mem_univ i)
              have hpow : ((2 : ℝ) ^ (i + 2)) ^ 2 = 16 * (4 : ℝ) ^ i := by
                rw [pow_add, pow_two]
                ring_nf
                rw [mul_comm i 2, pow_mul]
                norm_num
              calc
                ‖(y - x) i‖ ^ (2 : ℝ) = ‖(y - x) i‖ ^ 2 := by
                  rw [Real.rpow_two]
                _ ≤ (ε / 2 ^ (i + 2)) ^ 2 := by
                  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hcoord.le
                _ = ε ^ 2 / 16 * (1 / 4 : ℝ) ^ i := by
                  rw [div_pow, hpow]
                  rw [one_div, inv_pow]
                  field_simp
            · exact (lp.memℓp (y - x)).summable (by norm_num)
            · exact hboundSummable
      _ = ε ^ 2 / 12 := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
            ring
      _ ≤ (ε / 2) ^ (2 : ℝ) := by
            rw [Real.rpow_two]
            nlinarith [sq_nonneg ε]
  nlinarith

/-- Helper for Exercise 20.8: uniform distance between coordinate sequences is bounded by
the `ℓ²` distance. -/
lemma uniformDist_l2Coe_le (x y : ℓ²(ℕ, ℝ)) :
    (UniformMetric.metricSpace ℕ).dist (fun n ↦ x n) (fun n ↦ y n) ≤ dist x y := by
  -- Bound every truncated coordinate distance by the norm of the difference.
  rw [UniformMetric.dist_eq]
  refine ciSup_le fun n ↦ ?_
  refine (min_le_left _ _).trans ?_
  simpa only [dist_eq_norm, ← Pi.sub_apply, ← lp.coeFn_sub] using
    lp.norm_apply_le_norm (p := (2 : ENNReal)) (by norm_num) (x - y) n

/-- Helper for Exercise 20.8: the coordinate inclusion from `ℓ²` to the uniform sequence
space is continuous. -/
lemma continuous_l2Coe_uniform :
    @Continuous (ℓ²(ℕ, ℝ)) (ℕ → ℝ) inferInstance (UniformMetric.topology ℕ)
      (fun x n ↦ x n) := by
  -- The metric comparison gives the epsilon-delta estimate with the same radius.
  rw [@Metric.continuous_iff _ _ inferInstance
    (UniformMetric.metricSpace ℕ).toPseudoMetricSpace]
  intro x ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  exact lt_of_le_of_lt (uniformDist_l2Coe_le y x) hy

/-- Part (2) of Exercise 20.8: the `ℓ²` topology is finer than the uniform topology. -/
theorem l2_le_uniform :
    (inferInstance : TopologicalSpace (ℓ²(ℕ, ℝ))) ≤ l2UniformTopology := by
  -- Convert the induced-topology comparison to continuity of the coordinate inclusion.
  unfold l2UniformTopology
  exact continuous_iff_le_induced.1 continuous_l2Coe_uniform

/-- Helper for Exercise 20.8: the induced box topology on eventually-zero sequences is
finer than its induced `ℓ²` topology. -/
lemma eventuallyZero_box_le_l2 :
    eventuallyZeroRealBoxTopology ≤ eventuallyZeroRealL2Topology := by
  -- Pull the ambient box-to-`ℓ²` comparison back along the canonical inclusion.
  have h := induced_mono (g := eventuallyZeroToL2) box_le_l2
  simpa only [eventuallyZeroRealBoxTopology_def, eventuallyZeroRealL2Topology_def,
    l2BoxTopology, induced_compose, Function.comp_def, eventuallyZeroToL2_apply] using h

/-- Helper for Exercise 20.8: the induced `ℓ²` topology on eventually-zero sequences is
finer than its induced uniform topology. -/
lemma eventuallyZero_l2_le_uniform :
    eventuallyZeroRealL2Topology ≤ eventuallyZeroRealUniformTopology := by
  -- Pull the ambient `ℓ²`-to-uniform comparison back along the canonical inclusion.
  have h := induced_mono (g := eventuallyZeroToL2) l2_le_uniform
  simpa only [eventuallyZeroRealL2Topology_def, eventuallyZeroRealUniformTopology_def,
    l2UniformTopology, induced_compose, Function.comp_def, eventuallyZeroToL2_apply] using h

/-- Helper for Exercise 20.8: the induced uniform topology on eventually-zero sequences is
finer than its product-subspace topology. -/
lemma eventuallyZero_uniform_le_product :
    eventuallyZeroRealUniformTopology ≤
      (inferInstance : TopologicalSpace eventuallyZeroRealSequences) := by
  -- Pull back the ambient uniform-to-product comparison along the subtype inclusion.
  exact induced_mono (UniformMetric.topology_le_product ℕ)

/-- Helper for Exercise 20.8: the box topology on the Hilbert cube is finer than its
induced `ℓ²` topology. -/
lemma hilbertCube_box_le_l2 : hilbertCubeBoxTopology ≤ hilbertCubeL2Topology := by
  -- Pull the ambient comparison back along the Hilbert-cube inclusion into `ℓ²`.
  have h := induced_mono (g := hilbertCubeToL2) box_le_l2
  simpa only [hilbertCubeBoxTopology, hilbertCubeL2Topology, l2BoxTopology,
    induced_compose, Function.comp_def, hilbertCubeToL2] using h

/-- Helper for Exercise 20.8: the `ℓ²` topology on the Hilbert cube is finer than its
uniform topology. -/
lemma hilbertCube_l2_le_uniform :
    hilbertCubeL2Topology ≤ hilbertCubeUniformTopology := by
  -- Pull the ambient `ℓ²`-to-uniform comparison back along the cube inclusion.
  have h := induced_mono (g := hilbertCubeToL2) l2_le_uniform
  simpa only [hilbertCubeL2Topology, hilbertCubeUniformTopology, l2UniformTopology,
    induced_compose, Function.comp_def, hilbertCubeToL2] using h

/-- Helper for Exercise 20.8: the uniform topology on the Hilbert cube is finer than its
product-subspace topology. -/
lemma hilbertCube_uniform_le_product :
    hilbertCubeUniformTopology ≤ (inferInstance : TopologicalSpace hilbertCube) := by
  -- Pull back the ambient uniform-to-product comparison along the subtype inclusion.
  exact induced_mono (UniformMetric.topology_le_product ℕ)

/-- Helper for Exercise 20.8: reciprocal moving spikes converge to zero in the induced
`ℓ²` topology on eventually-zero sequences. -/
lemma reciprocalSpike_tendsto_l2 :
    @Filter.Tendsto ℕ eventuallyZeroRealSequences
      (coordinateSpikeEventuallyZero (fun n ↦ 1 / (n + 1 : ℝ))) Filter.atTop
      (@nhds eventuallyZeroRealSequences eventuallyZeroRealL2Topology eventuallyZeroZero) := by
  -- Reduce induced-topology convergence to convergence of the exact `ℓ²` norms.
  rw [eventuallyZeroRealL2Topology_def, tendsto_induced_iff]
  rw [eventuallyZeroToL2_zero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert (tendsto_one_div_add_atTop_nhds_zero_nat :
    Filter.Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0)) using 1
  funext n
  simp only [Function.comp_apply, eventuallyZeroToL2_coordinateSpike,
    coordinateSpikeL2_norm]
  rw [abs_of_pos]
  positivity

/-- Helper for Exercise 20.8: reciprocal moving spikes do not converge to zero in the
induced box topology on eventually-zero sequences. -/
lemma reciprocalSpike_not_tendsto_box :
    ¬ @Filter.Tendsto ℕ eventuallyZeroRealSequences
      (coordinateSpikeEventuallyZero (fun n ↦ 1 / (n + 1 : ℝ))) Filter.atTop
      (@nhds eventuallyZeroRealSequences eventuallyZeroRealBoxTopology eventuallyZeroZero) := by
  -- The box wrapper sees a nonzero value on every diagonal coordinate.
  rw [tendsto_eventuallyZeroBox_iff]
  apply not_tendsto_box_of_diagonal_ne_zero
  intro n
  simp only [Function.comp_apply, coordinateSpikeEventuallyZero_val,
    coordinateSpikeL2_apply_self]
  positivity

/-- Helper for Exercise 20.8: normalized initial segments converge uniformly to zero. -/
lemma normalizedInitialSegment_tendsto_uniform :
    @Filter.Tendsto ℕ eventuallyZeroRealSequences
      (initialSegmentEventuallyZero (fun n ↦ 1 / Real.sqrt (n + 1 : ℝ))) Filter.atTop
      (@nhds eventuallyZeroRealSequences eventuallyZeroRealUniformTopology eventuallyZeroZero) := by
  -- Bound every coordinate by the common height, which tends to zero.
  rw [tendsto_eventuallyZeroUniform_iff]
  have hb : Filter.Tendsto (fun n : ℕ ↦ 1 / Real.sqrt (n + 1 : ℝ)) Filter.atTop
      (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))
    have hsqrt' : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (1 / (n + 1 : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using hsqrt
    exact hsqrt'.congr' (Filter.Eventually.of_forall fun n ↦ by
      rw [one_div, Real.sqrt_inv]
      exact (one_div _).symm)
  have hraw := tendsto_uniform_of_pointwise_dist_le
    (fun n ↦ (initialSegmentEventuallyZero
      (fun k ↦ 1 / Real.sqrt (k + 1 : ℝ)) n).1)
    (fun n ↦ 1 / Real.sqrt (n + 1 : ℝ))
    (fun n ↦ by positivity)
    hb
    (fun n i ↦ by
      rw [initialSegmentEventuallyZero_apply]
      split_ifs
      · simp only [Real.dist_eq, sub_zero]
        rw [abs_of_nonneg (by positivity)]
      · simp only [dist_zero_left]
        simpa only [norm_zero] using
          (show 0 ≤ 1 / Real.sqrt (n + 1 : ℝ) by positivity))
  simpa only [Function.comp_def, eventuallyZeroZero_val] using hraw

/-- Helper for Exercise 20.8: normalized initial segments do not converge to zero in the
induced `ℓ²` topology. -/
lemma normalizedInitialSegment_not_tendsto_l2 :
    ¬ @Filter.Tendsto ℕ eventuallyZeroRealSequences
      (initialSegmentEventuallyZero (fun n ↦ 1 / Real.sqrt (n + 1 : ℝ))) Filter.atTop
      (@nhds eventuallyZeroRealSequences eventuallyZeroRealL2Topology eventuallyZeroZero) := by
  -- Their squared `ℓ²` norms are constantly one, so norm convergence is impossible.
  rw [eventuallyZeroRealL2Topology_def, tendsto_induced_iff]
  intro h
  rw [eventuallyZeroToL2_zero] at h
  have hnorm := tendsto_zero_iff_norm_tendsto_zero.mp h
  have hconst : (fun n : ℕ ↦ ‖eventuallyZeroToL2
      (initialSegmentEventuallyZero (fun k ↦ 1 / Real.sqrt (k + 1 : ℝ)) n)‖ ^ 2) =
      fun _ ↦ (1 : ℝ) := by
    funext n
    rw [eventuallyZeroToL2_initialSegment, initialSegmentL2_norm_sq]
    rw [abs_of_pos (by positivity), one_div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hsquare := hnorm.pow 2
  have hsquare' : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds 0) := by
    convert hsquare using 1
    · exact hconst.symm
    · norm_num
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hsquare')

/-- Helper for Exercise 20.8: unit moving spikes converge to zero in the product-subspace
topology on eventually-zero sequences. -/
lemma unitSpike_tendsto_product :
    Filter.Tendsto (coordinateSpikeEventuallyZero (fun _ ↦ 1)) Filter.atTop
      (nhds eventuallyZeroZero) := by
  -- Subtype convergence follows from coordinatewise convergence of the underlying spikes.
  rw [tendsto_subtype_rng]
  simpa only [Function.comp_apply, coordinateSpikeEventuallyZero_val, eventuallyZeroZero_val]
    using coordinateSpike_tendsto_product (fun _ ↦ 1)

/-- Helper for Exercise 20.8: unit moving spikes do not converge to zero in the induced
uniform topology on eventually-zero sequences. -/
lemma unitSpike_not_tendsto_uniform :
    ¬ @Filter.Tendsto ℕ eventuallyZeroRealSequences
      (coordinateSpikeEventuallyZero (fun _ ↦ 1)) Filter.atTop
      (@nhds eventuallyZeroRealSequences eventuallyZeroRealUniformTopology eventuallyZeroZero) := by
  -- Uniform convergence would force the constantly-one uniform distances to tend to zero.
  rw [tendsto_eventuallyZeroUniform_iff]
  intro h
  have hraw : @Filter.Tendsto ℕ (ℕ → ℝ)
      ((fun n ↦ (coordinateSpikeEventuallyZero (fun _ ↦ 1) n).1)) Filter.atTop
      (@nhds (ℕ → ℝ) (UniformMetric.topology ℕ) eventuallyZeroZero.1) := by
    have hforget := (@Continuous.tendsto UniformRealSequence (ℕ → ℝ) inferInstance
      (UniformMetric.topology ℕ)
      (WithTopology.ofTopology (t := UniformMetric.topology ℕ))
      (WithTopology.continuous_ofTopology (UniformMetric.topology ℕ))
      (UniformRealSequence.ofSequence eventuallyZeroZero.1)).comp h
    simpa only [Function.comp_def, UniformRealSequence.ofSequence_eq_toTopology] using hforget
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  have hdist := tendsto_iff_dist_tendsto_zero.mp hraw
  have hconst : (fun n : ℕ ↦ dist
      (coordinateSpikeEventuallyZero (fun _ ↦ 1) n).1 eventuallyZeroZero.1) =
      fun _ ↦ (1 : ℝ) := by
    funext n
    rw [eventuallyZeroZero_val]
    exact coordinateSpike_uniformDist_zero (fun _ ↦ 1) n |>.trans (by norm_num)
  rw [hconst] at hdist
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hdist)

/-- Helper for Exercise 20.8: the zero sequence belongs to the Hilbert cube. -/
lemma zero_mem_hilbertCube : (0 : ℕ → ℝ) ∈ hilbertCube := by
  -- Every coordinate is the left endpoint of its defining interval.
  intro n
  exact ⟨le_rfl, by positivity⟩

/-- Helper for Exercise 20.8: the zero point of the Hilbert cube. -/
def hilbertCubeZero : hilbertCube :=
  ⟨0, zero_mem_hilbertCube⟩

/-- Helper for Exercise 20.8: a reciprocal coordinate spike belongs to the Hilbert cube. -/
lemma reciprocalCoordinateSpike_mem (n : ℕ) :
    (fun i ↦ if i = n then 1 / (n + 1 : ℝ) else 0) ∈ hilbertCube := by
  -- At the selected coordinate the upper bound is attained; elsewhere the value is zero.
  intro i
  by_cases hi : i = n
  · subst i
    simp only [ite_true]
    exact ⟨by positivity, le_rfl⟩
  · simp only [if_neg hi]
    exact ⟨le_rfl, by positivity⟩

/-- Helper for Exercise 20.8: the reciprocal moving coordinate spike in the Hilbert cube. -/
noncomputable def hilbertCubeCoordinateSpike (n : ℕ) : hilbertCube :=
  ⟨fun i ↦ if i = n then 1 / (n + 1 : ℝ) else 0,
    reciprocalCoordinateSpike_mem n⟩

/-- Helper for Exercise 20.8: the `ℓ²` image of a reciprocal cube spike is the canonical
single-coordinate vector. -/
lemma hilbertCubeToL2_coordinateSpike (n : ℕ) :
    hilbertCubeToL2 (hilbertCubeCoordinateSpike n) =
      coordinateSpikeL2 (fun k ↦ 1 / (k + 1 : ℝ)) n := by
  -- Coordinate extensionality matches the raw cube function with `lp.single`.
  apply lp.ext
  funext i
  by_cases hi : i = n
  · subst i
    simp only [hilbertCubeToL2, hilbertCubeCoordinateSpike, ite_true,
      coordinateSpikeL2_apply_self]
  · simp only [hilbertCubeToL2, hilbertCubeCoordinateSpike, if_neg hi,
      coordinateSpikeL2_apply_ne _ hi]

/-- Helper for Exercise 20.8: the reciprocal cube spikes converge to zero in the induced
`ℓ²` topology. -/
lemma hilbertCubeCoordinateSpike_tendsto_l2 :
    @Filter.Tendsto ℕ hilbertCube hilbertCubeCoordinateSpike Filter.atTop
      (@nhds hilbertCube hilbertCubeL2Topology hilbertCubeZero) := by
  -- Reduce to the exact norm of a single-coordinate vector.
  rw [hilbertCubeL2Topology, tendsto_induced_iff]
  have hzero : hilbertCubeToL2 hilbertCubeZero = 0 := by
    apply lp.ext
    rfl
  rw [hzero, tendsto_zero_iff_norm_tendsto_zero]
  convert (tendsto_one_div_add_atTop_nhds_zero_nat :
    Filter.Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0)) using 1
  funext n
  rw [Function.comp_apply, hilbertCubeToL2_coordinateSpike, coordinateSpikeL2_norm]
  rw [abs_of_pos]
  positivity

/-- Helper for Exercise 20.8: the reciprocal cube spikes do not converge to zero in the
induced box topology. -/
lemma hilbertCubeCoordinateSpike_not_tendsto_box :
    ¬ @Filter.Tendsto ℕ hilbertCube hilbertCubeCoordinateSpike Filter.atTop
      (@nhds hilbertCube hilbertCubeBoxTopology hilbertCubeZero) := by
  -- Forgetting the subtype would produce box convergence with nonzero diagonal entries.
  rw [hilbertCubeBoxTopology]
  rw [@nhds_induced (ℕ → ℝ) hilbertCube
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) Subtype.val hilbertCubeZero]
  rw [Filter.tendsto_comap_iff]
  intro h
  have hwrap := (@Continuous.tendsto (ℕ → ℝ) BoxRealSequence
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) inferInstance
    (WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)))
    (WithTopology.continuous_toTopology
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))) 0).comp h
  have hwrapped : Filter.Tendsto
      (BoxRealSequence.ofSequence ∘ fun n ↦ (hilbertCubeCoordinateSpike n).1)
      Filter.atTop (nhds (BoxRealSequence.ofSequence 0)) := by
    simpa only [Function.comp_def, BoxRealSequence.ofSequence_eq_toTopology,
      hilbertCubeZero] using hwrap
  apply not_tendsto_box_of_diagonal_ne_zero
    (fun n ↦ (hilbertCubeCoordinateSpike n).1)
  · intro n
    simp only [hilbertCubeCoordinateSpike, ite_true]
    positivity
  · exact hwrapped

/-- Helper for Exercise 20.8: the coordinate inclusion from the Hilbert cube with its
product topology to uniform sequence space is continuous. -/
lemma continuous_hilbertCubeProduct_to_uniform :
    @Continuous hilbertCube (ℕ → ℝ) inferInstance (UniformMetric.topology ℕ) Subtype.val := by
  -- A finite coordinate cylinder controls the head, while cube bounds control the tail.
  rw [@continuous_iff_continuousAt hilbertCube (ℕ → ℝ) inferInstance
    (UniformMetric.topology ℕ) Subtype.val]
  intro x
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  apply Metric.continuousAt_iff'.2
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
  let V : ℕ → Set ℝ := fun i ↦ Metric.ball (x.1 i) (ε / 2)
  have hV : Set.pi (Finset.range N : Set ℕ) V ∈ nhds x.1 := by
    apply set_pi_mem_nhds (Finset.finite_toSet (Finset.range N))
    intro i hi
    exact Metric.ball_mem_nhds _ (half_pos hε)
  have hpre : Subtype.val ⁻¹' Set.pi (Finset.range N : Set ℕ) V ∈ nhds x :=
    continuous_subtype_val.continuousAt hV
  filter_upwards [hpre] with y hy
  rw [UniformMetric.dist_eq]
  refine lt_of_le_of_lt (ciSup_le fun i ↦ ?_) (half_lt_self hε)
  refine (min_le_left _ _).trans ?_
  by_cases hi : i < N
  · exact le_of_lt (hy i (by simpa only [Finset.mem_coe, Finset.mem_range] using hi))
  · have hcoord : dist (y.1 i) (x.1 i) ≤ 1 / (i + 1 : ℝ) := by
      rw [Real.dist_eq]
      apply (abs_le).2
      have hx0 := (x.property i).1
      have hx1 := (x.property i).2
      have hy0 := (y.property i).1
      have hy1 := (y.property i).2
      constructor <;> linarith
    exact hcoord.trans <| (Nat.one_div_le_one_div (Nat.le_of_not_gt hi)).trans (le_of_lt hN)

/-- Helper for Exercise 20.8: shifted tails of the reciprocal-square series become arbitrarily
small. -/
lemma reciprocalSquare_shiftedTail_lt (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∑' k : ℕ, (1 / (k + N + 1 : ℝ)) ^ 2 < η := by
  -- Use convergence of natural tails, then normalize the reciprocal-square summand.
  have htendsto := _root_.tendsto_sum_nat_add
    (fun n : ℕ ↦ (1 / (n + 1 : ℝ)) ^ 2)
  have heventually : ∀ᶠ N : ℕ in Filter.atTop,
      ∑' k : ℕ, (1 / (k + N + 1 : ℝ)) ^ 2 < η := by
    have hsmall := (tendsto_order.1 htendsto).2 η hη
    filter_upwards [hsmall] with N hN
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hN
  exact Filter.Eventually.exists heventually

/-- Helper for Exercise 20.8: the squared `ℓ²` distance on the Hilbert cube is bounded by a
uniformly controlled finite head plus a reciprocal-square tail. -/
lemma hilbertCube_l2Distance_sq_le (x y : hilbertCube) (N : ℕ) (δ : ℝ)
    (hhead : ∀ i < N, dist (y.1 i) (x.1 i) ≤ δ) :
    dist (hilbertCubeToL2 y) (hilbertCubeToL2 x) ^ 2 ≤
      N * δ ^ 2 + ∑' k : ℕ, (1 / (k + N + 1 : ℝ)) ^ 2 := by
  -- Split the squared coordinate series at `N`.
  have hsummable : Summable (fun i : ℕ ↦
      ‖(hilbertCubeToL2 y - hilbertCubeToL2 x) i‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (hilbertCubeToL2 y - hilbertCubeToL2 x)).summable (by norm_num)
  have hnorm : ‖hilbertCubeToL2 y - hilbertCubeToL2 x‖ ^ 2 =
      ∑' i : ℕ, ‖(hilbertCubeToL2 y - hilbertCubeToL2 x) i‖ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num)
        (hilbertCubeToL2 y - hilbertCubeToL2 x)
  rw [dist_eq_norm, hnorm]
  rw [← hsummable.sum_add_tsum_nat_add N]
  apply add_le_add
  · -- Every head coordinate is bounded by the supplied uniform radius.
    calc
      ∑ i ∈ Finset.range N, ‖(hilbertCubeToL2 y - hilbertCubeToL2 x) i‖ ^ 2
          ≤ ∑ _i ∈ Finset.range N, δ ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            apply pow_le_pow_left₀ (dist_nonneg) (hhead i (Finset.mem_range.1 hi)) 2
      _ = N * δ ^ 2 := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · -- Cube membership bounds each tail difference by the corresponding reciprocal.
    apply Summable.tsum_le_tsum
    · intro k
      have hcoord : dist (y.1 (k + N)) (x.1 (k + N)) ≤
          1 / (k + N + 1 : ℝ) := by
        rw [Real.dist_eq]
        apply (abs_le).2
        have hx1 := (x.property (k + N)).2
        have hy1 := (y.property (k + N)).2
        have hcast : ((k + N : ℕ) : ℝ) = k + N := by norm_num
        rw [hcast] at hx1 hy1
        have hx0 := (x.property (k + N)).1
        have hy0 := (y.property (k + N)).1
        constructor <;> linarith
      simpa only [hilbertCubeToL2, lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs,
        Real.dist_eq] using
        pow_le_pow_left₀ (dist_nonneg) hcoord 2
    · simpa only [Function.comp_def, hilbertCubeToL2, Nat.add_comm] using
        hsummable.comp_injective
        (add_left_injective N)
    · have hs : Summable (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℝ) ^ 2) := by
        have hs' := (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
        convert hs' using 1
        funext n
        rw [abs_of_pos (by positivity), Real.rpow_two]
      simpa only [Function.comp_def, one_div, inv_pow, Nat.add_comm, Nat.cast_add,
        add_assoc, add_comm, add_left_comm] using
        hs.comp_injective (add_left_injective N)

/-- Exercise 20.8: the coordinate inclusion from the uniformly topologized Hilbert cube into
`ℓ²` is continuous. -/
lemma continuous_hilbertCubeUniform_to_l2 :
    @Continuous hilbertCube (ℓ²(ℕ, ℝ)) hilbertCubeUniformTopology inferInstance
      hilbertCubeToL2 := by
  -- Work pointwise; a small uniform ball controls the finite head of the squared norm.
  rw [@continuous_iff_continuousAt hilbertCube (ℓ²(ℕ, ℝ))
    hilbertCubeUniformTopology inferInstance hilbertCubeToL2]
  intro x
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  apply (@Metric.continuousAt_iff' (ℓ²(ℕ, ℝ)) hilbertCube inferInstance
    hilbertCubeUniformTopology hilbertCubeToL2 x).2
  intro ε hε
  obtain ⟨N, htail⟩ := reciprocalSquare_shiftedTail_lt (ε ^ 2 / 2) (by positivity)
  let δ : ℝ := min (1 / 2) (ε / (2 * (N + 1)))
  have hδ : 0 < δ := by
    apply lt_min
    · norm_num
    · positivity
  have hδ_one : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hhead_budget : N * δ ^ 2 < ε ^ 2 / 2 := by
    have hδ_le : δ ≤ ε / (2 * (N + 1)) := min_le_right _ _
    have hδ_sq := pow_le_pow_left₀ hδ.le hδ_le 2
    have hN : (N : ℝ) < ((N : ℝ) + 1) ^ 2 := by
      nlinarith [show 0 ≤ (N : ℝ) by positivity]
    calc
      N * δ ^ 2 ≤ N * (ε / (2 * (N + 1))) ^ 2 := by
        gcongr
      _ < ((N : ℝ) + 1) ^ 2 * (ε / (2 * ((N : ℝ) + 1))) ^ 2 := by
        gcongr
      _ = ε ^ 2 / 4 := by
        field_simp
        norm_num
      _ < ε ^ 2 / 2 := by nlinarith [sq_pos_of_pos hε]
  have hball : Metric.ball x.1 δ ∈
      @nhds (ℕ → ℝ) (UniformMetric.topology ℕ) x.1 := Metric.ball_mem_nhds _ hδ
  have hpre : Subtype.val ⁻¹' Metric.ball x.1 δ ∈
      @nhds hilbertCube hilbertCubeUniformTopology x := by
    rw [hilbertCubeUniformTopology]
    exact (@mem_nhds_induced (ℕ → ℝ) hilbertCube (UniformMetric.topology ℕ)
      Subtype.val x (Subtype.val ⁻¹' Metric.ball x.1 δ)).2
      ⟨Metric.ball x.1 δ, hball, Set.Subset.rfl⟩
  filter_upwards [hpre] with y hy
  have hhead : ∀ i < N, dist (y.1 i) (x.1 i) ≤ δ := by
    intro i _hi
    rw [Set.mem_preimage, Metric.mem_ball, UniformMetric.dist_eq] at hy
    have hcoord : min (dist (y.1 i) (x.1 i)) 1 ≤
        ⨆ j, min (dist (y.1 j) (x.1 j)) 1 := by
      refine le_ciSup (α := ℝ) (f := fun j : ℕ ↦ min (dist (y.1 j) (x.1 j)) 1) ?_ i
      exact ⟨1, Set.forall_mem_range.mpr fun j ↦ min_le_right _ _⟩
    have hmin : min (dist (y.1 i) (x.1 i)) 1 < δ := hcoord.trans_lt hy
    have hdist_lt_one : dist (y.1 i) (x.1 i) < 1 := by
      by_contra h
      have hone : min (dist (y.1 i) (x.1 i)) 1 = 1 := min_eq_right (le_of_not_gt h)
      rw [hone] at hmin
      exact (hmin.trans hδ_one).false
    simpa only [min_eq_left hdist_lt_one.le] using hmin.le
  have hsq := hilbertCube_l2Distance_sq_le x y N δ hhead
  have hsq_lt : dist (hilbertCubeToL2 y) (hilbertCubeToL2 x) ^ 2 < ε ^ 2 := by
    calc
      dist (hilbertCubeToL2 y) (hilbertCubeToL2 x) ^ 2
          ≤ N * δ ^ 2 + ∑' k : ℕ, (1 / (k + N + 1 : ℝ)) ^ 2 := hsq
      _ < ε ^ 2 / 2 + ε ^ 2 / 2 := add_lt_add hhead_budget htail
      _ = ε ^ 2 := by ring
  exact (sq_lt_sq₀ dist_nonneg hε.le).1 hsq_lt

/-- Part (3) of Exercise 20.8: on eventually-zero sequences, the box topology is strictly finer
than the `ℓ²` topology. -/
theorem eventuallyZero_box_lt_l2 :
    eventuallyZeroRealBoxTopology < eventuallyZeroRealL2Topology := by
  -- The non-strict comparison is inherited from the ambient sequence spaces.
  refine lt_of_le_of_ne eventuallyZero_box_le_l2 ?_
  -- Equality would transport reciprocal-spike convergence to the box topology.
  intro h
  apply reciprocalSpike_not_tendsto_box
  rw [h]
  exact reciprocalSpike_tendsto_l2

/-- Part (4) of Exercise 20.8: on eventually-zero sequences, the `ℓ²` topology is strictly finer
than the uniform topology. -/
theorem eventuallyZero_l2_lt_uniform :
    eventuallyZeroRealL2Topology < eventuallyZeroRealUniformTopology := by
  -- The non-strict comparison follows from the canonical metric bound.
  refine lt_of_le_of_ne eventuallyZero_l2_le_uniform ?_
  -- Equality would transport uniform convergence of normalized initial segments to `ℓ²`.
  intro h
  apply normalizedInitialSegment_not_tendsto_l2
  rw [h]
  exact normalizedInitialSegment_tendsto_uniform

/-- Part (5) of Exercise 20.8: on eventually-zero sequences, the uniform topology is strictly finer
than the product topology. -/
theorem eventuallyZero_uniform_lt_product :
    eventuallyZeroRealUniformTopology <
      (inferInstance : TopologicalSpace eventuallyZeroRealSequences) := by
  -- The uniform topology is already known to be finer than the product topology.
  refine lt_of_le_of_ne eventuallyZero_uniform_le_product ?_
  -- Equality would transport product convergence of unit spikes to the uniform topology.
  intro h
  apply unitSpike_not_tendsto_uniform
  rw [h]
  exact unitSpike_tendsto_product

/-- Part (6) of Exercise 20.8: on the Hilbert cube, the box topology is strictly finer than the
`ℓ²` topology. -/
theorem hilbertCube_box_lt_l2 :
    hilbertCubeBoxTopology < hilbertCubeL2Topology := by
  -- The ambient box-to-`ℓ²` comparison restricts to the cube.
  refine lt_of_le_of_ne hilbertCube_box_le_l2 ?_
  -- Equality would transport reciprocal-spike convergence to the box topology.
  intro h
  apply hilbertCubeCoordinateSpike_not_tendsto_box
  rw [h]
  exact hilbertCubeCoordinateSpike_tendsto_l2

/-- Part (7) of Exercise 20.8: on the Hilbert cube, the `ℓ²` and uniform topologies coincide. -/
theorem hilbertCube_l2_eq_uniform :
    hilbertCubeL2Topology = hilbertCubeUniformTopology := by
  -- One inclusion is inherited from the ambient metric comparison.
  apply le_antisymm hilbertCube_l2_le_uniform
  -- The reverse inclusion is exactly continuity of the canonical inclusion into `ℓ²`.
  exact continuous_iff_le_induced.1 continuous_hilbertCubeUniform_to_l2

/-- Part (8) of Exercise 20.8: on the Hilbert cube, the uniform and product topologies coincide. -/
theorem hilbertCube_uniform_eq_product :
    hilbertCubeUniformTopology = (inferInstance : TopologicalSpace hilbertCube) := by
  -- One inclusion is inherited from the ambient uniform-to-product comparison.
  apply le_antisymm hilbertCube_uniform_le_product
  -- The reverse inclusion is continuity of the coordinate inclusion into uniform space.
  exact continuous_iff_le_induced.1 continuous_hilbertCubeProduct_to_uniform
