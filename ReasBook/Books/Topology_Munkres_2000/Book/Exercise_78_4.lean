module

public import Topology_Munkres_2000.Book.Definition_78_4.Holes
public import Topology_Munkres_2000.Book.Definition_78_3.Boundary
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Connected.CardComponents
public import Mathlib.Topology.Connected.Clopen

open scoped Manifold

public section

universe u

namespace Surface

open TopologicalSpace

/-- Helper for Exercise 78.4: the geometric boundary circles cut out by the chosen hole charts. -/
private def holeCircles {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) : Set X :=
  ⋃ i, charts i '' Metric.sphere 0 (1 / 2 : ℝ)

/-- Helper for Exercise 78.4: every radius-`1 / 2` circle lies in the source of its hole chart. -/
private lemma sphere_subset_holeChart_source {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) (i : Fin k) :
    Metric.sphere 0 (1 / 2 : ℝ) ⊆ (charts i).source := by
  -- The half-radius sphere lies strictly inside the unit coordinate ball.
  rw [charts.source_eq]
  exact Metric.sphere_subset_ball (by norm_num)

/-- Helper for Exercise 78.4: distinct geometric boundary circles are disjoint. -/
private lemma holeCircle_pairwiseDisjoint {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) :
    Set.univ.PairwiseDisjoint
      (fun i ↦ charts i '' Metric.sphere 0 (1 / 2 : ℝ)) := by
  -- Each circle sits in its chart target, whose targets are pairwise disjoint.
  intro i _hi j _hj hij
  exact (charts.pairwiseDisjoint_target (Set.mem_univ i) (Set.mem_univ j) hij).mono
    (Set.image_mono (sphere_subset_holeChart_source charts i) |>.trans
      (le_of_eq (charts i).image_source_eq_target))
    (Set.image_mono (sphere_subset_holeChart_source charts j) |>.trans
      (le_of_eq (charts j).image_source_eq_target))

/-- Helper for Exercise 78.4: each geometric boundary circle is connected. -/
private lemma holeCircle_isConnected {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) (i : Fin k) :
    IsConnected (charts i '' Metric.sphere 0 (1 / 2 : ℝ)) := by
  -- A Euclidean circle is connected, and the chart is continuous on its source.
  apply (isConnected_sphere (E := EuclideanSpace ℝ (Fin 2)) (by
    rw [← Module.finrank_eq_rank]
    norm_num) 0 (by norm_num)).image
  exact (charts i).continuousOn.mono (sphere_subset_holeChart_source charts i)

/-- Helper for Exercise 78.4: each geometric boundary circle is closed in the ambient surface. -/
private lemma holeCircle_isClosed {X : Type u} [TopologicalSpace X] [T2Space X] {k : ℕ}
    (charts : HoleCharts X k) (i : Fin k) :
    IsClosed (charts i '' Metric.sphere 0 (1 / 2 : ℝ)) := by
  -- The chart sends the compact coordinate circle continuously into the Hausdorff surface.
  exact ((isCompact_sphere 0 (1 / 2 : ℝ)).image_of_continuousOn
    ((charts i).continuousOn.mono (sphere_subset_holeChart_source charts i))).isClosed

/-- Helper for Exercise 78.4: the `i`th circle as a subset of the union of all hole circles. -/
private def holeCirclePiece {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) (i : Fin k) : Set (holeCircles charts) :=
  Subtype.val ⁻¹' (charts i '' Metric.sphere 0 (1 / 2 : ℝ))

/-- Helper for Exercise 78.4: each circle is clopen in the finite union of hole circles. -/
private lemma holeCirclePiece_isClopen {X : Type u} [TopologicalSpace X] [T2Space X] {k : ℕ}
    (charts : HoleCharts X k) (i : Fin k) :
    IsClopen (holeCirclePiece charts i) := by
  -- Closedness follows by pulling back the closed ambient circle.
  constructor
  · exact (holeCircle_isClosed charts i).preimage continuous_subtype_val
  · rw [← isClosed_compl_iff]
    have hcomplement :
        (holeCirclePiece charts i)ᶜ =
          Subtype.val ⁻¹' (⋃ j : {j : Fin k // j ≠ i},
            charts j.1 '' Metric.sphere 0 (1 / 2 : ℝ)) := by
      ext x
      simp only [Set.mem_compl_iff, holeCirclePiece, Set.mem_preimage,
        Set.mem_iUnion]
      constructor
      · intro hxi
        have hxunion :
            x.1 ∈ ⋃ j : Fin k, charts j '' Metric.sphere 0 (1 / 2 : ℝ) := by
          simpa only [holeCircles] using x.2
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxunion
        have hji : j ≠ i := by
          intro hji
          subst j
          exact hxi hxj
        exact ⟨⟨j, hji⟩, hxj⟩
      · rintro ⟨j, hxj⟩ hxi
        have hdisjoint := holeCircle_pairwiseDisjoint charts
          (Set.mem_univ i) (Set.mem_univ j.1) (Ne.symm j.2)
        exact Set.disjoint_left.mp hdisjoint hxi hxj
    rw [hcomplement]
    exact (isClosed_iUnion_of_finite fun (j : {j : Fin k // j ≠ i}) ↦
      holeCircle_isClosed charts j.1).preimage
      continuous_subtype_val

/-- Helper for Exercise 78.4: each relative circle piece is connected. -/
private lemma holeCirclePiece_isConnected {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) (i : Fin k) :
    IsConnected (holeCirclePiece charts i) := by
  -- The subtype inclusion identifies the relative piece with its ambient circle.
  constructor
  · obtain ⟨x, hx⟩ := (holeCircle_isConnected charts i).nonempty
    refine ⟨⟨x, ?_⟩, hx⟩
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have himage :
        Subtype.val '' holeCirclePiece charts i =
          charts i '' Metric.sphere 0 (1 / 2 : ℝ) := by
      rw [holeCirclePiece, Subtype.image_preimage_coe, Set.inter_eq_right]
      intro x hx
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    rw [himage]
    exact (holeCircle_isConnected charts i).isPreconnected

/-- Helper for Exercise 78.4: the connected components of the geometric boundary-circle union
are indexed by the chosen hole charts. -/
private lemma holeCircles_componentsEquivFin {X : Type u} [TopologicalSpace X] [T2Space X]
    {k : ℕ} (charts : HoleCharts X k) :
    Nonempty (ConnectedComponents (holeCircles charts) ≃ Fin k) := by
  -- Apply the canonical component equivalence to the finite clopen circle partition.
  refine ⟨ConnectedComponents.equivOfIsClopenOfIsConnected
    (fun i ↦ holeCirclePiece_isClopen charts i) ?_ ?_
    (fun i ↦ holeCirclePiece_isConnected charts i)⟩
  · intro i j hij
    exact Disjoint.preimage Subtype.val
      (holeCircle_pairwiseDisjoint charts (Set.mem_univ i) (Set.mem_univ j) hij)
  · apply Set.eq_univ_of_forall
    intro x
    have hxunion :
        x.1 ∈ ⋃ i : Fin k, charts i '' Metric.sphere 0 (1 / 2 : ℝ) := by
      simpa only [holeCircles] using x.2
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxunion
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩

/-- Helper for Exercise 78.4: the retained coordinate annulus of a hole chart. -/
private abbrev retainedAnnulus :=
  {x : EuclideanSpace ℝ (Fin 2) //
    x ∈ Metric.ball 0 1 ∧ x ∉ Metric.ball 0 (1 / 2 : ℝ)}

/-- Helper for Exercise 78.4: the polar collar before removing its outer endpoint. -/
private abbrev polarCollar :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1

/-- Helper for Exercise 78.4: the half-open polar collar is open in `S¹ × [0,1]`. -/
private lemma isOpen_polarCollar_lt_top :
    IsOpen {q : polarCollar | q.2.1 < 1} := by
  -- It is the preimage of the open ray under the continuous interval coordinate.
  exact isOpen_Iio.preimage (continuous_subtype_val.comp continuous_snd)

/-- Helper for Exercise 78.4: the open polar collar used as the annular model. -/
private def polarCollarOpen : Opens polarCollar :=
  ⟨{q | q.2.1 < 1}, isOpen_polarCollar_lt_top⟩

/-- Helper for Exercise 78.4: retained-annulus points have norm strictly below one. -/
private lemma retainedAnnulus_norm_lt_one (x : retainedAnnulus) :
    ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ < 1 := by
  -- Rewrite open-ball membership as the defining norm inequality.
  simpa only [Metric.mem_ball, dist_zero_right] using x.2.1

/-- Helper for Exercise 78.4: retained-annulus points have norm at least `1 / 2`. -/
private lemma retainedAnnulus_half_le_norm (x : retainedAnnulus) :
    (1 / 2 : ℝ) ≤ ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ := by
  -- Negated membership in the inner ball is the complementary norm inequality.
  simpa only [Metric.mem_ball, dist_zero_right, not_lt] using x.2.2

/-- Helper for Exercise 78.4: retained-annulus points are nonzero. -/
private lemma retainedAnnulus_ne_zero (x : retainedAnnulus) :
    (x.1 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
  -- A zero vector cannot have norm at least `1 / 2`.
  intro hx
  have hnorm := retainedAnnulus_half_le_norm x
  rw [hx, norm_zero] at hnorm
  norm_num at hnorm

/-- Helper for Exercise 78.4: radial normalization of an annular point lies on the unit circle. -/
private lemma retainedAnnulus_direction_mem (x : retainedAnnulus) :
    ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖⁻¹ • (x.1 : EuclideanSpace ℝ (Fin 2)) ∈
      Metric.sphere 0 1 := by
  -- The nonzero norm cancels after normalizing the vector.
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (retainedAnnulus_ne_zero x))]

/-- Helper for Exercise 78.4: the affine radial coordinate lies in `[0,1]`. -/
private lemma retainedAnnulus_radius_mem (x : retainedAnnulus) :
    2 * ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ - 1 ∈ Set.Icc (0 : ℝ) 1 := by
  -- The annular norm bounds become the two endpoint inequalities.
  constructor
  · linarith [retainedAnnulus_half_le_norm x]
  · linarith [retainedAnnulus_norm_lt_one x]

/-- Helper for Exercise 78.4: the annular radial coordinate avoids the outer collar endpoint. -/
private lemma retainedAnnulus_radius_lt_top (x : retainedAnnulus) :
    2 * ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ - 1 < 1 := by
  -- Strictness comes from the outer open unit ball.
  linarith [retainedAnnulus_norm_lt_one x]

/-- Helper for Exercise 78.4: polar coordinates send the retained annulus into the open collar. -/
private noncomputable def retainedAnnulusToPolarCollar
    (x : retainedAnnulus) : polarCollarOpen :=
  ⟨(⟨‖(x.1 : EuclideanSpace ℝ (Fin 2))‖⁻¹ • x.1,
      retainedAnnulus_direction_mem x⟩,
    ⟨2 * ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ - 1,
      retainedAnnulus_radius_mem x⟩),
    retainedAnnulus_radius_lt_top x⟩

/-- Helper for Exercise 78.4: the inverse polar radius is positive. -/
private lemma polarCollar_radius_pos (q : polarCollarOpen) :
    0 < (q.1.2.1 + 1) / 2 := by
  -- The interval coordinate is nonnegative.
  have hq := q.1.2.2.1
  linarith

/-- Helper for Exercise 78.4: scaling a collar direction by its inverse affine radius has
the expected norm. -/
private lemma polarCollar_scaled_norm (q : polarCollarOpen) :
    ‖((q.1.2.1 + 1) / 2) •
        (q.1.1.1 : EuclideanSpace ℝ (Fin 2))‖ = (q.1.2.1 + 1) / 2 := by
  -- The direction has unit norm and the radius is positive.
  have hdirection : ‖(q.1.1.1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using q.1.1.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (polarCollar_radius_pos q), hdirection, mul_one]

/-- Helper for Exercise 78.4: inverse polar coordinates land in the retained annulus. -/
private lemma polarCollarToRetainedAnnulus_mem (q : polarCollarOpen) :
    ((q.1.2.1 + 1) / 2) • (q.1.1.1 : EuclideanSpace ℝ (Fin 2)) ∈ Metric.ball 0 1 ∧
      ((q.1.2.1 + 1) / 2) • (q.1.1.1 : EuclideanSpace ℝ (Fin 2)) ∉
        Metric.ball 0 (1 / 2 : ℝ) := by
  -- The half-open interval bounds translate exactly to the annular norm bounds.
  simp only [Metric.mem_ball, dist_zero_right]
  rw [polarCollar_scaled_norm]
  constructor
  · have htop : q.1.2.1 < 1 := q.2
    linarith
  · rw [not_lt]
    linarith [q.1.2.2.1]

/-- Helper for Exercise 78.4: inverse polar coordinates on the open collar. -/
private noncomputable def polarCollarToRetainedAnnulus
    (q : polarCollarOpen) : retainedAnnulus :=
  ⟨((q.1.2.1 + 1) / 2) • (q.1.1.1 : EuclideanSpace ℝ (Fin 2)),
    polarCollarToRetainedAnnulus_mem q⟩

/-- Helper for Exercise 78.4: inverse polar coordinates undo radial normalization. -/
private lemma polarCollarToRetainedAnnulus_leftInverse :
    Function.LeftInverse polarCollarToRetainedAnnulus retainedAnnulusToPolarCollar := by
  -- The affine radius recovers the norm and cancels its reciprocal.
  intro x
  apply Subtype.ext
  simp only [polarCollarToRetainedAnnulus, retainedAnnulusToPolarCollar]
  rw [show (2 * ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ - 1 + 1) / 2 = ‖x.1‖ by ring]
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (retainedAnnulus_ne_zero x)), one_smul]

/-- Helper for Exercise 78.4: radial normalization undoes inverse polar coordinates. -/
private lemma polarCollarToRetainedAnnulus_rightInverse :
    Function.RightInverse polarCollarToRetainedAnnulus retainedAnnulusToPolarCollar := by
  -- Compare the direction and interval coordinates separately.
  intro q
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simp only [retainedAnnulusToPolarCollar, polarCollarToRetainedAnnulus]
    rw [polarCollar_scaled_norm, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (polarCollar_radius_pos q)), one_smul]
  · apply Subtype.ext
    simp only [retainedAnnulusToPolarCollar, polarCollarToRetainedAnnulus]
    rw [polarCollar_scaled_norm]
    ring

/-- Helper for Exercise 78.4: polar coordinates vary continuously on the retained annulus. -/
private lemma continuous_retainedAnnulusToPolarCollar :
    Continuous retainedAnnulusToPolarCollar := by
  -- All operations are continuous away from the excluded zero vector.
  apply continuous_induced_rng.2
  apply Continuous.prodMk
  · apply continuous_induced_rng.2
    exact (continuous_norm.comp continuous_subtype_val).inv₀
      (fun x ↦ norm_ne_zero_iff.mpr (retainedAnnulus_ne_zero x)) |>.smul
        continuous_subtype_val
  · apply continuous_induced_rng.2
    fun_prop

/-- Helper for Exercise 78.4: inverse polar coordinates vary continuously on the open collar. -/
private lemma continuous_polarCollarToRetainedAnnulus :
    Continuous polarCollarToRetainedAnnulus := by
  -- The inverse is an affine scalar multiple of the continuous unit direction.
  apply continuous_induced_rng.2
  fun_prop

/-- Helper for Exercise 78.4: the retained annulus is homeomorphic to the open polar collar. -/
private noncomputable def retainedAnnulusHomeomorphPolarCollar :
    retainedAnnulus ≃ₜ polarCollarOpen :=
  { toFun := retainedAnnulusToPolarCollar
    invFun := polarCollarToRetainedAnnulus
    left_inv := polarCollarToRetainedAnnulus_leftInverse
    right_inv := polarCollarToRetainedAnnulus_rightInverse
    continuous_toFun := continuous_retainedAnnulusToPolarCollar
    continuous_invFun := continuous_polarCollarToRetainedAnnulus }

/-- Helper for Exercise 78.4: placing the half-line coordinate first produces a point of
`EuclideanHalfSpace 2`. -/
private lemma modelProductToHalfSpace_mem
    (q : EuclideanSpace ℝ (Fin 1) × EuclideanHalfSpace 1) :
    0 ≤ (WithLp.toLp 2 ![q.2.1 0, q.1 0]) 0 := by
  -- The zeroth coordinate is exactly the nonnegative half-line coordinate.
  simpa using q.2.2

/-- Helper for Exercise 78.4: the product model maps to the standard two-dimensional
half-space by putting its half-line coordinate first. -/
private def modelProductToHalfSpace
    (q : EuclideanSpace ℝ (Fin 1) × EuclideanHalfSpace 1) : EuclideanHalfSpace 2 :=
  ⟨WithLp.toLp 2 ![q.2.1 0, q.1 0],
    modelProductToHalfSpace_mem q⟩

/-- Helper for Exercise 78.4: extracting the zeroth coordinate produces a point of the
one-dimensional half-space. -/
private lemma halfSpaceToModelProduct_mem (z : EuclideanHalfSpace 2) :
    0 ≤ WithLp.toLp 2 (fun _ : Fin 1 ↦ z.1 0) 0 := by
  -- The extracted coordinate inherits the half-space inequality.
  simpa using z.2

/-- Helper for Exercise 78.4: inverse coordinate splitting of the standard half-space. -/
private def halfSpaceToModelProduct
    (z : EuclideanHalfSpace 2) : EuclideanSpace ℝ (Fin 1) × EuclideanHalfSpace 1 :=
  (WithLp.toLp 2 (fun _ : Fin 1 ↦ z.1 1),
    ⟨WithLp.toLp 2 (fun _ : Fin 1 ↦ z.1 0), halfSpaceToModelProduct_mem z⟩)

/-- Helper for Exercise 78.4: splitting coordinates after joining the product model is the
identity. -/
private lemma halfSpaceToModelProduct_leftInverse :
    Function.LeftInverse halfSpaceToModelProduct modelProductToHalfSpace := by
  -- Extensionality reduces both one-dimensional coordinates to their unique index.
  intro q
  apply Prod.ext
  · ext i
    fin_cases i
    rfl
  · apply Subtype.ext
    ext i
    fin_cases i
    rfl

/-- Helper for Exercise 78.4: joining coordinates after splitting the half-space is the identity. -/
private lemma halfSpaceToModelProduct_rightInverse :
    Function.RightInverse halfSpaceToModelProduct modelProductToHalfSpace := by
  -- Extensionality separates the two coordinates of `Fin 2`.
  intro z
  apply Subtype.ext
  ext i
  fin_cases i
  · rfl
  · rfl

/-- Helper for Exercise 78.4: joining product-model coordinates is continuous. -/
private lemma continuous_modelProductToHalfSpace :
    Continuous modelProductToHalfSpace := by
  -- Both output coordinates are continuous coordinate projections.
  unfold modelProductToHalfSpace
  apply continuous_induced_rng.2
  fun_prop

/-- Helper for Exercise 78.4: splitting half-space coordinates is continuous. -/
private lemma continuous_halfSpaceToModelProduct :
    Continuous halfSpaceToModelProduct := by
  -- Each factor is assembled from a continuous coordinate projection.
  unfold halfSpaceToModelProduct
  fun_prop

/-- Helper for Exercise 78.4: the product of a line and a half-line is the standard
two-dimensional half-space. -/
private def modelProductHomeomorphHalfSpace :
    (EuclideanSpace ℝ (Fin 1) × EuclideanHalfSpace 1) ≃ₜ EuclideanHalfSpace 2 :=
  { toFun := modelProductToHalfSpace
    invFun := halfSpaceToModelProduct
    left_inv := halfSpaceToModelProduct_leftInverse
    right_inv := halfSpaceToModelProduct_rightInverse
    continuous_toFun := continuous_modelProductToHalfSpace
    continuous_invFun := continuous_halfSpaceToModelProduct }

/-- Helper for Exercise 78.4: the product chart on the open polar collar, expressed in the
standard two-dimensional half-space model. -/
private noncomputable def polarCollarChartAt (q : polarCollarOpen) :
    OpenPartialHomeomorph polarCollarOpen (EuclideanHalfSpace 2) :=
  (((chartAt (EuclideanSpace ℝ (Fin 1)) q.1.1).prod (IccLeftChart 0 1)).subtypeRestr
      ⟨q⟩).transHomeomorph modelProductHomeomorphHalfSpace

/-- Helper for Exercise 78.4: the selected product chart contains its collar base point. -/
private lemma mem_polarCollarChartAt_source (q : polarCollarOpen) :
    q ∈ (polarCollarChartAt q).source := by
  -- Both the sphere chart and the left interval chart contain their selected coordinates.
  rw [polarCollarChartAt, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    Set.preimage_univ, Set.inter_univ, OpenPartialHomeomorph.subtypeRestr_source]
  exact ⟨mem_chart_source (EuclideanSpace ℝ (Fin 1)) q.1.1, q.2⟩

/-- Helper for Exercise 78.4: the normal coordinate of the collar chart is its interval
coordinate. -/
private lemma polarCollarChartAt_apply_zero (q : polarCollarOpen) :
    (polarCollarChartAt q q).1 0 = q.1.2.1 := by
  -- Unfold only the chart interfaces; the left interval chart subtracts the zero endpoint.
  unfold polarCollarChartAt
  change (modelProductToHalfSpace
    ((((chartAt (EuclideanSpace ℝ (Fin 1)) q.1.1).prod (IccLeftChart 0 1)).subtypeRestr
      ⟨q⟩) q)).1 0 = q.1.2.1
  rw [OpenPartialHomeomorph.subtypeRestr_coe]
  simp only [Set.restrict_apply, OpenPartialHomeomorph.prod_apply,
    modelProductToHalfSpace, IccLeftChart]
  simp only [Fin.isValue, sub_zero, add_zero, unitInterval.coe_lt_one,
    OpenPartialHomeomorph.coe_mk, Matrix.cons_val_zero]

/-- Helper for Exercise 78.4: the collar chart meets the model frontier exactly at radial
coordinate zero. -/
private lemma polarCollarChartAt_boundary_iff (q : polarCollarOpen) :
    (polarCollarChartAt q).extend (𝓡∂ 2) q ∈
        frontier (Set.range (𝓡∂ 2)) ↔ q.1.2.1 = 0 := by
  -- The standard half-space frontier is the vanishing of the first coordinate.
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  simp only [Set.mem_setOf_eq]
  rw [OpenPartialHomeomorph.extend_coe]
  change 0 = (polarCollarChartAt q q).1 0 ↔ q.1.2.1 = 0
  rw [polarCollarChartAt_apply_zero]
  exact eq_comm

/-- Helper for Exercise 78.4: the half-space chart on the retained annulus obtained from
polar coordinates. -/
private noncomputable def retainedAnnulusChartAt (x : retainedAnnulus) :
    OpenPartialHomeomorph retainedAnnulus (EuclideanHalfSpace 2) :=
  retainedAnnulusHomeomorphPolarCollar.transOpenPartialHomeomorph
    (polarCollarChartAt (retainedAnnulusHomeomorphPolarCollar x))

/-- Helper for Exercise 78.4: the selected retained-annulus chart contains its base point. -/
private lemma mem_retainedAnnulusChartAt_source (x : retainedAnnulus) :
    x ∈ (retainedAnnulusChartAt x).source := by
  -- The homeomorphism carries the point into the source of its selected collar chart.
  rw [retainedAnnulusChartAt, Homeomorph.transOpenPartialHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    Set.univ_inter]
  exact mem_polarCollarChartAt_source _

/-- Helper for Exercise 78.4: the collar radial coordinate of an annular point is its
affinely rescaled norm. -/
private lemma retainedAnnulusHomeomorphPolarCollar_radius (x : retainedAnnulus) :
    (retainedAnnulusHomeomorphPolarCollar x).1.2.1 =
      2 * ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ - 1 := by
  -- This is the named projection interface for the polar-coordinate homeomorphism.
  rfl

/-- Helper for Exercise 78.4: the retained-annulus chart reaches the model frontier exactly on
the inner radius-`1 / 2` circle. -/
private lemma retainedAnnulusChartAt_boundary_iff (x : retainedAnnulus) :
    (retainedAnnulusChartAt x).extend (𝓡∂ 2) x ∈
        frontier (Set.range (𝓡∂ 2)) ↔
      ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ = 1 / 2 := by
  -- Expose the transported chart value, then translate its affine radius back to a norm.
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  simp only [Set.mem_setOf_eq]
  rw [OpenPartialHomeomorph.extend_coe]
  change 0 =
      (polarCollarChartAt (retainedAnnulusHomeomorphPolarCollar x)
        (retainedAnnulusHomeomorphPolarCollar x)).1 0 ↔
      ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ = 1 / 2
  rw [polarCollarChartAt_apply_zero]
  rw [retainedAnnulusHomeomorphPolarCollar_radius]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Helper for Exercise 78.4: the retained annulus lies in the source of every hole chart. -/
private lemma retainedAnnulus_subset_holeChart_source
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    {x : EuclideanSpace ℝ (Fin 2) |
      x ∈ Metric.ball 0 1 ∧ x ∉ Metric.ball 0 (1 / 2 : ℝ)} ⊆ (charts i).source := by
  -- The first annulus condition is exactly membership in the unit-ball chart source.
  rw [charts.source_eq]
  exact fun _ hx ↦ hx.1

/-- Helper for Exercise 78.4: the image of the retained annulus in the `i`th hole chart. -/
private def retainedAnnulusImage
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    Set X :=
  charts i '' {x : EuclideanSpace ℝ (Fin 2) |
    x ∈ Metric.ball 0 1 ∧ x ∉ Metric.ball 0 (1 / 2 : ℝ)}

/-- Helper for Exercise 78.4: the defining image of the retained annulus has its named form. -/
private lemma image_retainedAnnulus_eq
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    charts i '' {x : EuclideanSpace ℝ (Fin 2) |
      x ∈ Metric.ball 0 1 ∧ x ∉ Metric.ball 0 (1 / 2 : ℝ)} =
        retainedAnnulusImage charts i := by
  -- This lemma keeps later homeomorphism construction independent of the definition body.
  rfl

/-- Helper for Exercise 78.4: a retained annulus image is the part of its chart target left
after deleting all chosen open half-disks. -/
private lemma retainedAnnulusImage_eq_target_inter_compl_removedDisks
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    retainedAnnulusImage charts i =
      (charts i).target ∩ (removedDisks charts)ᶜ := by
  -- In the forward direction, pairwise disjoint chart targets exclude every other hole.
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · exact (charts i).map_source (retainedAnnulus_subset_holeChart_source charts i hx)
    · rw [Set.mem_compl_iff]
      intro hzRemoved
      obtain ⟨j, y, hyBall, hyEq⟩ := (mem_removedDisks charts _).mp hzRemoved
      have hySource : y ∈ (charts j).source := by
        rw [charts.source_eq]
        exact Metric.ball_subset_ball (by norm_num) hyBall
      by_cases hji : j = i
      · subst j
        have hxy : y = x := (charts i).injOn hySource
          (retainedAnnulus_subset_holeChart_source charts i hx) hyEq
        exact hx.2 (hxy ▸ hyBall)
      · have htargets := charts.pairwiseDisjoint_target
          (Set.mem_univ j) (Set.mem_univ i) hji
        exact Set.disjoint_left.mp htargets ((charts j).map_source hySource)
          (hyEq ▸ (charts i).map_source
            (retainedAnnulus_subset_holeChart_source charts i hx))
  · rintro ⟨hzTarget, hzOutside⟩
    let x := (charts i).symm z
    have hxSource : x ∈ (charts i).source := (charts i).map_target hzTarget
    have hxOuter : x ∈ Metric.ball 0 1 := by
      rw [← charts.source_eq i]
      exact hxSource
    have hxInner : x ∉ Metric.ball 0 (1 / 2 : ℝ) := by
      intro hxBall
      rw [Set.mem_compl_iff] at hzOutside
      apply hzOutside
      rw [mem_removedDisks]
      refine ⟨i, x, hxBall, ?_⟩
      exact (charts i).right_inv hzTarget
    refine ⟨x, ⟨hxOuter, hxInner⟩, ?_⟩
    exact (charts i).right_inv hzTarget

/-- Helper for Exercise 78.4: a retained annulus image is contained in the punctured surface. -/
private lemma retainedAnnulusImage_subset_compl_removedDisks
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    retainedAnnulusImage charts i ⊆ (removedDisks charts)ᶜ := by
  -- Project the normal-form equality to its complement factor.
  rw [retainedAnnulusImage_eq_target_inter_compl_removedDisks]
  exact Set.inter_subset_right

/-- Helper for Exercise 78.4: a retained coordinate annulus is homeomorphic to its image in a
hole chart. -/
private noncomputable def retainedAnnulusHomeomorphImage
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    retainedAnnulus ≃ₜ retainedAnnulusImage charts i :=
  (charts i).homeomorphOfImageSubsetSource
    (retainedAnnulus_subset_holeChart_source charts i)
    (image_retainedAnnulus_eq charts i)

/-- Helper for Exercise 78.4: the retained-annulus image is open relative to the complement of
the deleted disks. -/
private lemma retainedAnnulusImage_isOpen_in_compl_removedDisks
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    IsOpen (Subtype.val ⁻¹' retainedAnnulusImage charts i : Set (withHoles charts)) := by
  -- In the complement subtype, the annulus image is just the preimage of the open chart target.
  have heq :
      (Subtype.val ⁻¹' retainedAnnulusImage charts i : Set (withHoles charts)) =
        Subtype.val ⁻¹' (charts i).target := by
    ext z
    rw [Set.mem_preimage]
    constructor
    · intro hz
      rw [retainedAnnulusImage_eq_target_inter_compl_removedDisks] at hz
      exact hz.1
    · intro hz
      rw [retainedAnnulusImage_eq_target_inter_compl_removedDisks]
      exact ⟨hz, z.2⟩
  rw [heq]
  exact (charts i).open_target.preimage continuous_subtype_val

/-- Helper for Exercise 78.4: the retained annulus includes openly into the punctured surface. -/
private noncomputable def retainedAnnulusEmbedding
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    retainedAnnulus → withHoles charts :=
  Set.inclusion (retainedAnnulusImage_subset_compl_removedDisks charts i) ∘
    retainedAnnulusHomeomorphImage charts i

/-- Helper for Exercise 78.4: the annular inclusion is an open topological embedding. -/
private lemma retainedAnnulusEmbedding_isOpenEmbedding
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k) :
    Topology.IsOpenEmbedding (retainedAnnulusEmbedding charts i) := by
  -- Compose the annulus homeomorphism with inclusion of its relatively open image.
  exact (Topology.IsOpenEmbedding.inclusion
    (retainedAnnulusImage_subset_compl_removedDisks charts i)
    (retainedAnnulusImage_isOpen_in_compl_removedDisks charts i)).comp
      (retainedAnnulusHomeomorphImage charts i).isOpenEmbedding

/-- Helper for Exercise 78.4: the ambient value of the annular embedding is the value of the
chosen hole chart. -/
private lemma coe_retainedAnnulusEmbedding
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k)
    (x : retainedAnnulus) :
    ((retainedAnnulusEmbedding charts i x : withHoles charts) : X) = charts i x.1 := by
  -- Both subtype inclusions erase to the original hole-chart map.
  rfl

/-- Helper for Exercise 78.4: the half-space chart on an annulus, lifted to the punctured
surface. -/
private noncomputable def liftedRetainedAnnulusChartAt
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k)
    (x : retainedAnnulus) :
    OpenPartialHomeomorph (withHoles charts) (EuclideanHalfSpace 2) :=
  (retainedAnnulusChartAt x).lift_openEmbedding
    (retainedAnnulusEmbedding_isOpenEmbedding charts i)

/-- Helper for Exercise 78.4: a lifted annular chart contains its embedded base point. -/
private lemma mem_liftedRetainedAnnulusChartAt_source
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k)
    (x : retainedAnnulus) :
    retainedAnnulusEmbedding charts i x ∈
      (liftedRetainedAnnulusChartAt charts i x).source := by
  -- The lifted source is the image of the original annular chart source.
  rw [liftedRetainedAnnulusChartAt, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨x, mem_retainedAnnulusChartAt_source x, rfl⟩

/-- Helper for Exercise 78.4: lifting an annular chart preserves its exact boundary criterion. -/
private lemma liftedRetainedAnnulusChartAt_boundary_iff
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) (i : Fin k)
    (x : retainedAnnulus) :
    (liftedRetainedAnnulusChartAt charts i x).extend (𝓡∂ 2)
        (retainedAnnulusEmbedding charts i x) ∈ frontier (Set.range (𝓡∂ 2)) ↔
      ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ = 1 / 2 := by
  -- Evaluate the lifted chart at its embedded point and reuse the annular frontier interface.
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  simp only [Set.mem_setOf_eq]
  rw [OpenPartialHomeomorph.extend_coe]
  change 0 =
      (liftedRetainedAnnulusChartAt charts i x
        (retainedAnnulusEmbedding charts i x)).1 0 ↔
      ‖(x.1 : EuclideanSpace ℝ (Fin 2))‖ = 1 / 2
  rw [liftedRetainedAnnulusChartAt,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  have hannulus := retainedAnnulusChartAt_boundary_iff x
  rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hannulus
  simp only [Set.mem_setOf_eq] at hannulus
  rw [OpenPartialHomeomorph.extend_coe] at hannulus
  exact hannulus

/-- Helper for Exercise 78.4: a point on the half-radius coordinate circle defines a retained
annulus point. -/
private lemma halfSpherePoint_mem_retainedAnnulus
    (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ)) :
    (y.1 ∈ Metric.ball 0 1 ∧ y.1 ∉ Metric.ball 0 (1 / 2 : ℝ)) := by
  -- The sphere lies in the larger unit ball and is disjoint from its own open ball.
  constructor
  · exact Metric.sphere_subset_ball (by norm_num) y.2
  · exact Set.disjoint_left.mp Metric.sphere_disjoint_ball y.2

/-- Helper for Exercise 78.4: include the half-radius sphere into the retained annulus. -/
private def halfSpherePointToRetainedAnnulus
    (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ)) :
    retainedAnnulus :=
  ⟨y.1, halfSpherePoint_mem_retainedAnnulus y⟩

/-- Helper for Exercise 78.4: the retained-annulus point coming from a half-radius sphere has
norm exactly `1 / 2`. -/
private lemma norm_halfSpherePointToRetainedAnnulus
    (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ)) :
    ‖((halfSpherePointToRetainedAnnulus y).1 : EuclideanSpace ℝ (Fin 2))‖ = 1 / 2 := by
  -- Sphere membership is the norm equality because the center is zero.
  simpa only [halfSpherePointToRetainedAnnulus, Metric.mem_sphere, dist_zero_right] using y.2

/-- Helper for Exercise 78.4: every geometric boundary-circle point has a local half-space chart
whose selected point lies on the model frontier. -/
private lemma exists_boundaryHalfSpaceChart
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k)
    (p : withHoles charts) (hp : (p.1 : X) ∈ holeCircles charts) :
    ∃ e : OpenPartialHomeomorph (withHoles charts) (EuclideanHalfSpace 2),
      p ∈ e.source ∧
        e.extend (𝓡∂ 2) p ∈ frontier (Set.range (𝓡∂ 2)) := by
  -- Choose the unique circle chart witnessing the geometric boundary membership.
  rw [holeCircles] at hp
  obtain ⟨i, y, hySphere, hyEq⟩ := Set.mem_iUnion.mp hp
  let ys : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2 : ℝ) := ⟨y, hySphere⟩
  let x := halfSpherePointToRetainedAnnulus ys
  have hembedding : retainedAnnulusEmbedding charts i x = p := by
    apply Subtype.ext
    rw [coe_retainedAnnulusEmbedding]
    exact hyEq
  refine ⟨liftedRetainedAnnulusChartAt charts i x, ?_, ?_⟩
  · rw [← hembedding]
    exact mem_liftedRetainedAnnulusChartAt_source charts i x
  · rw [← hembedding, liftedRetainedAnnulusChartAt_boundary_iff]
    exact norm_halfSpherePointToRetainedAnnulus ys

/-- Helper for Exercise 78.4: the finite union of closed half-disks in the chosen hole charts. -/
private def closedHoleDisks
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) : Set X :=
  ⋃ i, charts i '' Metric.closedBall 0 (1 / 2 : ℝ)

/-- Helper for Exercise 78.4: the closed half-disk union is closed in a Hausdorff surface. -/
private lemma closedHoleDisks_isClosed
    {X : Type u} [TopologicalSpace X] [T2Space X] {k : ℕ} (charts : HoleCharts X k) :
    IsClosed (closedHoleDisks charts) := by
  -- Each closed coordinate disk is compact, and the family is finite.
  apply isClosed_iUnion_of_finite
  intro i
  exact ((isCompact_closedBall 0 (1 / 2 : ℝ)).image_of_continuousOn
    ((charts i).continuousOn.mono fun _ hx ↦ by
      rw [charts.source_eq]
      exact Metric.closedBall_subset_ball (by norm_num) hx)).isClosed

/-- Helper for Exercise 78.4: the open region lying outside every closed half-disk. -/
private def safeInterior
    {X : Type u} [TopologicalSpace X] [T2Space X] {k : ℕ} (charts : HoleCharts X k) :
    Opens X :=
  ⟨(closedHoleDisks charts)ᶜ, (closedHoleDisks_isClosed charts).isOpen_compl⟩

/-- Helper for Exercise 78.4: the safe interior region avoids all deleted open disks. -/
private lemma safeInterior_subset_compl_removedDisks
    {X : Type u} [TopologicalSpace X] [T2Space X] {k : ℕ} (charts : HoleCharts X k) :
    (safeInterior charts : Set X) ⊆ (removedDisks charts)ᶜ := by
  -- Every deleted open half-disk is contained in the corresponding closed half-disk.
  intro z hzSafe
  rw [Set.mem_compl_iff]
  intro hzRemoved
  obtain ⟨i, y, hyBall, rfl⟩ := (mem_removedDisks charts z).mp hzRemoved
  apply hzSafe
  exact Set.mem_iUnion.mpr
    ⟨i, ⟨y, Metric.ball_subset_closedBall hyBall, rfl⟩⟩

/-- Helper for Exercise 78.4: inclusion of the safe open region into the punctured surface. -/
private def safeInteriorInclusion
    {X : Type u} [TopologicalSpace X] [T2Space X] {k : ℕ} (charts : HoleCharts X k) :
    safeInterior charts → withHoles charts :=
  Set.inclusion (safeInterior_subset_compl_removedDisks charts)

/-- Helper for Exercise 78.4: the safe region includes openly into the punctured surface. -/
private lemma safeInteriorInclusion_isOpenEmbedding
    {X : Type u} [TopologicalSpace X] [T2Space X] {k : ℕ} (charts : HoleCharts X k) :
    Topology.IsOpenEmbedding (safeInteriorInclusion charts) := by
  -- Ambient openness remains openness after restricting to the punctured subtype.
  apply Topology.IsOpenEmbedding.inclusion
    (safeInterior_subset_compl_removedDisks charts)
  exact (safeInterior charts).isOpen.preimage continuous_subtype_val

/-- Helper for Exercise 78.4: a punctured-surface point off all boundary circles lies outside
every closed half-disk. -/
private lemma mem_safeInterior_of_not_mem_holeCircles
    {X : Type u} [TopologicalSpace X] [T2Space X] {k : ℕ} (charts : HoleCharts X k)
    (p : withHoles charts) (hp : (p.1 : X) ∉ holeCircles charts) :
    (p.1 : X) ∈ safeInterior charts := by
  -- A point in a closed half-disk but not its open disk must lie on the boundary circle.
  change (p.1 : X) ∈ (closedHoleDisks charts)ᶜ
  rw [Set.mem_compl_iff]
  intro hpClosed
  obtain ⟨i, y, hyClosed, hyEq⟩ := Set.mem_iUnion.mp hpClosed
  have hyNotBall : y ∉ Metric.ball 0 (1 / 2 : ℝ) := by
    intro hyBall
    apply p.2
    rw [mem_removedDisks]
    exact ⟨i, y, hyBall, hyEq⟩
  have hySphere : y ∈ Metric.sphere 0 (1 / 2 : ℝ) := by
    rw [← Metric.closedBall_sdiff_ball]
    exact ⟨hyClosed, hyNotBall⟩
  apply hp
  rw [holeCircles]
  exact Set.mem_iUnion.mpr ⟨i, y, hySphere, hyEq⟩

/-- Helper for Exercise 78.4: the center of a small ball lying strictly inside the model
half-space. -/
private def interiorChartCenter : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun _ ↦ 1)

/-- Helper for Exercise 78.4: the zeroth coordinate of the interior chart center is one. -/
private lemma interiorChartCenter_zero : interiorChartCenter 0 = 1 := by
  -- Evaluate the constant coordinate vector at the zeroth index.
  rfl

/-- Helper for Exercise 78.4: the radius used for the interior model ball is positive. -/
private lemma interiorChartRadius_pos : (0 : ℝ) < 1 / 2 := by
  -- This is the fixed positive half-radius.
  norm_num

/-- Helper for Exercise 78.4: every point in the selected model ball has positive zeroth
coordinate. -/
private lemma interiorChartBall_zero_pos
    {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Metric.ball interiorChartCenter (1 / 2 : ℝ)) : 0 < y 0 := by
  -- Coordinate distance is bounded by Euclidean distance from the center.
  have hcoordinate : dist (y 0) (interiorChartCenter 0) ≤ dist y interiorChartCenter :=
    PiLp.dist_apply_le y interiorChartCenter 0
  rw [interiorChartCenter_zero, Real.dist_eq] at hcoordinate
  rw [Metric.mem_ball] at hy
  have habs : |y 0 - 1| < 1 / 2 := lt_of_le_of_lt hcoordinate hy
  rw [abs_lt] at habs
  linarith

/-- Helper for Exercise 78.4: the selected interior ball lies in the model half-space. -/
private lemma interiorChartBall_subset_halfSpace :
    Metric.ball interiorChartCenter (1 / 2 : ℝ) ⊆
      {y : EuclideanSpace ℝ (Fin 2) | 0 ≤ y 0} := by
  -- Strict positivity from the ball estimate implies the half-space inequality.
  intro y hy
  exact (interiorChartBall_zero_pos hy).le

/-- Helper for Exercise 78.4: the canonical Euclidean-to-ball chart has the named interior ball
as its target. -/
private lemma euclideanInteriorBall_target :
    (OpenPartialHomeomorph.univBall interiorChartCenter (1 / 2 : ℝ)).target =
      Metric.ball interiorChartCenter (1 / 2 : ℝ) := by
  -- Use the positive-radius target computation for the canonical ball chart.
  exact OpenPartialHomeomorph.univBall_target interiorChartCenter interiorChartRadius_pos

/-- Helper for Exercise 78.4: the canonical Euclidean-to-ball chart has full source. -/
private lemma euclideanInteriorBall_source :
    (OpenPartialHomeomorph.univBall interiorChartCenter (1 / 2 : ℝ)).source = Set.univ := by
  -- The canonical ball chart is globally defined on Euclidean space.
  exact OpenPartialHomeomorph.univBall_source interiorChartCenter (1 / 2 : ℝ)

/-- Helper for Exercise 78.4: Euclidean space is homeomorphic to the small interior model ball. -/
private noncomputable def euclideanHomeomorphInteriorBall :
    EuclideanSpace ℝ (Fin 2) ≃ₜ Metric.ball interiorChartCenter (1 / 2 : ℝ) :=
  (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 2))).symm |>.trans
    ((Homeomorph.setCongr euclideanInteriorBall_source).symm |>.trans
      ((OpenPartialHomeomorph.univBall interiorChartCenter
        (1 / 2 : ℝ)).toHomeomorphSourceTarget |>.trans
          (Homeomorph.setCongr euclideanInteriorBall_target)))

/-- Helper for Exercise 78.4: inclusion of the small interior ball into the half-space model. -/
private def interiorBallInclusion :
    Metric.ball interiorChartCenter (1 / 2 : ℝ) → EuclideanHalfSpace 2 :=
  Set.inclusion interiorChartBall_subset_halfSpace

/-- Helper for Exercise 78.4: the small interior ball includes openly into the half-space. -/
private lemma interiorBallInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding interiorBallInclusion := by
  -- The metric ball is open both ambiently and relative to the half-space.
  apply Topology.IsOpenEmbedding.inclusion interiorChartBall_subset_halfSpace
  exact (Metric.isOpen_ball : IsOpen (Metric.ball interiorChartCenter (1 / 2 : ℝ))).preimage
    continuous_subtype_val

/-- Helper for Exercise 78.4: an open embedding of Euclidean space into the interior of the
half-space model. -/
private noncomputable def euclideanInteriorEmbedding :
    EuclideanSpace ℝ (Fin 2) → EuclideanHalfSpace 2 :=
  interiorBallInclusion ∘ euclideanHomeomorphInteriorBall

/-- Helper for Exercise 78.4: the Euclidean interior embedding is open. -/
private lemma euclideanInteriorEmbedding_isOpenEmbedding :
    Topology.IsOpenEmbedding euclideanInteriorEmbedding := by
  -- Compose the Euclidean-to-ball homeomorphism with the relatively open ball inclusion.
  exact interiorBallInclusion_isOpenEmbedding.comp
    euclideanHomeomorphInteriorBall.isOpenEmbedding

/-- Helper for Exercise 78.4: the Euclidean interior embedding has positive normal coordinate. -/
private lemma euclideanInteriorEmbedding_zero_pos (x : EuclideanSpace ℝ (Fin 2)) :
    0 < (euclideanInteriorEmbedding x).1 0 := by
  -- Its underlying point belongs to the chosen interior ball.
  exact interiorChartBall_zero_pos (euclideanHomeomorphInteriorBall x).2

/-- Helper for Exercise 78.4: the Euclidean interior embedding as an open partial homeomorphism. -/
private noncomputable def euclideanInteriorChart :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 2) :=
  euclideanInteriorEmbedding_isOpenEmbedding.toOpenPartialHomeomorph
    euclideanInteriorEmbedding

/-- Helper for Exercise 78.4: the Euclidean interior chart is defined everywhere. -/
private lemma euclideanInteriorChart_source : euclideanInteriorChart.source = Set.univ := by
  -- Open embeddings produce partial homeomorphisms with full source.
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source
    euclideanInteriorEmbedding euclideanInteriorEmbedding_isOpenEmbedding

/-- Helper for Exercise 78.4: postcomposing any chart with the interior model chart avoids the
model frontier at every point. -/
private lemma trans_euclideanInteriorChart_not_boundary
    {A : Type*} [TopologicalSpace A]
    (e : OpenPartialHomeomorph A (EuclideanSpace ℝ (Fin 2))) (x : A) :
    (e.trans euclideanInteriorChart).extend (𝓡∂ 2) x ∉
      frontier (Set.range (𝓡∂ 2)) := by
  -- The final chart value has strictly positive zeroth coordinate.
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  simp only [Set.mem_setOf_eq]
  rw [OpenPartialHomeomorph.extend_coe]
  change ¬0 = (euclideanInteriorEmbedding (e x)).1 0
  exact (ne_of_gt (euclideanInteriorEmbedding_zero_pos (e x))).symm

/-- Helper for Exercise 78.4: the lifted interior chart selected at a point of the safe region. -/
private noncomputable def liftedSafeInteriorChartAt
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (q : safeInterior charts) :
    OpenPartialHomeomorph (withHoles charts) (EuclideanHalfSpace 2) :=
  (((chartAt (EuclideanSpace ℝ (Fin 2)) q.1).subtypeRestr ⟨q⟩).trans
    euclideanInteriorChart).lift_openEmbedding
      (safeInteriorInclusion_isOpenEmbedding charts)

/-- Helper for Exercise 78.4: a lifted safe-region chart contains its embedded base point. -/
private lemma mem_liftedSafeInteriorChartAt_source
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (q : safeInterior charts) :
    safeInteriorInclusion charts q ∈ (liftedSafeInteriorChartAt charts q).source := by
  -- The restricted original chart contains `q`, and the interior postchart has full source.
  rw [liftedSafeInteriorChartAt, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨q, ?_, rfl⟩
  rw [OpenPartialHomeomorph.trans_source, euclideanInteriorChart_source,
    Set.preimage_univ, Set.inter_univ, OpenPartialHomeomorph.subtypeRestr_source]
  exact mem_chart_source (EuclideanSpace ℝ (Fin 2)) q.1

/-- Helper for Exercise 78.4: a lifted safe-region chart avoids the model frontier. -/
private lemma liftedSafeInteriorChartAt_not_boundary
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (q : safeInterior charts) :
    (liftedSafeInteriorChartAt charts q).extend (𝓡∂ 2)
        (safeInteriorInclusion charts q) ∉ frontier (Set.range (𝓡∂ 2)) := by
  -- Evaluate the lifted chart and apply the strict-interior computation of the postchart.
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  simp only [Set.mem_setOf_eq]
  rw [OpenPartialHomeomorph.extend_coe]
  change ¬0 =
    (liftedSafeInteriorChartAt charts q (safeInteriorInclusion charts q)).1 0
  rw [liftedSafeInteriorChartAt, OpenPartialHomeomorph.lift_openEmbedding_apply]
  have hcore := trans_euclideanInteriorChart_not_boundary
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q.1).subtypeRestr ⟨q⟩) q
  rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hcore
  simp only [Set.mem_setOf_eq] at hcore
  rw [OpenPartialHomeomorph.extend_coe] at hcore
  exact hcore

/-- Helper for Exercise 78.4: every point away from the geometric boundary circles has a local
half-space chart whose selected point lies off the model frontier. -/
private lemma exists_interiorHalfSpaceChart
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (p : withHoles charts)
    (hp : (p.1 : X) ∉ holeCircles charts) :
    ∃ e : OpenPartialHomeomorph (withHoles charts) (EuclideanHalfSpace 2),
      p ∈ e.source ∧ e.extend (𝓡∂ 2) p ∉ frontier (Set.range (𝓡∂ 2)) := by
  -- Regard `p` as a point of the safe open region and use its lifted original chart.
  let q : safeInterior charts := ⟨p.1, mem_safeInterior_of_not_mem_holeCircles charts p hp⟩
  have hembedding : safeInteriorInclusion charts q = p := by
    apply Subtype.ext
    rfl
  refine ⟨liftedSafeInteriorChartAt charts q, ?_, ?_⟩
  · rw [← hembedding]
    exact mem_liftedSafeInteriorChartAt_source charts q
  · rw [← hembedding]
    exact liftedSafeInteriorChartAt_not_boundary charts q

/-- Helper for Exercise 78.4: every punctured-surface point has a local half-space chart whose
frontier flag is exactly membership in the geometric hole circles. -/
private lemma exists_localHalfSpaceChart_withBoundarySpec
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (p : withHoles charts) :
    ∃ e : OpenPartialHomeomorph (withHoles charts) (EuclideanHalfSpace 2),
      p ∈ e.source ∧
        (e.extend (𝓡∂ 2) p ∈ frontier (Set.range (𝓡∂ 2)) ↔
          (p.1 : X) ∈ holeCircles charts) := by
  -- Use the annular chart on a boundary circle and the safe-region chart otherwise.
  by_cases hp : (p.1 : X) ∈ holeCircles charts
  · obtain ⟨e, hpSource, hpBoundary⟩ := exists_boundaryHalfSpaceChart charts p hp
    exact ⟨e, hpSource, ⟨fun _ ↦ hp, fun _ ↦ hpBoundary⟩⟩
  · obtain ⟨e, hpSource, hpInterior⟩ := exists_interiorHalfSpaceChart charts p hp
    exact ⟨e, hpSource, ⟨fun h ↦ (hpInterior h).elim, fun h ↦ (hp h).elim⟩⟩

/-- Helper for Exercise 78.4: choose a specified local half-space chart at each punctured-surface
point. -/
private noncomputable def selectedWithHolesChart
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (p : withHoles charts) :
    OpenPartialHomeomorph (withHoles charts) (EuclideanHalfSpace 2) :=
  Classical.choose (exists_localHalfSpaceChart_withBoundarySpec charts p)

/-- Helper for Exercise 78.4: the selected local chart contains its base point. -/
private lemma mem_selectedWithHolesChart_source
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (p : withHoles charts) :
    p ∈ (selectedWithHolesChart charts p).source := by
  -- Extract the source clause from the choice specification.
  exact (Classical.choose_spec (exists_localHalfSpaceChart_withBoundarySpec charts p)).1

/-- Helper for Exercise 78.4: the selected chart's model-frontier flag is geometric circle
membership. -/
private lemma selectedWithHolesChart_boundary_iff
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (p : withHoles charts) :
    (selectedWithHolesChart charts p).extend (𝓡∂ 2) p ∈
        frontier (Set.range (𝓡∂ 2)) ↔ (p.1 : X) ∈ holeCircles charts := by
  -- Extract the exact frontier clause from the choice specification.
  exact (Classical.choose_spec (exists_localHalfSpaceChart_withBoundarySpec charts p)).2

/-- Helper for Exercise 78.4: every selected chart lies in the range atlas. -/
private lemma selectedWithHolesChart_mem_range
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) (p : withHoles charts) :
    selectedWithHolesChart charts p ∈ Set.range (selectedWithHolesChart charts) := by
  -- The point itself witnesses range membership.
  exact ⟨p, rfl⟩

/-- Helper for Exercise 78.4: the selected local charts form a half-space charted-space
structure on the punctured surface. -/
@[implicit_reducible]
private noncomputable def withHolesHalfSpaceChartedSpace
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) :
    ChartedSpace (EuclideanHalfSpace 2) (withHoles charts) :=
  { atlas := Set.range (selectedWithHolesChart charts)
    chartAt := selectedWithHolesChart charts
    mem_chart_source := mem_selectedWithHolesChart_source charts
    chart_mem_atlas := selectedWithHolesChart_mem_range charts }

/-- Helper for Exercise 78.4: the boundary of the selected atlas is exactly the subtype over the
geometric union of hole circles. -/
private lemma boundaryWith_withHolesHalfSpaceChartedSpace
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X]
    {k : ℕ} (charts : HoleCharts X k) :
    @Surface.boundaryWith (withHoles charts) _ (withHolesHalfSpaceChartedSpace charts) =
      {p : withHoles charts | (p.1 : X) ∈ holeCircles charts} := by
  -- Boundary membership unfolds to the selected chart's exact frontier specification.
  ext p
  change (selectedWithHolesChart charts p).extend (𝓡∂ 2) p ∈
      frontier (Set.range (𝓡∂ 2)) ↔ (p.1 : X) ∈ holeCircles charts
  exact selectedWithHolesChart_boundary_iff charts p

/-- Helper for Exercise 78.4: every geometric hole circle avoids all deleted open disks. -/
private lemma holeCircles_subset_compl_removedDisks
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) :
    holeCircles charts ⊆ (removedDisks charts)ᶜ := by
  -- A circle point belongs to its retained annulus, which already lies in the complement.
  intro z hz
  rw [holeCircles] at hz
  obtain ⟨i, y, hySphere, rfl⟩ := Set.mem_iUnion.mp hz
  apply retainedAnnulusImage_subset_compl_removedDisks charts i
  refine ⟨y, ⟨Metric.sphere_subset_ball (by norm_num) hySphere, ?_⟩, rfl⟩
  exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hySphere

/-- Helper for Exercise 78.4: forgetting the punctured-surface proof maps the geometric
boundary subtype exactly onto the union of hole circles. -/
private lemma image_geometricBoundary_subtypeVal
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) :
    (Subtype.val : withHoles charts → X) ''
        {p : withHoles charts | (p.1 : X) ∈ holeCircles charts} = holeCircles charts := by
  -- Forward membership is immediate; conversely the complement lemma supplies the subtype proof.
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hz
    refine ⟨⟨z, holeCircles_subset_compl_removedDisks charts hz⟩, hz, rfl⟩

/-- Helper for Exercise 78.4: the boundary subtype of the punctured surface is homeomorphic
to the ambient union of geometric hole circles. -/
private noncomputable def geometricBoundaryHomeomorphHoleCircles
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) :
    {p : withHoles charts | (p.1 : X) ∈ holeCircles charts} ≃ₜ holeCircles charts :=
  Topology.IsEmbedding.subtypeVal.homeomorphImage
      {p : withHoles charts | (p.1 : X) ∈ holeCircles charts} |>.trans
    (Homeomorph.setCongr (image_geometricBoundary_subtypeVal charts))

/-- Helper for Exercise 78.4: a fiber of a homeomorphism is a connected singleton. -/
private lemma homeomorphPreimageSingleton_isConnected
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (y : B) : IsConnected (e ⁻¹' {y}) := by
  -- Bijectivity identifies the fiber with the singleton containing the inverse image.
  have hfiber : e ⁻¹' {y} = {e.symm y} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  rw [hfiber]
  exact isConnected_singleton

/-- Helper for Exercise 78.4: the two boundary models have equivalent connected-component
spaces. -/
private noncomputable def geometricBoundaryComponentsHomeomorphHoleCircles
    {X : Type u} [TopologicalSpace X] {k : ℕ} (charts : HoleCharts X k) :
    ConnectedComponents
        {p : withHoles charts | (p.1 : X) ∈ holeCircles charts} ≃ₜ
      ConnectedComponents (holeCircles charts) :=
  let e := geometricBoundaryHomeomorphHoleCircles charts
  e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (fun y ↦ homeomorphPreimageSingleton_isConnected e y)

end Surface

/-- Exercise 78.4. Deleting the images of the concentric radius-`1 / 2` disks from
`k` pairwise disjoint disk charts on a 2-manifold produces a 2-manifold with boundary
whose boundary has exactly `k` connected components. -/
theorem withHoles_isTwoManifoldWithBoundary
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) 0 X]
    [T2Space X] [SecondCountableTopology X]
    {k : ℕ} (charts : Surface.HoleCharts X k) :
      ∃ c : ChartedSpace (EuclideanHalfSpace 2) (Surface.withHoles charts),
        Surface.IsManifoldWithBoundary c ∧
        Cardinal.mk (ConnectedComponents
          (Surface.boundaryWith c)) = k := by
  -- Install the explicitly selected atlas so the universal order-zero manifold instance applies.
  letI : ChartedSpace (EuclideanHalfSpace 2) (Surface.withHoles charts) :=
    Surface.withHolesHalfSpaceChartedSpace charts
  letI : SecondCountableTopology (Surface.withHoles charts) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  refine ⟨Surface.withHolesHalfSpaceChartedSpace charts, ?_, ?_⟩
  · -- Separation and countability pass to the subtype, while every charted space is `C⁰`.
    rw [Surface.isManifoldWithBoundary_iff]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · -- Replace the atlas boundary by its geometric model and then use the circle partition.
    rw [Surface.boundaryWith_withHolesHalfSpaceChartedSpace charts]
    obtain ⟨e⟩ := Surface.holeCircles_componentsEquivFin charts
    calc
      Cardinal.mk (ConnectedComponents
          {p : Surface.withHoles charts |
            (p.1 : X) ∈ Surface.holeCircles charts}) =
          Cardinal.mk (ConnectedComponents (Surface.holeCircles charts)) :=
        Cardinal.mk_congr
          (Surface.geometricBoundaryComponentsHomeomorphHoleCircles charts).toEquiv
      _ = Cardinal.lift.{u} (Cardinal.mk (Fin k)) := by
        simpa only [Cardinal.lift_uzero] using Cardinal.mk_congr_lift e
      _ = k := Cardinal.lift_mk_fin k
