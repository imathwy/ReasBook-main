module

public import Topology_Munkres_2000.Book.Theorem_78_1.TriangleEdgeTopology

public section

universe u

namespace CurvedTriangle

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Theorem 78.1: the vertices of a planar curved-triangle model
affinely span the ambient plane. -/
theorem affineSpan_modelPoints_eq_top (triangle : CurvedTriangle X) :
    affineSpan ℝ (Set.range triangle.model.points) = ⊤ := by
  -- A two-simplex in the two-dimensional Euclidean model is full-dimensional.
  exact triangle.model.span_eq_top (by simp)

/-- Helper for Theorem 78.1: the vertices of a curved-triangle model, regarded
as the canonical affine basis of the ambient plane. -/
noncomputable def modelAffineBasis (triangle : CurvedTriangle X) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨triangle.model.points, triangle.model.independent,
    triangle.affineSpan_modelPoints_eq_top⟩

/-- Helper for Theorem 78.1: the canonical model affine basis evaluates to
the corresponding simplex vertex. -/
@[simp]
theorem modelAffineBasis_apply (triangle : CurvedTriangle X) (i : Fin 3) :
    triangle.modelAffineBasis i = triangle.model.points i := by
  -- Expose the affine-basis constructor before evaluating its point map.
  unfold modelAffineBasis
  rfl

/-- Helper for Theorem 78.1: the affine-basis coordinate opposite a selected
face vanishes exactly on the affine span of that face. -/
theorem mem_affineSpan_faceOpposite_iff_modelAffineBasis_coord_eq_zero
    (triangle : CurvedTriangle X) (i : Fin 3)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ affineSpan ℝ (Set.range (triangle.model.faceOpposite i).points) ↔
      (triangle.modelAffineBasis.coord i) x = 0 := by
  -- Expand `x` in the canonical affine basis and apply the simplex face
  -- criterion to its barycentric coordinates.
  let basis := triangle.modelAffineBasis
  have hsum : ∑ j, basis.coord j x = 1 := basis.sum_coord_apply_eq_one x
  have hexpand :
      Finset.univ.affineCombination ℝ triangle.model.points
          (fun j ↦ basis.coord j x) = x := by
    exact basis.affineCombination_coord_eq_self x
  change x ∈ affineSpan ℝ
      (Set.range (triangle.model.faceOpposite i).points) ↔
    basis.coord i x = 0
  constructor
  · intro hx
    apply (triangle.model.affineCombination_mem_affineSpan_faceOpposite_iff
      (i := i) hsum).mp
    rwa [hexpand]
  · intro hcoord
    have hcombination :=
      (triangle.model.affineCombination_mem_affineSpan_faceOpposite_iff
        (i := i) hsum).mpr hcoord
    rwa [hexpand] at hcombination

/-- Helper for Theorem 78.1: longitudinal and normal unit-interval
coordinates for a half-collar, excluding its collapsed normal endpoint. -/
abbrev ModelHalfCollarDomain :=
  {q : unitInterval × unitInterval // (q.2 : ℝ) < 1}

/-- Helper for Theorem 78.1: the affine half-collar joining a selected model
edge to the opposite vertex. -/
def modelHalfCollar (triangle : CurvedTriangle X) (i : Fin 3)
    (q : ModelHalfCollarDomain) : EuclideanSpace ℝ (Fin 2) :=
  AffineMap.lineMap (triangle.modelEdgeValue i q.1.1)
    (triangle.model.points i) (q.1.2 : ℝ)

/-- Helper for Theorem 78.1: the endpoint and height data defining the affine
half-collar vary continuously. -/
theorem continuous_modelHalfCollarParameters
    (triangle : CurvedTriangle X) (i : Fin 3) :
    Continuous (fun q : ModelHalfCollarDomain ↦
      (triangle.modelEdgeValue i q.1.1,
        (triangle.model.points i, (q.1.2 : ℝ)))) := by
  have hedge : Continuous (fun q : ModelHalfCollarDomain ↦
      triangle.modelEdgeValue i q.1.1) :=
    (triangle.continuous_modelEdgeValue i).comp
      (continuous_fst.comp continuous_subtype_val)
  have hheight : Continuous (fun q : ModelHalfCollarDomain ↦ (q.1.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  -- Package the two endpoints and scalar parameter in the order expected by
  -- the uncurried continuity theorem for `lineMap`.
  exact hedge.prodMk (continuous_const.prodMk hheight)

/-- Helper for Theorem 78.1: the model half-collar varies continuously in
both its longitudinal and normal coordinates. -/
theorem continuous_modelHalfCollar (triangle : CurvedTriangle X) (i : Fin 3) :
    Continuous (triangle.modelHalfCollar i) := by
  -- Feed the continuous edge value, fixed vertex, and normal coordinate into
  -- the jointly continuous affine line map.
  have hcontinuous := AffineMap.lineMap_continuous_uncurry.comp
    (triangle.continuous_modelHalfCollarParameters i)
  apply hcontinuous.congr
  intro q
  -- Compare the two spellings pointwise, avoiding a global definitional
  -- equality through the model-edge implementation.
  unfold modelHalfCollar
  rfl

/-- Helper for Theorem 78.1: every half-collar point remains in the closed
model triangle. -/
theorem modelHalfCollar_mem_closedInterior (triangle : CurvedTriangle X)
    (i : Fin 3) (q : ModelHalfCollarDomain) :
    triangle.modelHalfCollar i q ∈ triangle.model.closedInterior := by
  have hconvex : Convex ℝ triangle.model.closedInterior := by
    rw [← triangle.model.convexHull_eq_closedInterior]
    exact convex_convexHull ℝ (Set.range triangle.model.points)
  have hedge :
      triangle.modelEdgeValue i q.1.1 ∈ triangle.model.closedInterior :=
    triangle.modelEdgeValue_mem_region i q.1.1
  -- Convexity keeps the segment from the selected edge to the opposite vertex
  -- inside the model triangle.
  exact hconvex.lineMap_mem hedge (triangle.model.point_mem_closedInterior i)
    q.1.2.property

/-- Helper for Theorem 78.1: the opposite barycentric coordinate of a
half-collar point is exactly its normal height. -/
theorem modelAffineBasis_coord_modelHalfCollar (triangle : CurvedTriangle X)
    (i : Fin 3) (q : ModelHalfCollarDomain) :
    triangle.modelAffineBasis.coord i (triangle.modelHalfCollar i q) =
      (q.1.2 : ℝ) := by
  have hedgeSpan : triangle.modelEdgeValue i q.1.1 ∈
      affineSpan ℝ (Set.range (triangle.model.faceOpposite i).points) := by
    apply (triangle.model.faceOpposite i).closedInterior_subset_affineSpan
    rw [← triangle.modelEdge_def i, ← triangle.range_modelEdgePoint_val i]
    exact ⟨q.1.1, rfl⟩
  have hedgeCoord :
      triangle.modelAffineBasis.coord i (triangle.modelEdgeValue i q.1.1) = 0 :=
    (triangle.mem_affineSpan_faceOpposite_iff_modelAffineBasis_coord_eq_zero
      i _).mp hedgeSpan
  -- Affine coordinates preserve line maps; the edge coordinate is zero and
  -- the opposite vertex coordinate is one.
  unfold modelHalfCollar
  rw [AffineMap.apply_lineMap, hedgeCoord]
  rw [← triangle.modelAffineBasis_apply i, AffineBasis.coord_apply_eq]
  simp only [AffineMap.lineMap_apply_module, smul_eq_mul, mul_zero, zero_add,
    mul_one]

/-- Helper for Theorem 78.1: a half-collar point lies on the selected edge
exactly at normal height zero. -/
theorem modelHalfCollar_mem_modelEdge_iff (triangle : CurvedTriangle X)
    (i : Fin 3) (q : ModelHalfCollarDomain) :
    triangle.modelHalfCollar i q ∈ triangle.modelEdge i ↔
      (q.1.2 : ℝ) = 0 := by
  constructor
  · intro hq
    have hspan : triangle.modelHalfCollar i q ∈
        affineSpan ℝ (Set.range (triangle.model.faceOpposite i).points) := by
      apply (triangle.model.faceOpposite i).closedInterior_subset_affineSpan
      rwa [← triangle.modelEdge_def i]
    have hcoord :=
      (triangle.mem_affineSpan_faceOpposite_iff_modelAffineBasis_coord_eq_zero
        i _).mp hspan
    -- The coordinate computation identifies this vanishing coordinate with height.
    rwa [triangle.modelAffineBasis_coord_modelHalfCollar i q] at hcoord
  · intro hheight
    -- At height zero the line map is its edge endpoint.
    unfold modelHalfCollar
    rw [hheight, AffineMap.lineMap_apply_zero, ← triangle.range_modelEdgePoint_val i]
    exact ⟨q.1.1, rfl⟩

/-- Helper for Theorem 78.1: the model half-collar is injective before the
normal coordinate reaches the collapsed opposite vertex. -/
theorem injective_modelHalfCollar (triangle : CurvedTriangle X) (i : Fin 3) :
    Function.Injective (triangle.modelHalfCollar i) := by
  intro q r hqr
  have hheight : (q.1.2 : ℝ) = (r.1.2 : ℝ) := by
    have hcoord := congrArg (triangle.modelAffineBasis.coord i) hqr
    simpa only [triangle.modelAffineBasis_coord_modelHalfCollar] using hcoord
  have hedgeValue :
      triangle.modelEdgeValue i q.1.1 =
        triangle.modelEdgeValue i r.1.1 := by
    have hline := hqr
    unfold modelHalfCollar at hline
    rw [← hheight] at hline
    rw [← AffineMap.lineMap_apply_one_sub (triangle.model.points i)
      (triangle.modelEdgeValue i q.1.1),
      ← AffineMap.lineMap_apply_one_sub (triangle.model.points i)
        (triangle.modelEdgeValue i r.1.1)] at hline
    have hv := congrArg (fun z ↦ z -ᵥ triangle.model.points i) hline
    simp only [AffineMap.lineMap_vsub_left] at hv
    have hscale : (1 - (q.1.2 : ℝ)) ≠ 0 :=
      ne_of_gt (sub_pos.mpr q.2)
    have hvsub := smul_right_injective _ hscale hv
    exact vsub_left_cancel hvsub
  have hparameter : (q.1.1 : ℝ) = (r.1.1 : ℝ) := by
    exact congrArg Subtype.val
      (triangle.injective_modelEdgeValue i hedgeValue)
  -- Equality of the two scalar coordinates determines the collar-domain point.
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hparameter
  · exact Subtype.ext hheight

/-- Helper for Theorem 78.1: the open longitudinal-normal strip used to glue
two half-collars along their common seam. -/
abbrev OpenEdgeStrip :=
  {p : ℝ × ℝ // p.1 ∈ Set.Ioo 0 1 ∧ p.2 ∈ Set.Ioo (-1) 1}

/-- Helper for Theorem 78.1: the longitudinal coordinate of the open strip
lies in the closed unit interval. -/
theorem openEdgeStrip_longitudinal_mem_Icc (q : OpenEdgeStrip) :
    q.1.1 ∈ Set.Icc (0 : ℝ) 1 := by
  -- Forget strictness while retaining both endpoint inequalities.
  exact ⟨q.2.1.1.le, q.2.1.2.le⟩

/-- Helper for Theorem 78.1: the nonnegative part of the normal coordinate
lies in the closed unit interval. -/
theorem openEdgeStrip_positiveHeight_mem_Icc (q : OpenEdgeStrip) :
    max q.1.2 0 ∈ Set.Icc (0 : ℝ) 1 := by
  -- The strip bounds its normal coordinate strictly above by one.
  exact ⟨le_max_right _ _, (max_lt_iff.mpr ⟨q.2.2.2, zero_lt_one⟩).le⟩

/-- Helper for Theorem 78.1: the nonnegative part of the normal coordinate
stays strictly below the collapsed height one. -/
theorem openEdgeStrip_positiveHeight_lt_one (q : OpenEdgeStrip) :
    max q.1.2 0 < (1 : ℝ) := by
  -- Both entries of the maximum are strictly below one.
  exact max_lt q.2.2.2 zero_lt_one

/-- Helper for Theorem 78.1: the reflected negative part of the normal
coordinate lies in the closed unit interval. -/
theorem openEdgeStrip_negativeHeight_mem_Icc (q : OpenEdgeStrip) :
    max (-q.1.2) 0 ∈ Set.Icc (0 : ℝ) 1 := by
  have hneg : -q.1.2 < (1 : ℝ) := by
    linarith [q.2.2.1]
  -- Reflect the lower strip bound and retain the nonnegative part.
  exact ⟨le_max_right _ _, (max_lt hneg zero_lt_one).le⟩

/-- Helper for Theorem 78.1: the reflected negative normal coordinate stays
strictly below the collapsed height one. -/
theorem openEdgeStrip_negativeHeight_lt_one (q : OpenEdgeStrip) :
    max (-q.1.2) 0 < (1 : ℝ) := by
  -- Reflection turns the lower strip bound into the required upper bound.
  apply max_lt
  · linarith [q.2.2.1]
  · exact zero_lt_one

/-- Helper for Theorem 78.1: package the strip's longitudinal coordinate as
a unit-interval parameter. -/
def openEdgeStripLongitudinal (q : OpenEdgeStrip) : unitInterval :=
  ⟨q.1.1, openEdgeStrip_longitudinal_mem_Icc q⟩

/-- Helper for Theorem 78.1: orient a longitudinal strip parameter according
to the affine compatibility of the second edge. -/
def orientedOpenEdgeStripLongitudinal (reverse : Bool) (q : OpenEdgeStrip) :
    unitInterval :=
  if reverse then unitInterval.symm (openEdgeStripLongitudinal q)
  else openEdgeStripLongitudinal q

/-- Helper for Theorem 78.1: turn the upper half of the strip into coordinates
for the first model half-collar. -/
def positiveModelHalfCollarCoordinate (q : OpenEdgeStrip) :
    ModelHalfCollarDomain :=
  ⟨(openEdgeStripLongitudinal q,
      ⟨max q.1.2 0, openEdgeStrip_positiveHeight_mem_Icc q⟩),
    openEdgeStrip_positiveHeight_lt_one q⟩

/-- Helper for Theorem 78.1: turn the lower half of the strip into reflected,
compatibly oriented coordinates for the second model half-collar. -/
def negativeModelHalfCollarCoordinate (reverse : Bool) (q : OpenEdgeStrip) :
    ModelHalfCollarDomain :=
  ⟨(orientedOpenEdgeStripLongitudinal reverse q,
      ⟨max (-q.1.2) 0, openEdgeStrip_negativeHeight_mem_Icc q⟩),
    openEdgeStrip_negativeHeight_lt_one q⟩

/-- Helper for Theorem 78.1: upper half-collar coordinates depend
continuously on the open-strip point. -/
theorem continuous_positiveModelHalfCollarCoordinate :
    Continuous positiveModelHalfCollarCoordinate := by
  -- All fields are assembled from coordinate projections and `max`.
  unfold positiveModelHalfCollarCoordinate openEdgeStripLongitudinal
  fun_prop

/-- Helper for Theorem 78.1: lower half-collar coordinates depend
continuously on the open-strip point for either edge orientation. -/
theorem continuous_negativeModelHalfCollarCoordinate (reverse : Bool) :
    Continuous (negativeModelHalfCollarCoordinate reverse) := by
  -- Split the fixed orientation once; both branches use continuous projections,
  -- reflection, and `max`.
  cases reverse
  · unfold negativeModelHalfCollarCoordinate
      orientedOpenEdgeStripLongitudinal openEdgeStripLongitudinal
    simp only [Bool.false_eq_true, if_false]
    fun_prop
  · unfold negativeModelHalfCollarCoordinate
      orientedOpenEdgeStripLongitudinal openEdgeStripLongitudinal
    simp only [if_true]
    fun_prop

/-- Helper for Theorem 78.1: the upper half of the glued strip mapped through
the first curved-triangle chart. -/
def positiveCollarMap (triangle : CurvedTriangle X) (i : Fin 3)
    (q : OpenEdgeStrip) : X :=
  (triangle.chart
    ⟨triangle.modelHalfCollar i (positiveModelHalfCollarCoordinate q),
      triangle.modelHalfCollar_mem_closedInterior i
        (positiveModelHalfCollarCoordinate q)⟩ : triangle.carrier)

/-- Helper for Theorem 78.1: the reflected lower half of the glued strip
mapped through the second curved-triangle chart. -/
def negativeCollarMap (triangle : CurvedTriangle X) (i : Fin 3)
    (reverse : Bool) (q : OpenEdgeStrip) : X :=
  (triangle.chart
    ⟨triangle.modelHalfCollar i
        (negativeModelHalfCollarCoordinate reverse q),
      triangle.modelHalfCollar_mem_closedInterior i
        (negativeModelHalfCollarCoordinate reverse q)⟩ : triangle.carrier)

/-- Helper for Theorem 78.1: the upper curved half-collar map is continuous. -/
theorem continuous_positiveCollarMap (triangle : CurvedTriangle X) (i : Fin 3) :
    Continuous (triangle.positiveCollarMap i) := by
  have hmodel : Continuous (fun q : OpenEdgeStrip ↦
      ⟨triangle.modelHalfCollar i (positiveModelHalfCollarCoordinate q),
        triangle.modelHalfCollar_mem_closedInterior i
          (positiveModelHalfCollarCoordinate q)⟩ :
        OpenEdgeStrip → triangle.model.closedInterior) := by
    exact (triangle.continuous_modelHalfCollar i).comp
      continuous_positiveModelHalfCollarCoordinate |>.subtype_mk _
  -- Compose the continuous model collar with the triangle chart and inclusion.
  exact continuous_subtype_val.comp (triangle.chart.continuous.comp hmodel)

/-- Helper for Theorem 78.1: the lower curved half-collar map is continuous
for either compatible edge orientation. -/
theorem continuous_negativeCollarMap (triangle : CurvedTriangle X) (i : Fin 3)
    (reverse : Bool) :
    Continuous (triangle.negativeCollarMap i reverse) := by
  have hmodel : Continuous (fun q : OpenEdgeStrip ↦
      ⟨triangle.modelHalfCollar i (negativeModelHalfCollarCoordinate reverse q),
        triangle.modelHalfCollar_mem_closedInterior i
          (negativeModelHalfCollarCoordinate reverse q)⟩ :
        OpenEdgeStrip → triangle.model.closedInterior) := by
    exact (triangle.continuous_modelHalfCollar i).comp
      (continuous_negativeModelHalfCollarCoordinate reverse) |>.subtype_mk _
  -- Compose the reflected model collar with the second triangle chart.
  exact continuous_subtype_val.comp (triangle.chart.continuous.comp hmodel)

/-- Helper for Theorem 78.1: compatible upper and lower curved half-collars
agree along their common normal-height-zero seam. -/
theorem positiveCollarMap_eq_negativeCollarMap_of_height_eq_zero
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool)
    (hcompatible : ∀ t : unitInterval,
      (first.chart (first.modelEdgePoint i t) : X) =
        (second.chart (second.modelEdgePoint j
          (if reverse then unitInterval.symm t else t)) : X))
    (q : OpenEdgeStrip) (hq : q.1.2 = 0) :
    first.positiveCollarMap i q = second.negativeCollarMap j reverse q := by
  -- At the seam both half-collars reduce to their edge parametrizations, so
  -- the stored compatibility equation applies directly.
  unfold positiveCollarMap negativeCollarMap modelHalfCollar
    positiveModelHalfCollarCoordinate negativeModelHalfCollarCoordinate
    orientedOpenEdgeStripLongitudinal
  simp only [hq, max_self, neg_zero, AffineMap.lineMap_apply_zero]
  exact hcompatible (openEdgeStripLongitudinal q)

/-- Helper for Theorem 78.1: after applying a curved-triangle chart, a model
half-collar point lies on the selected curved edge exactly at height zero. -/
theorem chart_modelHalfCollar_mem_edge_iff (triangle : CurvedTriangle X)
    (i : Fin 3) (q : ModelHalfCollarDomain) :
    (triangle.chart
        ⟨triangle.modelHalfCollar i q,
          triangle.modelHalfCollar_mem_closedInterior i q⟩ : X) ∈
        triangle.edge i ↔
      (q.1.2 : ℝ) = 0 := by
  rw [triangle.edge_eq_chart_image_modelEdge i]
  constructor
  · rintro ⟨y, hyEdge, hy⟩
    have hyModel : y =
        ⟨triangle.modelHalfCollar i q,
          triangle.modelHalfCollar_mem_closedInterior i q⟩ := by
      apply triangle.chart.injective
      exact Subtype.ext hy
    rw [hyModel] at hyEdge
    exact (triangle.modelHalfCollar_mem_modelEdge_iff i q).mp hyEdge
  · intro hheight
    refine ⟨⟨triangle.modelHalfCollar i q,
      triangle.modelHalfCollar_mem_closedInterior i q⟩, ?_, rfl⟩
    exact (triangle.modelHalfCollar_mem_modelEdge_iff i q).mpr hheight

/-- Helper for Theorem 78.1: the first curved half-collar is injective on the
closed upper half of the open strip. -/
theorem injOn_positiveCollarMap (triangle : CurvedTriangle X) (i : Fin 3) :
    Set.InjOn (triangle.positiveCollarMap i) {q | 0 ≤ q.1.2} := by
  intro q hq r hr hmap
  change 0 ≤ q.1.2 at hq
  change 0 ≤ r.1.2 at hr
  have hcoordinates :
      positiveModelHalfCollarCoordinate q =
        positiveModelHalfCollarCoordinate r := by
    apply triangle.injective_modelHalfCollar i
    exact congrArg Subtype.val
      (triangle.chart.injective (Subtype.ext hmap))
  have hlongitudinal : q.1.1 = r.1.1 := by
    exact congrArg
      (fun c : ModelHalfCollarDomain ↦ ((c.1.1 : unitInterval) : ℝ))
      hcoordinates
  have hnormalMax : max q.1.2 0 = max r.1.2 0 := by
    exact congrArg
      (fun c : ModelHalfCollarDomain ↦ ((c.1.2 : unitInterval) : ℝ))
      hcoordinates
  have hnormal : q.1.2 = r.1.2 := by
    simpa only [max_eq_left hq, max_eq_left hr] using hnormalMax
  -- The two real coordinates determine a point of the product strip.
  apply Subtype.ext
  exact Prod.ext hlongitudinal hnormal

/-- Helper for Theorem 78.1: the second curved half-collar is injective on the
closed lower half of the open strip. -/
theorem injOn_negativeCollarMap (triangle : CurvedTriangle X) (i : Fin 3)
    (reverse : Bool) :
    Set.InjOn (triangle.negativeCollarMap i reverse) {q | q.1.2 ≤ 0} := by
  intro q hq r hr hmap
  change q.1.2 ≤ 0 at hq
  change r.1.2 ≤ 0 at hr
  have hcoordinates :
      negativeModelHalfCollarCoordinate reverse q =
        negativeModelHalfCollarCoordinate reverse r := by
    apply triangle.injective_modelHalfCollar i
    exact congrArg Subtype.val
      (triangle.chart.injective (Subtype.ext hmap))
  have horiented :
      orientedOpenEdgeStripLongitudinal reverse q =
        orientedOpenEdgeStripLongitudinal reverse r := by
    exact congrArg (fun c : ModelHalfCollarDomain ↦ c.1.1) hcoordinates
  have hlongitudinal : q.1.1 = r.1.1 := by
    cases reverse
    · simpa only [orientedOpenEdgeStripLongitudinal, Bool.false_eq_true,
        if_false, openEdgeStripLongitudinal] using congrArg Subtype.val horiented
    · have hsymmetric := unitInterval.symm_bijective.injective horiented
      simpa only [orientedOpenEdgeStripLongitudinal, if_true,
        openEdgeStripLongitudinal] using congrArg Subtype.val hsymmetric
  have hnormalMax : max (-q.1.2) 0 = max (-r.1.2) 0 := by
    exact congrArg
      (fun c : ModelHalfCollarDomain ↦ ((c.1.2 : unitInterval) : ℝ))
      hcoordinates
  have hnormal : q.1.2 = r.1.2 := by
    have hneg : -q.1.2 = -r.1.2 := by
      simpa only [max_eq_left (neg_nonneg.mpr hq),
        max_eq_left (neg_nonneg.mpr hr)] using hnormalMax
    linarith
  -- The reflected normal coordinate and oriented longitudinal coordinate
  -- recover the original lower-strip point.
  apply Subtype.ext
  exact Prod.ext hlongitudinal hnormal

/-- Helper for Theorem 78.1: every upper half-collar value lies in the first
curved triangle's carrier. -/
theorem positiveCollarMap_mem_carrier (triangle : CurvedTriangle X) (i : Fin 3)
    (q : OpenEdgeStrip) :
    triangle.positiveCollarMap i q ∈ triangle.carrier := by
  -- The chart codomain subtype records carrier membership.
  exact (triangle.chart
    ⟨triangle.modelHalfCollar i (positiveModelHalfCollarCoordinate q),
      triangle.modelHalfCollar_mem_closedInterior i
        (positiveModelHalfCollarCoordinate q)⟩).property

/-- Helper for Theorem 78.1: every lower half-collar value lies in the second
curved triangle's carrier. -/
theorem negativeCollarMap_mem_carrier (triangle : CurvedTriangle X) (i : Fin 3)
    (reverse : Bool) (q : OpenEdgeStrip) :
    triangle.negativeCollarMap i reverse q ∈ triangle.carrier := by
  -- The chart codomain subtype records carrier membership.
  exact (triangle.chart
    ⟨triangle.modelHalfCollar i (negativeModelHalfCollarCoordinate reverse q),
      triangle.modelHalfCollar_mem_closedInterior i
        (negativeModelHalfCollarCoordinate reverse q)⟩).property

/-- Helper for Theorem 78.1: an upper-page value and a strictly lower-page
value cannot agree when the two triangle carriers meet exactly in their
selected edges. -/
theorem positiveCollarMap_ne_negativeCollarMap_of_negative_height
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool)
    (hintersectionFirst : first.carrier ∩ second.carrier = first.edge i)
    (hintersectionSecond : first.carrier ∩ second.carrier = second.edge j)
    (q r : OpenEdgeStrip) (hr : r.1.2 < 0) :
    first.positiveCollarMap i q ≠ second.negativeCollarMap j reverse r := by
  intro hmaps
  have hfirst : first.positiveCollarMap i q ∈ first.carrier :=
    first.positiveCollarMap_mem_carrier i q
  have hsecond : first.positiveCollarMap i q ∈ second.carrier := by
    rw [hmaps]
    exact second.negativeCollarMap_mem_carrier j reverse r
  have hintersection :
      first.positiveCollarMap i q ∈ first.carrier ∩ second.carrier :=
    ⟨hfirst, hsecond⟩
  have hupperEdge : first.positiveCollarMap i q ∈ first.edge i := by
    rwa [← hintersectionFirst]
  have hupperHeight : max q.1.2 0 = 0 := by
    exact (first.chart_modelHalfCollar_mem_edge_iff i
      (positiveModelHalfCollarCoordinate q)).mp hupperEdge
  have hlowerEdge : second.negativeCollarMap j reverse r ∈ second.edge j := by
    rw [← hintersectionSecond, ← hmaps]
    exact hintersection
  have hlowerHeight : max (-r.1.2) 0 = 0 := by
    exact (second.chart_modelHalfCollar_mem_edge_iff j
      (negativeModelHalfCollarCoordinate reverse r)).mp hlowerEdge
  -- A strictly negative strip height has strictly positive reflected height,
  -- contradicting membership in the common edge.
  have hpositive : 0 < max (-r.1.2) 0 := by
    exact lt_max_of_lt_left (neg_pos.mpr hr)
  linarith [hupperHeight]

/-- Helper for Theorem 78.1: glue the compatible upper and lower curved
half-collars by selecting the page according to the normal-coordinate sign. -/
def twoPageCollarMap (first second : CurvedTriangle X) (i j : Fin 3)
    (reverse : Bool) (q : OpenEdgeStrip) : X :=
  if 0 ≤ q.1.2 then first.positiveCollarMap i q
  else second.negativeCollarMap j reverse q

/-- Helper for Theorem 78.1: the two-page collar map is continuous whenever
the selected curved edges have compatible affine parametrizations. -/
theorem continuous_twoPageCollarMap
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool)
    (hcompatible : ∀ t : unitInterval,
      (first.chart (first.modelEdgePoint i t) : X) =
        (second.chart (second.modelEdgePoint j
          (if reverse then unitInterval.symm t else t)) : X)) :
    Continuous (first.twoPageCollarMap second i j reverse) := by
  -- The two continuous branches agree precisely when the normal coordinate
  -- equals zero, by affine edge compatibility.
  apply (first.continuous_positiveCollarMap i).if_le
    (second.continuous_negativeCollarMap j reverse) continuous_const
    (continuous_snd.comp continuous_subtype_val)
  intro q hq
  exact first.positiveCollarMap_eq_negativeCollarMap_of_height_eq_zero
    second i j reverse hcompatible q hq.symm

/-- Helper for Theorem 78.1: the glued two-page collar is injective when the
two carrier intersection is exactly the selected edge on both pages. -/
theorem injective_twoPageCollarMap
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool)
    (hintersectionFirst : first.carrier ∩ second.carrier = first.edge i)
    (hintersectionSecond : first.carrier ∩ second.carrier = second.edge j) :
    Function.Injective (first.twoPageCollarMap second i j reverse) := by
  intro q r hmaps
  by_cases hq : 0 ≤ q.1.2
  · by_cases hr : 0 ≤ r.1.2
    · apply first.injOn_positiveCollarMap i hq hr
      simpa only [twoPageCollarMap, if_pos hq, if_pos hr] using hmaps
    · have hrneg : r.1.2 < 0 := lt_of_not_ge hr
      have hcross : first.positiveCollarMap i q =
          second.negativeCollarMap j reverse r := by
        simpa only [twoPageCollarMap, if_pos hq, if_neg hr] using hmaps
      exact False.elim
        (first.positiveCollarMap_ne_negativeCollarMap_of_negative_height
          second i j reverse hintersectionFirst hintersectionSecond q r hrneg hcross)
  · by_cases hr : 0 ≤ r.1.2
    · have hqneg : q.1.2 < 0 := lt_of_not_ge hq
      have hcross : first.positiveCollarMap i r =
          second.negativeCollarMap j reverse q := by
        simpa only [twoPageCollarMap, if_neg hq, if_pos hr] using hmaps.symm
      exact False.elim
        (first.positiveCollarMap_ne_negativeCollarMap_of_negative_height
          second i j reverse hintersectionFirst hintersectionSecond r q hqneg hcross)
    · apply second.injOn_negativeCollarMap j reverse
        (le_of_lt (lt_of_not_ge hq)) (le_of_lt (lt_of_not_ge hr))
      simpa only [twoPageCollarMap, if_neg hq, if_neg hr] using hmaps

/-- Helper for Theorem 78.1: the glued collar takes values in the union of
the two curved-triangle carriers. -/
theorem range_twoPageCollarMap_subset_union
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool) :
    Set.range (first.twoPageCollarMap second i j reverse) ⊆
      first.carrier ∪ second.carrier := by
  rintro _ ⟨q, rfl⟩
  by_cases hq : 0 ≤ q.1.2
  · rw [twoPageCollarMap, if_pos hq]
    exact Or.inl (first.positiveCollarMap_mem_carrier i q)
  · rw [twoPageCollarMap, if_neg hq]
    exact Or.inr (second.negativeCollarMap_mem_carrier j reverse q)

/-- Helper for Theorem 78.1: zero lies in the open normal interval used by
the two-page collar. -/
theorem zero_mem_openEdgeStrip_normal : (0 : ℝ) ∈ Set.Ioo (-1) 1 := by
  -- Both strict inequalities are numerical.
  norm_num

/-- Helper for Theorem 78.1: the point on the collar seam with prescribed
strict longitudinal parameter. -/
def openEdgeStripSeamPoint (t : unitInterval) (ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    OpenEdgeStrip :=
  ⟨((t : ℝ), 0), ht, zero_mem_openEdgeStrip_normal⟩

/-- Helper for Theorem 78.1: the glued two-page collar sends its seam point
to the first curved edge at the prescribed affine parameter. -/
theorem twoPageCollarMap_openEdgeStripSeamPoint
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool)
    (t : unitInterval) (ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    first.twoPageCollarMap second i j reverse
        (openEdgeStripSeamPoint t ht) =
      (first.chart (first.modelEdgePoint i t) : X) := by
  -- The seam selects the upper page and its height-zero line map is the
  -- original model-edge point.
  unfold twoPageCollarMap positiveCollarMap modelHalfCollar
    positiveModelHalfCollarCoordinate openEdgeStripSeamPoint
    openEdgeStripLongitudinal
  simp only [le_refl, if_pos, max_self, AffineMap.lineMap_apply_zero]
  rfl

/-- Helper for Theorem 78.1: standard product coordinates on the Euclidean
plane, obtained by forgetting the `PiLp` wrapper and evaluating `Fin 2`. -/
noncomputable def planarCoordinateHomeomorph :
    EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
    (Homeomorph.finTwoArrow (X := ℝ))

/-- Helper for Theorem 78.1: the open Euclidean strip obtained by expressing
longitudinal-normal collar coordinates in the standard `Fin 2` plane. -/
def planarOpenEdgeStrip : Set (EuclideanSpace ℝ (Fin 2)) :=
  planarCoordinateHomeomorph ⁻¹'
    (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1)

/-- Helper for Theorem 78.1: the planar collar strip is open. -/
theorem isOpen_planarOpenEdgeStrip : IsOpen planarOpenEdgeStrip := by
  -- Pull back the product of the two open coordinate intervals through the
  -- standard finite-product homeomorphism.
  unfold planarOpenEdgeStrip
  exact (isOpen_Ioo.prod isOpen_Ioo).preimage
    planarCoordinateHomeomorph.continuous

/-- Helper for Theorem 78.1: identify the planar open strip with its explicit
longitudinal-normal product-coordinate subtype. -/
def planarOpenEdgeStripHomeomorph : planarOpenEdgeStrip ≃ₜ OpenEdgeStrip :=
  planarCoordinateHomeomorph.subtype (fun _ ↦ Iff.rfl)

/-- Helper for Theorem 78.1: the seam point transported into the standard
Euclidean plane. -/
def planarOpenEdgeStripSeamPoint (t : unitInterval)
    (ht : (t : ℝ) ∈ Set.Ioo 0 1) : planarOpenEdgeStrip :=
  planarOpenEdgeStripHomeomorph.symm (openEdgeStripSeamPoint t ht)

/-- Helper for Theorem 78.1: the glued collar written on an open subset of the
standard Euclidean plane. -/
def planarTwoPageCollarMap (first second : CurvedTriangle X) (i j : Fin 3)
    (reverse : Bool) (q : planarOpenEdgeStrip) : X :=
  first.twoPageCollarMap second i j reverse (planarOpenEdgeStripHomeomorph q)

/-- Helper for Theorem 78.1: the planar-coordinate two-page collar is
continuous. -/
theorem continuous_planarTwoPageCollarMap
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool)
    (hcompatible : ∀ t : unitInterval,
      (first.chart (first.modelEdgePoint i t) : X) =
        (second.chart (second.modelEdgePoint j
          (if reverse then unitInterval.symm t else t)) : X)) :
    Continuous (first.planarTwoPageCollarMap second i j reverse) := by
  -- Precompose the continuous glued strip map with the strip homeomorphism.
  exact (first.continuous_twoPageCollarMap second i j reverse hcompatible).comp
    planarOpenEdgeStripHomeomorph.continuous

/-- Helper for Theorem 78.1: the planar-coordinate two-page collar is
injective under the exact shared-edge intersection hypotheses. -/
theorem injective_planarTwoPageCollarMap
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool)
    (hintersectionFirst : first.carrier ∩ second.carrier = first.edge i)
    (hintersectionSecond : first.carrier ∩ second.carrier = second.edge j) :
    Function.Injective (first.planarTwoPageCollarMap second i j reverse) := by
  -- Both the coordinate homeomorphism and the glued collar are injective.
  exact (first.injective_twoPageCollarMap second i j reverse
    hintersectionFirst hintersectionSecond).comp
      planarOpenEdgeStripHomeomorph.injective

/-- Helper for Theorem 78.1: the planar-coordinate collar remains inside the
union of the two selected curved triangles. -/
theorem range_planarTwoPageCollarMap_subset_union
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool) :
    Set.range (first.planarTwoPageCollarMap second i j reverse) ⊆
      first.carrier ∪ second.carrier := by
  rintro _ ⟨q, rfl⟩
  exact first.range_twoPageCollarMap_subset_union second i j reverse
    ⟨planarOpenEdgeStripHomeomorph q, rfl⟩

/-- Helper for Theorem 78.1: the planar-coordinate collar sends the chosen
seam point to the prescribed point on the first curved edge. -/
theorem planarTwoPageCollarMap_seamPoint
    (first second : CurvedTriangle X) (i j : Fin 3) (reverse : Bool)
    (t : unitInterval) (ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    first.planarTwoPageCollarMap second i j reverse
        (planarOpenEdgeStripSeamPoint t ht) =
      (first.chart (first.modelEdgePoint i t) : X) := by
  -- Cancel the strip homeomorphism and apply the product-coordinate seam rule.
  unfold planarTwoPageCollarMap planarOpenEdgeStripSeamPoint
  rw [planarOpenEdgeStripHomeomorph.apply_symm_apply]
  exact first.twoPageCollarMap_openEdgeStripSeamPoint second i j reverse t ht

/-- Helper for Theorem 78.1: two curved triangles meeting compatibly in one
selected edge supply an injective continuous planar patch through every
strictly interior point of that edge. -/
theorem existsPlanarEmbeddingAtOfCompatibleSharedEdge
    (first second : CurvedTriangle X) (i j : Fin 3)
    (hintersectionFirst : first.carrier ∩ second.carrier = first.edge i)
    (hintersectionSecond : first.carrier ∩ second.carrier = second.edge j)
    (hcompatible : first.EdgesCompatible second i j)
    (t : unitInterval) (ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      ∃ p : U, ∃ f : U → X,
        Continuous f ∧ Function.Injective f ∧
          f p = (first.chart (first.modelEdgePoint i t) : X) ∧
          Set.range f ⊆ first.carrier ∪ second.carrier := by
  obtain ⟨reverse, hreverse⟩ :=
    (first.edgesCompatible_iff second i j).mp hcompatible
  -- Use the explicit planar strip, its chosen seam point, and the transported
  -- two-page collar map supplied by the preceding interface.
  refine ⟨planarOpenEdgeStrip, isOpen_planarOpenEdgeStrip,
    planarOpenEdgeStripSeamPoint t ht,
    first.planarTwoPageCollarMap second i j reverse, ?_, ?_, ?_, ?_⟩
  · exact first.continuous_planarTwoPageCollarMap second i j reverse hreverse
  · exact first.injective_planarTwoPageCollarMap second i j reverse
      hintersectionFirst hintersectionSecond
  · exact first.planarTwoPageCollarMap_seamPoint second i j reverse t ht
  · exact first.range_planarTwoPageCollarMap_subset_union second i j reverse

end

end CurvedTriangle
