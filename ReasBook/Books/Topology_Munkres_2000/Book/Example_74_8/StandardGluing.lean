module

public import Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Example_74_8.BoundaryGluing
public import Topology_Munkres_2000.Book.Example_74_8.ProjectiveModel

public section

open Set

namespace ProjectivePlaneTorus

noncomputable section

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Helper for Example 74.8: the quotient-model projective chart restricted to the open unit
disc. -/
private noncomputable def projectiveDiscChart :
    OpenPartialHomeomorph Plane RealProjectivePlane :=
  (projectiveModelEmbedding_isOpenEmbedding.toOpenPartialHomeomorph
    projectiveModelEmbedding).restrOpen (Metric.ball 0 1) Metric.isOpen_ball

/-- Helper for Example 74.8: the quotient-model projective chart has the open unit disc as its
source. -/
private theorem projectiveDiscChart_source :
    projectiveDiscChart.source = Metric.ball (0 : Plane) 1 := by
  -- The open embedding has full source before restriction to the unit ball.
  simp only [projectiveDiscChart, OpenPartialHomeomorph.restrOpen_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, univ_inter]

/-- Helper for Example 74.8: the projective chart computes by the canonical quotient-model open
embedding. -/
private theorem projectiveDiscChart_apply (point : Plane) :
    projectiveDiscChart point = projectiveModelEmbedding point := by
  -- Restriction changes only the source set, not the underlying map.
  rfl

/-- Helper for Example 74.8: the scale used by the torus model is nonzero. -/
theorem quarterScale_ne_zero : (1 / 4 : ℝ) ≠ 0 := by
  -- The positive denominator makes the coordinate scale nonzero.
  norm_num

/-- Helper for Example 74.8: scaled Euclidean coordinates identify the model plane with a
Cartesian pair of real coordinates. -/
noncomputable def torusModelCoordinates :
    EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  (Homeomorph.smulOfNeZero (1 / 4 : ℝ) quarterScale_ne_zero).trans
    ((EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
      (Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ))

/-- Helper for Example 74.8: the scaled torus coordinates are one quarter of the two
Euclidean coordinates. -/
lemma torusModelCoordinates_apply (point : EuclideanSpace ℝ (Fin 2)) :
    torusModelCoordinates point =
      ((1 / 4 : ℝ) * point 0, (1 / 4 : ℝ) * point 1) := by
  -- Compute the scalar homeomorphism and the two finite coordinates at their owner.
  simp [torusModelCoordinates, Homeomorph.finTwoArrow]

/-- Helper for Example 74.8: the global quotient presentation of the torus in the coordinates
used by the deleted-disc chart. -/
noncomputable def torusModelMap :
    EuclideanSpace ℝ (Fin 2) → UnitAddCircle × UnitAddCircle :=
  Prod.map (fun x : ℝ ↦ (x : UnitAddCircle))
      (fun x : ℝ ↦ (x : UnitAddCircle)) ∘
    torusModelCoordinates

/-- Helper for Example 74.8: the canonical torus model coerces the two scaled real
coordinates to the two additive circles. -/
lemma torusModelMap_apply (point : EuclideanSpace ℝ (Fin 2)) :
    torusModelMap point =
      (((torusModelCoordinates point).1 : UnitAddCircle),
        ((torusModelCoordinates point).2 : UnitAddCircle)) := by
  -- This records the product quotient computation without exposing the chart implementation
  -- across the module boundary.
  rfl

/-- Helper for Example 74.8: the global scaled-coordinate map onto the torus is an open
quotient map. -/
lemma torusModelMap_isOpenQuotientMap :
    IsOpenQuotientMap torusModelMap := by
  -- Each real-to-circle quotient is open; products and precomposition by the coordinate
  -- homeomorphism preserve the complete quotient-map interface.
  have hcircle : IsOpenQuotientMap
      (fun x : ℝ ↦ (x : UnitAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  exact (hcircle.prodMap hcircle).comp torusModelCoordinates.isOpenQuotientMap

/-- Helper for Example 74.8: the global scaled-coordinate map is in particular a quotient
map. -/
lemma torusModelMap_isQuotientMap :
    Topology.IsQuotientMap torusModelMap := by
  -- Forget openness from the stronger owner-level presentation.
  exact torusModelMap_isOpenQuotientMap.isQuotientMap

/-- Helper for Example 74.8: the standard real coordinate chart on the additive unit circle. -/
private def circleCoordinateChart : OpenPartialHomeomorph ℝ UnitAddCircle :=
  AddCircle.openPartialHomeomorphCoe (1 : ℝ) (-1 / 2)

/-- Helper for Example 74.8: the product of the two standard circle coordinate charts. -/
private def torusCoordinateChart :
    OpenPartialHomeomorph (ℝ × ℝ) (UnitAddCircle × UnitAddCircle) :=
  circleCoordinateChart.prod circleCoordinateChart

/-- Helper for Example 74.8: the scaled product chart before restricting its source to the
unit disc. -/
private def torusAmbientChart :
    OpenPartialHomeomorph Plane (UnitAddCircle × UnitAddCircle) :=
  torusModelCoordinates.toOpenPartialHomeomorph.trans torusCoordinateChart

/-- A standard open-disc chart in the torus, centered at `(0, 0)`. -/
def torusDiscChart :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (UnitAddCircle × UnitAddCircle) :=
  torusAmbientChart.restrOpen (Metric.ball 0 1) Metric.isOpen_ball

/-- Helper for Example 74.8: the restricted torus chart has the open unit disc as its source. -/
private theorem torusDiscChart_source :
    torusDiscChart.source = Metric.ball (0 : Plane) 1 := by
  rw [torusDiscChart, OpenPartialHomeomorph.restrOpen_source, inter_eq_right]
  intro point hpoint
  have hnorm : ‖point‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hpoint
  have hcoordinate (i : Fin 2) : |point i| < 1 := by
    have hcoordinateNorm : ‖point i‖ ≤ ‖point‖ := PiLp.norm_apply_le point i
    calc
      |point i| = ‖point i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖point‖ := hcoordinateNorm
      _ < 1 := hnorm
  have hcoordinateZero := hcoordinate 0
  have hcoordinateOne := hcoordinate 1
  rw [abs_lt] at hcoordinateZero hcoordinateOne
  simp only [torusAmbientChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, univ_inter, mem_preimage,
    torusCoordinateChart, OpenPartialHomeomorph.prod_source, mem_prod,
    circleCoordinateChart, AddCircle.openPartialHomeomorphCoe_source, mem_Ioo,
    torusModelCoordinates, one_div]
  constructor
  · constructor
    · norm_num at ⊢
      nlinarith
    · norm_num at ⊢
      nlinarith
  · constructor
    · norm_num at ⊢
      nlinarith
    · norm_num at ⊢
      nlinarith

/-- Helper for Example 74.8: a radius-`1 / 2` boundary point cannot lie in the image of the
open radius-`1 / 2` disc under a unit-disc chart. -/
private theorem chartBoundary_not_mem_deletedDisc {Z : Type*} [TopologicalSpace Z]
    (chart : OpenPartialHomeomorph Plane Z)
    (hsource : chart.source = Metric.ball (0 : Plane) 1)
    (point : DiscBoundaryGluing.BoundaryCircle) :
    chart point ∉ chart '' Metric.ball 0 (1 / 2 : ℝ) := by
  rintro ⟨interiorPoint, hinteriorPoint, hsameImage⟩
  have hpointSource : (point : Plane) ∈ chart.source := by
    rw [hsource]
    exact Metric.sphere_subset_ball (by norm_num) point.property
  have hinteriorSource : interiorPoint ∈ chart.source := by
    rw [hsource]
    exact Metric.ball_subset_ball (by norm_num) hinteriorPoint
  have hsamePoint : interiorPoint = (point : Plane) :=
    chart.injOn hinteriorSource hpointSource hsameImage
  subst interiorPoint
  have hboundary := point.property
  rw [Metric.mem_ball] at hinteriorPoint
  rw [Metric.mem_sphere] at hboundary
  linarith

/-- Helper for Example 74.8: the restriction of a unit-disc chart to its radius-`1 / 2`
boundary circle is an embedding into the deleted-disc complement. -/
private theorem chartBoundaryEmbedding {Z : Type*} [TopologicalSpace Z]
    (chart : OpenPartialHomeomorph Plane Z)
    (hsource : chart.source = Metric.ball (0 : Plane) 1) :
    Topology.IsEmbedding
      (Set.codRestrict
        (fun point : DiscBoundaryGluing.BoundaryCircle ↦ chart point)
        {z : Z | z ∉ chart '' Metric.ball 0 (1 / 2 : ℝ)}
        (chartBoundary_not_mem_deletedDisc chart hsource)) := by
  have hsphere : Metric.sphere (0 : Plane) (1 / 2 : ℝ) ⊆ chart.source := by
    rw [hsource]
    exact Metric.sphere_subset_ball (by norm_num)
  have hambient : Topology.IsEmbedding
      (fun point : DiscBoundaryGluing.BoundaryCircle ↦ chart point) := by
    exact (Topology.IsEmbedding.subtypeVal.comp
      chart.toHomeomorphSourceTarget.isEmbedding).comp
        (Topology.IsEmbedding.inclusion hsphere)
  exact hambient.codRestrict _ _

/-- Helper for Example 74.8: the projective-plane boundary circle as a map into the deleted-disc
complement. -/
private def projectiveBoundary :
    DiscBoundaryGluing.BoundaryCircle →
      {x : RealProjectivePlane //
        x ∉ projectiveDiscChart '' Metric.ball 0 (1 / 2 : ℝ)} :=
  Set.codRestrict
    (fun point : DiscBoundaryGluing.BoundaryCircle ↦ projectiveDiscChart point) _
    (chartBoundary_not_mem_deletedDisc projectiveDiscChart projectiveDiscChart_source)

/-- Helper for Example 74.8: the torus boundary circle as a map into the deleted-disc
complement. -/
private def torusBoundary :
    DiscBoundaryGluing.BoundaryCircle →
      {x : UnitAddCircle × UnitAddCircle //
        x ∉ torusDiscChart '' Metric.ball 0 (1 / 2 : ℝ)} :=
  Set.codRestrict
    (fun point : DiscBoundaryGluing.BoundaryCircle ↦ torusDiscChart point) _
    (chartBoundary_not_mem_deletedDisc torusDiscChart torusDiscChart_source)

/-- Helper for Example 74.8: the projective boundary map has the normalized chart as its
underlying map. -/
private theorem projectiveBoundary_coe (point : DiscBoundaryGluing.BoundaryCircle) :
    (projectiveBoundary point : RealProjectivePlane) = projectiveDiscChart point := by
  rfl

/-- Helper for Example 74.8: the torus boundary map has the normalized chart as its underlying
map. -/
private theorem torusBoundary_coe (point : DiscBoundaryGluing.BoundaryCircle) :
    (torusBoundary point : UnitAddCircle × UnitAddCircle) = torusDiscChart point := by
  rfl

/-- Helper for Example 74.8: the projective boundary map is an embedding. -/
private theorem projectiveBoundary_embedding : Topology.IsEmbedding projectiveBoundary := by
  exact chartBoundaryEmbedding projectiveDiscChart projectiveDiscChart_source

/-- Helper for Example 74.8: the torus boundary map is an embedding. -/
private theorem torusBoundary_embedding : Topology.IsEmbedding torusBoundary := by
  exact chartBoundaryEmbedding torusDiscChart torusDiscChart_source

/-- The standard construction obtained by deleting coordinate discs from `P²` and the torus
and identifying their boundary circles with the same Euclidean parameter. -/
def standardGluing :
    DiscBoundaryGluing RealProjectivePlane (UnitAddCircle × UnitAddCircle) where
  leftChart := projectiveDiscChart
  rightChart := torusDiscChart
  leftSource := projectiveDiscChart_source
  rightSource := torusDiscChart_source
  leftBoundary := projectiveBoundary
  rightBoundary := torusBoundary
  leftBoundary_coe := projectiveBoundary_coe
  rightBoundary_coe := torusBoundary_coe
  leftBoundary_embedding := projectiveBoundary_embedding
  rightBoundary_embedding := torusBoundary_embedding
  boundaryIdentification := Homeomorph.refl _

/-- Helper for Example 74.8: the standard gluing identifies the two boundary circles with
the same Euclidean parameter. -/
lemma standardGluing_boundaryIdentification_apply
    (point : DiscBoundaryGluing.BoundaryCircle) :
    standardGluing.boundaryIdentification point = point := by
  -- The stored boundary homeomorphism is the identity homeomorphism.
  rfl

/-- Helper for Example 74.8: the left chart of the standard gluing is the canonical
projective model map on the corresponding interior disk point. -/
lemma standardGluing_leftChart_apply (point : ModelPlane) :
    standardGluing.leftChart point = projectiveModelMap (projectiveInteriorPoint point) := by
  -- Expose the restricted chart once at its owner, then pass to the canonical disk model.
  exact (projectiveDiscChart_apply point).trans
    (projectiveModelEmbedding_eq_modelMap point)

/-- Helper for Example 74.8: the right chart of the standard gluing is the canonical scaled
torus model map on every model-plane point. -/
lemma standardGluing_rightChart_apply (point : ModelPlane) :
    standardGluing.rightChart point = torusModelMap point := by
  -- Restriction changes only the chart source, while the product circle chart coerces the two
  -- scaled real coordinates to the two additive circles.
  rfl

/-- Helper for Example 74.8: the deleted projective disc has exactly the expected preimage in
the canonical closed-disk quotient model. -/
lemma projectiveModelMap_preimage_leftDeletedDisc :
    projectiveModelMap ⁻¹' standardGluing.leftDeletedDisc =
      projectiveInteriorPoint '' Metric.ball (0 : ModelPlane) (1 / 2 : ℝ) := by
  ext point
  change projectiveModelMap point ∈
      projectiveDiscChart '' Metric.ball (0 : ModelPlane) (1 / 2 : ℝ) ↔
    point ∈ projectiveInteriorPoint '' Metric.ball (0 : ModelPlane) (1 / 2 : ℝ)
  constructor
  · rintro ⟨coordinate, hcoordinate, hcoordinateImage⟩
    -- Cancel the projective homeomorphism and inspect the disk-antipodal quotient fiber.
    have hmodel :
        projectiveModelMap (projectiveInteriorPoint coordinate) =
          projectiveModelMap point := by
      calc
        projectiveModelMap (projectiveInteriorPoint coordinate) =
            projectiveModelEmbedding coordinate :=
          (projectiveModelEmbedding_eq_modelMap coordinate).symm
        _ = projectiveDiscChart coordinate :=
          (projectiveDiscChart_apply coordinate).symm
        _ = projectiveModelMap point := hcoordinateImage
    have hquotient :=
      (projectiveModelMap_eq_iff (projectiveInteriorPoint coordinate) point).mp hmodel
    rcases (DiskAntipodalQuotient.quotientMap_eq_iff
      (projectiveInteriorPoint coordinate) point).mp hquotient with
      hsame | ⟨hboundary, _⟩
    · exact ⟨coordinate, hcoordinate, hsame.symm⟩
    · exact (projectiveInteriorPoint_not_boundary coordinate hboundary).elim
  · rintro ⟨coordinate, hcoordinate, rfl⟩
    -- The chart and model map use the same interior quotient representative.
    exact ⟨coordinate, hcoordinate,
      (projectiveDiscChart_apply coordinate).trans
        (projectiveModelEmbedding_eq_modelMap coordinate)⟩


end

end ProjectivePlaneTorus
