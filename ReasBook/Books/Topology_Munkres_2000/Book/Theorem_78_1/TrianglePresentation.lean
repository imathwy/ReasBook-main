module

public import Topology_Munkres_2000.Book.Theorem_78_1.OpenEdgeCollar
public import Topology_Munkres_2000.Book.Theorem_74_1.PolygonalPasting
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.Basis

import all Topology_Munkres_2000.Book.Definition_78_1.Triangulation
import all Topology_Munkres_2000.Book.Definition_74_2.Parameterization
import all Topology_Munkres_2000.Book.Definition_74_3

public section

open scoped Affine

namespace Theorem78_1

/-- Helper for Theorem 78.1: the lifted arguments of the fixed cyclic triangle. -/
noncomputable def presentationTriangleAngles (i : Fin 4) : ℝ :=
  ![0, Real.pi / 2, Real.pi, 2 * Real.pi] i

/-- Helper for Theorem 78.1: the lifted triangle arguments are strictly increasing. -/
theorem presentationTriangleAngles_strictMono :
    StrictMono presentationTriangleAngles := by
  -- Check the three successive inequalities, using positivity of `π`.
  refine Fin.strictMono_iff_lt_succ.mpr ?_
  intro i
  fin_cases i
  · norm_num [presentationTriangleAngles, Matrix.cons_val_two]
    linarith [Real.pi_pos]
  · norm_num [presentationTriangleAngles, Matrix.cons_val_two]
    linarith [Real.pi_pos]
  · norm_num [presentationTriangleAngles, Matrix.cons_val_two]
    linarith [Real.pi_pos]

/-- Helper for Theorem 78.1: the lifted triangle arguments close after one turn. -/
theorem presentationTriangleAngles_last :
    presentationTriangleAngles (Fin.last 3) =
      presentationTriangleAngles 0 + 2 * Real.pi := by
  -- Both sides reduce to `2 * π`.
  norm_num [presentationTriangleAngles, Fin.last]

/-- Helper for Theorem 78.1: the third fixed lifted angle is `π`. -/
theorem presentationTriangleAngles_castSucc_two :
    presentationTriangleAngles (Fin.castSucc (2 : Fin 3)) = Real.pi := by
  -- Evaluate the explicit four-entry vector at its third coordinate.
  have hindex : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := Fin.ext rfl
  rw [hindex]
  rfl

/-- Helper for Theorem 78.1: the first fixed lifted angle is zero. -/
theorem presentationTriangleAngles_zero : presentationTriangleAngles 0 = 0 := by
  -- Evaluate the first entry of the explicit angle vector.
  rfl

/-- Helper for Theorem 78.1: the second fixed lifted angle is `π / 2`. -/
theorem presentationTriangleAngles_one : presentationTriangleAngles 1 = Real.pi / 2 := by
  -- Evaluate the second entry of the explicit angle vector.
  rfl

/-- Helper for Theorem 78.1: the fixed cyclic planar triangle used for every cell. -/
noncomputable def presentationTriangle : CyclicPolygon 3 where
  three_le := le_rfl
  center := 0
  radius := 1
  radius_pos := zero_lt_one
  angles := presentationTriangleAngles
  angles_strictMono := presentationTriangleAngles_strictMono
  angles_last := presentationTriangleAngles_last

/-- Helper for Theorem 78.1: the two nonzero indices of `Fin 3` are indexed by `Fin 2`. -/
def finTwoEquivNonzeroFinThree : Fin 2 ≃ {j : Fin 3 // j ≠ 0} where
  toFun j := ⟨j.succ, Fin.succ_ne_zero j⟩
  invFun j := ⟨j.1 - 1, by omega⟩
  left_inv j := by
    apply Fin.ext
    change j.1 + 1 - 1 = j.1
    omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    change j.1.1 - 1 + 1 = j.1.1
    have hj : 0 < j.1.1 := by
      exact Fin.pos_iff_ne_zero.mpr j.2
    omega

/-- Helper for Theorem 78.1: the three fixed cyclic vertices are affinely independent. -/
theorem presentationTriangle_affineIndependent :
    AffineIndependent ℝ presentationTriangle.toPolygon.vertices := by
  -- Use the first vertex as origin and check that the two edge vectors are independent.
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3)]
  rw [← linearIndependent_equiv finTwoEquivNonzeroFinThree]
  rw [linearIndependent_fin2]
  constructor
  · intro hzero
    have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) hzero
    simp only [CyclicPolygon.toPolygon_vertices] at hcoord
    norm_num [finTwoEquivNonzeroFinThree, presentationTriangle,
      CyclicPolygon.vertex, presentationTriangleAngles_castSucc_two,
      presentationTriangleAngles_zero, presentationTriangleAngles_one,
      Matrix.cons_val_two, Matrix.cons_val_three, PiLp.toLp_apply] at hcoord
  · intro a heq
    have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) heq
    simp only [CyclicPolygon.toPolygon_vertices] at hcoord
    norm_num [finTwoEquivNonzeroFinThree, presentationTriangle,
      CyclicPolygon.vertex, presentationTriangleAngles_castSucc_two,
      presentationTriangleAngles_zero, presentationTriangleAngles_one,
      Matrix.cons_val_two, Matrix.cons_val_three, PiLp.toLp_apply] at hcoord

/-- Helper for Theorem 78.1: the fixed cyclic vertices regarded as an affine simplex. -/
noncomputable def presentationSimplex :
    Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 :=
  ⟨presentationTriangle.toPolygon.vertices,
    presentationTriangle_affineIndependent⟩

/-- Helper for Theorem 78.1: the fixed presentation simplex spans the plane. -/
theorem presentationSimplex_span_eq_top :
    affineSpan ℝ (Set.range presentationSimplex.points) = ⊤ := by
  -- Its dimension equals the dimension of the Euclidean plane.
  exact presentationSimplex.span_eq_top (by simp)

/-- Helper for Theorem 78.1: the fixed cyclic region is the closed interior of
the corresponding affine simplex. -/
theorem presentationTriangle_region_eq_closedInterior :
    presentationTriangle.region = presentationSimplex.closedInterior := by
  -- Both sets are the convex hull of the same three vertices.
  rw [presentationTriangle.region_eq_convexHull,
    ← presentationSimplex.convexHull_eq_closedInterior]
  rfl

/-- Helper for Theorem 78.1: the fixed presentation vertices form an affine basis. -/
noncomputable def presentationAffineBasis :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨presentationSimplex.points, presentationSimplex.independent,
    presentationSimplex_span_eq_top⟩

/-- Helper for Theorem 78.1: cyclic edges of the fixed presentation triangle
are in bijection with the opposite-face indices of its affine simplex. -/
def presentationEdgeEquiv : Fin 3 ≃ Fin 3 where
  toFun i := finRotate 3 (finRotate 3 i)
  invFun i := finRotate 3 i
  left_inv i := by
    fin_cases i <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

/-- Helper for Theorem 78.1: the model edge corresponding to a cyclic edge of
the fixed presentation triangle. -/
def presentationEdgeToModelEdge (i : Fin 3) : Fin 3 :=
  presentationEdgeEquiv i

/-- Helper for Theorem 78.1: the cyclic parameter must be reversed precisely
on the last edge to match the model face ordering. -/
def presentationEdgeSign (i : Fin 3) : Bool :=
  decide (i ≠ 2)

/-- Helper for Theorem 78.1: equip the fixed presentation triangle with an
arbitrary edge labelling and the model-compatible base orientations. -/
noncomputable def presentationEdgePasting {S : Type*} (label : Fin 3 → S) :
    presentationTriangle.EdgePasting S :=
  CyclicPolygon.EdgePasting.ofSigns presentationTriangle label presentationEdgeSign

/-- Helper for Theorem 78.1: an oriented presentation-edge point is the cyclic
edge point with the parameter selected by the base orientation. -/
theorem presentationEdgePasting_orientedPoint
    {S : Type*} (label : Fin 3 → S) (i : Fin 3) (t : unitInterval) :
    (presentationEdgePasting label |>.orientedPoint i t :
        EuclideanSpace ℝ (Fin 2)) =
      (presentationTriangle.edgePoint i
          (if presentationEdgeSign i then t else unitInterval.symm t) :
        EuclideanSpace ℝ (Fin 2)) := by
  -- The positive cases use the cyclic segment; the last case uses its reversal.
  fin_cases i <;>
    rw [CyclicPolygon.EdgePasting.orientedPoint_apply,
      CyclicPolygon.EdgePasting.includePoint_coe,
      OrientedSegment.point_coe,
      presentationTriangle.edgePoint_coe_eq_lineMap] <;>
    simp [presentationEdgePasting, presentationEdgeSign,
      CyclicPolygon.EdgePasting.ofSigns, CyclicPolygon.signedOrientation,
      CyclicPolygon.cyclicOrientation, OrientedSegment.reverse,
      unitInterval.coe_symm_eq, AffineMap.lineMap_apply_module'] <;>
    ext k <;>
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] <;>
    ring

/-- Helper for Theorem 78.1: orient each fixed presentation edge either with
or against its model-compatible parameterization. -/
noncomputable def presentationDirectedEdgePasting {S : Type*}
    (label : Fin 3 → S) (direction : Fin 3 → Bool) :
    presentationTriangle.EdgePasting S :=
  CyclicPolygon.EdgePasting.ofSigns presentationTriangle label
    (fun i ↦ decide (presentationEdgeSign i = direction i))

/-- Helper for Theorem 78.1: the directed edge pasting retains the supplied
edge labels. -/
theorem presentationDirectedEdgePasting_label
    {S : Type*} (label : Fin 3 → S) (direction : Fin 3 → Bool) (i : Fin 3) :
    (presentationDirectedEdgePasting label direction).label i = label i := by
  -- Direction changes only the sign field, not the label field.
  rfl

/-- Helper for Theorem 78.1: a directed presentation-edge point is the base
model-compatible point with its parameter reversed exactly in the negative
direction. -/
theorem presentationDirectedEdgePasting_orientedPoint
    {S : Type*} (label : Fin 3 → S) (direction : Fin 3 → Bool)
    (i : Fin 3) (t : unitInterval) :
    (presentationDirectedEdgePasting label direction |>.orientedPoint i t :
        EuclideanSpace ℝ (Fin 2)) =
      (presentationEdgePasting label |>.orientedPoint i
        (if direction i then t else unitInterval.symm t) :
          EuclideanSpace ℝ (Fin 2)) := by
  -- On each of the three sides, split the requested direction and compare
  -- the two affine segment parameterizations directly.
  fin_cases i
  · cases hdirection : direction 0 <;>
      rw [CyclicPolygon.EdgePasting.orientedPoint_apply,
        CyclicPolygon.EdgePasting.includePoint_coe,
        CyclicPolygon.EdgePasting.orientedPoint_apply,
        CyclicPolygon.EdgePasting.includePoint_coe,
        OrientedSegment.point_coe,
        OrientedSegment.point_coe] <;>
      simp [presentationDirectedEdgePasting, presentationEdgePasting,
        presentationEdgeSign, hdirection,
        CyclicPolygon.EdgePasting.ofSigns, CyclicPolygon.signedOrientation,
        CyclicPolygon.cyclicOrientation, OrientedSegment.reverse,
        unitInterval.coe_symm_eq, AffineMap.lineMap_apply_module'] <;>
      ext k <;>
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul] <;>
      ring
  · cases hdirection : direction 1 <;>
      rw [CyclicPolygon.EdgePasting.orientedPoint_apply,
        CyclicPolygon.EdgePasting.includePoint_coe,
        CyclicPolygon.EdgePasting.orientedPoint_apply,
        CyclicPolygon.EdgePasting.includePoint_coe,
        OrientedSegment.point_coe,
        OrientedSegment.point_coe] <;>
      simp [presentationDirectedEdgePasting, presentationEdgePasting,
        presentationEdgeSign, hdirection,
        CyclicPolygon.EdgePasting.ofSigns, CyclicPolygon.signedOrientation,
        CyclicPolygon.cyclicOrientation, OrientedSegment.reverse,
        unitInterval.coe_symm_eq, AffineMap.lineMap_apply_module'] <;>
      ext k <;>
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul] <;>
      ring
  · cases hdirection : direction 2 <;>
      rw [CyclicPolygon.EdgePasting.orientedPoint_apply,
      CyclicPolygon.EdgePasting.includePoint_coe,
      CyclicPolygon.EdgePasting.orientedPoint_apply,
      CyclicPolygon.EdgePasting.includePoint_coe,
      OrientedSegment.point_coe,
      OrientedSegment.point_coe] <;>
      simp [presentationDirectedEdgePasting, presentationEdgePasting,
        presentationEdgeSign, hdirection,
        CyclicPolygon.EdgePasting.ofSigns, CyclicPolygon.signedOrientation,
        CyclicPolygon.cyclicOrientation, OrientedSegment.reverse,
        unitInterval.coe_symm_eq, AffineMap.lineMap_apply_module'] <;>
      ext k <;>
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul] <;>
      ring

end Theorem78_1

namespace CurvedTriangle

/-- Helper for Theorem 78.1: the affine equivalence carrying each fixed cyclic vertex
to the correspondingly indexed model vertex of a curved triangle. -/
noncomputable def presentationAffineEquiv
    {X : Type*} [TopologicalSpace X] (triangle : CurvedTriangle X) :
    EuclideanSpace ℝ (Fin 2) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  AffineEquiv.ofLinearEquiv
    ((Theorem78_1.presentationAffineBasis.basisOf 0).equiv
      (triangle.modelAffineBasis.basisOf 0) (Equiv.refl _))
    (Theorem78_1.presentationAffineBasis 0) (triangle.modelAffineBasis 0)

/-- Helper for Theorem 78.1: the presentation affine equivalence has the prescribed
value on every cyclic vertex. -/
theorem presentationAffineEquiv_vertex
    {X : Type*} [TopologicalSpace X] (triangle : CurvedTriangle X) (i : Fin 3) :
    triangle.presentationAffineEquiv
        (Theorem78_1.presentationTriangle.toPolygon.vertices i) =
      triangle.model.points i := by
  by_cases hi : i = 0
  · subst i
    -- The distinguished base vertex is built into `AffineEquiv.ofLinearEquiv`.
    rw [presentationAffineEquiv, AffineEquiv.ofLinearEquiv_apply]
    have hbase : Theorem78_1.presentationTriangle.toPolygon.vertices 0 =
        Theorem78_1.presentationAffineBasis 0 := rfl
    rw [hbase, vsub_self, map_zero, zero_vadd]
    exact triangle.modelAffineBasis_apply 0
  · let j : {k : Fin 3 // k ≠ 0} := ⟨i, hi⟩
    -- Every other vertex is the base vertex plus its corresponding basis vector.
    calc
      triangle.presentationAffineEquiv
          (Theorem78_1.presentationTriangle.toPolygon.vertices i) =
          ((Theorem78_1.presentationAffineBasis.basisOf 0).equiv
              (triangle.modelAffineBasis.basisOf 0) (Equiv.refl _))
              (Theorem78_1.presentationAffineBasis i -ᵥ
                Theorem78_1.presentationAffineBasis 0) +ᵥ
            triangle.modelAffineBasis 0 := by
              rw [presentationAffineEquiv, AffineEquiv.ofLinearEquiv_apply]
              rfl
      _ = ((Theorem78_1.presentationAffineBasis.basisOf 0).equiv
              (triangle.modelAffineBasis.basisOf 0) (Equiv.refl _))
              (Theorem78_1.presentationAffineBasis.basisOf 0 j) +ᵥ
            triangle.modelAffineBasis 0 := by
              rw [Theorem78_1.presentationAffineBasis.basisOf_apply]
      _ = triangle.modelAffineBasis.basisOf 0 j +ᵥ
            triangle.modelAffineBasis 0 := by
              rw [Module.Basis.equiv_apply]
              rfl
      _ = triangle.modelAffineBasis i := by
              rw [triangle.modelAffineBasis.basisOf_apply, vsub_vadd]
      _ = triangle.model.points i := triangle.modelAffineBasis_apply i

/-- Helper for Theorem 78.1: affine transport sends a cyclic edge parameter
to the corresponding model-face parameter, with the single required reversal. -/
theorem presentationAffineEquiv_edgePoint
    {X : Type*} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (i : Fin 3) (t : unitInterval) :
    triangle.presentationAffineEquiv
        (Theorem78_1.presentationTriangle.edgePoint i t :
          EuclideanSpace ℝ (Fin 2)) =
      triangle.modelEdgeValue (Theorem78_1.presentationEdgeToModelEdge i)
        (if i = 2 then unitInterval.symm t else t) := by
  have hsuccAboveTwoOne : (2 : Fin 3).succAbove (1 : Fin 2) = 1 :=
    Fin.ext rfl
  -- The three finite cases expose the induced ordering on each opposite face.
  fin_cases i <;>
    rw [Theorem78_1.presentationTriangle.edgePoint_coe_eq_lineMap,
      AffineEquiv.apply_lineMap, triangle.presentationAffineEquiv_vertex,
      triangle.presentationAffineEquiv_vertex] <;>
    simp [Theorem78_1.presentationEdgeToModelEdge,
      Theorem78_1.presentationEdgeEquiv,
      CurvedTriangle.modelEdgeValue,
      Affine.Simplex.faceOpposite_point_eq_point_succAbove,
      hsuccAboveTwoOne, unitInterval.coe_symm_eq,
      AffineMap.lineMap_apply_module'] <;>
    ext k <;>
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] <;>
    ring

/-- Helper for Theorem 78.1: affine transport sends a directed polygon edge
to the corresponding model edge with precisely the requested direction. -/
theorem presentationAffineEquiv_directedOrientedPoint
    {X : Type*} [TopologicalSpace X] (triangle : CurvedTriangle X)
    {S : Type*} (label : Fin 3 → S) (direction : Fin 3 → Bool)
    (i : Fin 3) (t : unitInterval) :
    triangle.presentationAffineEquiv
        (Theorem78_1.presentationDirectedEdgePasting label direction
          |>.orientedPoint i t : EuclideanSpace ℝ (Fin 2)) =
      triangle.modelEdgeValue (Theorem78_1.presentationEdgeToModelEdge i)
        (if direction i then t else unitInterval.symm t) := by
  -- First normalize to the model-compatible base orientation, then use the
  -- affine edge computation; its one cyclic reversal cancels the base sign.
  rw [Theorem78_1.presentationDirectedEdgePasting_orientedPoint,
    Theorem78_1.presentationEdgePasting_orientedPoint,
    triangle.presentationAffineEquiv_edgePoint]
  fin_cases i <;>
    simp [Theorem78_1.presentationEdgeSign]

/-- Helper for Theorem 78.1: the presentation affine equivalence carries the
fixed cyclic region onto a curved triangle's planar model. -/
theorem presentationAffineEquiv_image_region
    {X : Type*} [TopologicalSpace X] (triangle : CurvedTriangle X) :
    triangle.presentationAffineEquiv ''
        Theorem78_1.presentationTriangle.region =
      triangle.model.closedInterior := by
  have hrange : triangle.presentationAffineEquiv ''
      Set.range Theorem78_1.presentationTriangle.toPolygon.vertices =
        Set.range triangle.model.points := by
    -- The affine equivalence sends the three generators to the model generators.
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (triangle.presentationAffineEquiv_vertex i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Theorem78_1.presentationTriangle.toPolygon.vertices i,
        ⟨i, rfl⟩, triangle.presentationAffineEquiv_vertex i⟩
  -- Affine maps commute with convex hulls, so the vertex computation controls
  -- the complete filled triangle.
  rw [Theorem78_1.presentationTriangle.region_eq_convexHull]
  calc
    triangle.presentationAffineEquiv ''
          convexHull ℝ (Set.range
            Theorem78_1.presentationTriangle.toPolygon.vertices) =
        convexHull ℝ (triangle.presentationAffineEquiv ''
          Set.range Theorem78_1.presentationTriangle.toPolygon.vertices) :=
      triangle.presentationAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ (Set.range triangle.model.points) :=
      congrArg (convexHull ℝ) hrange
    _ = triangle.model.closedInterior :=
      triangle.model.convexHull_eq_closedInterior

/-- Helper for Theorem 78.1: the fixed cyclic region is homeomorphic to every
curved-triangle carrier, via affine transport followed by its chart. -/
noncomputable def presentationRegionHomeomorph
    {X : Type*} [TopologicalSpace X] (triangle : CurvedTriangle X) :
    Theorem78_1.presentationTriangle.region ≃ₜ triangle.carrier :=
  ((((AffineEquiv.toContinuousAffineEquiv triangle.presentationAffineEquiv)
      |>.toHomeomorph).image Theorem78_1.presentationTriangle.region).trans
    (Homeomorph.setCongr triangle.presentationAffineEquiv_image_region)).trans
      triangle.chart

/-- Helper for Theorem 78.1: the carrier-valued presentation homeomorphism
applies the affine model map and then the curved-triangle chart. -/
theorem presentationRegionHomeomorph_coe
    {X : Type*} [TopologicalSpace X] (triangle : CurvedTriangle X)
    (x : Theorem78_1.presentationTriangle.region) :
    ((triangle.presentationRegionHomeomorph x : triangle.carrier) : X) =
      (triangle.chart
        (⟨triangle.presentationAffineEquiv x,
          by
            rw [← triangle.presentationAffineEquiv_image_region]
            exact ⟨x, x.property, rfl⟩⟩ : triangle.model.closedInterior) : X) := by
  -- The two intermediate homeomorphisms only replace the image-membership
  -- certificate, so coercion exposes the affine value before applying `chart`.
  rw [presentationRegionHomeomorph, Homeomorph.trans_apply,
    Homeomorph.trans_apply]
  rfl

/-- Helper for Theorem 78.1: on every directed polygon edge, the presentation
homeomorphism is the curved edge parameterization with that direction. -/
theorem presentationRegionHomeomorph_directedOrientedPoint
    {X : Type*} [TopologicalSpace X] (triangle : CurvedTriangle X)
    {S : Type*} (label : Fin 3 → S) (direction : Fin 3 → Bool)
    (i : Fin 3) (t : unitInterval) :
    ((triangle.presentationRegionHomeomorph
        (Theorem78_1.presentationDirectedEdgePasting label direction
          |>.orientedPoint i t) : triangle.carrier) : X) =
      (triangle.chart
        (triangle.modelEdgePoint
          (Theorem78_1.presentationEdgeToModelEdge i)
          (if direction i then t else unitInterval.symm t)) : X) := by
  -- Use the coercion computation to move to the planar model, then identify
  -- the transported affine value with the canonical model-edge point.
  rw [triangle.presentationRegionHomeomorph_coe]
  apply congrArg (fun y : triangle.model.closedInterior ↦
    (triangle.chart y : X))
  apply Subtype.ext
  exact triangle.presentationAffineEquiv_directedOrientedPoint
    label direction i t

end CurvedTriangle
