module

public import Topology_Munkres_2000.Book.Example_74_8.BoundaryGluing
public import Topology_Munkres_2000.Book.Example_74_8.CollarKernel
public import Topology_Munkres_2000.Book.Example_74_8.CollarGeometry
public import Topology_Munkres_2000.Book.Example_74_8.StandardGluing
public import Topology_Munkres_2000.Book.Example_74_8.Surface
public import Topology_Munkres_2000.Book.Example_74_8.TorusCollarRadial
public import Topology_Munkres_2000.Book.Example_74_8.TorusFundamentalSquare
public import Topology_Munkres_2000.Book.Proposition_74_1
import Topology_Munkres_2000.Book.Theorem_60_3
import Mathlib.Topology.LocalAtTarget

public section

namespace ProjectivePlaneTorus

/-- Helper for Example 74.8: restrict the global torus model to the preimage of the chosen
deleted-disc complement. -/
noncomputable def torusComplementModelMap :
    torusModelMap ⁻¹' standardGluing.rightDeletedDiscᶜ → standardGluing.RightComplement :=
  standardGluing.rightDeletedDiscᶜ.restrictPreimage torusModelMap

/-- Helper for Example 74.8: the restricted torus model is a quotient presentation of the
chosen deleted-disc complement. -/
lemma torusComplementModelMap_isQuotientMap :
    Topology.IsQuotientMap torusComplementModelMap := by
  -- Open quotient maps remain quotient maps after restricting over any target subset.
  exact (torusModelMap_isOpenQuotientMap.restrictPreimage
    standardGluing.rightDeletedDiscᶜ).isQuotientMap

/-- Helper for Example 74.8: the chosen projective-plane disc is open. -/
lemma isOpen_standardGluing_leftDeletedDisc :
    IsOpen standardGluing.leftDeletedDisc := by
  -- The smaller coordinate ball lies in the chart source, so its chart image is open.
  apply standardGluing.leftChart.isOpen_image_of_subset_source Metric.isOpen_ball
  rw [standardGluing.leftSource]
  have hradius : (1 / 2 : ℝ) ≤ 1 := by
    norm_num
  exact Metric.ball_subset_ball hradius

/-- Helper for Example 74.8: the canonical disk-model preimage of the projective complement
is the complement of the radius-one-half coordinate image. -/
lemma projectiveModelMap_preimage_leftComplement :
    projectiveModelMap ⁻¹' standardGluing.leftDeletedDiscᶜ =
      (projectiveInteriorPoint ''
        Metric.ball (0 : ModelPlane) (1 / 2 : ℝ))ᶜ := by
  -- Preimages commute with complements, and the deleted-disc preimage was computed exactly.
  rw [Set.preimage_compl, projectiveModelMap_preimage_leftDeletedDisc]

/-- Helper for Example 74.8: restrict the canonical projective model to the preimage of the
chosen deleted-disc complement. -/
noncomputable def projectiveComplementModelMap :
    projectiveModelMap ⁻¹' standardGluing.leftDeletedDiscᶜ →
      standardGluing.LeftComplement :=
  standardGluing.leftDeletedDiscᶜ.restrictPreimage projectiveModelMap

/-- Helper for Example 74.8: the restricted disk-antipodal model is a quotient presentation
of the chosen projective-plane complement. -/
lemma projectiveComplementModelMap_isQuotientMap :
    Topology.IsQuotientMap projectiveComplementModelMap := by
  -- The model domain is a closed subset of the compact disk; its continuous surjection onto
  -- the Hausdorff projective complement is therefore a quotient map.
  have hclosed : IsClosed
      (projectiveModelMap ⁻¹' standardGluing.leftDeletedDiscᶜ) :=
    isOpen_standardGluing_leftDeletedDisc.isClosed_compl.preimage
      projectiveModelMap_isQuotientMap.continuous
  letI : CompactSpace
      (projectiveModelMap ⁻¹' standardGluing.leftDeletedDiscᶜ) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  exact Topology.IsQuotientMap.of_surjective_continuous
    (projectiveModelMap_isQuotientMap.surjective.restrictPreimage _)
    projectiveModelMap_isQuotientMap.continuous.restrictPreimage

/-- Helper for Example 74.8: restricting the projective model to the complement preserves
its underlying projective-plane value. -/
lemma projectiveComplementModelMap_coe
    (point : projectiveModelMap ⁻¹' standardGluing.leftDeletedDiscᶜ) :
    (projectiveComplementModelMap point : RealProjectivePlane) =
      projectiveModelMap point := by
  -- Unfold the restriction once, at its owner-facing coercion boundary.
  rfl

/-- Helper for Example 74.8: the disjoint union of the two model preimages presents the two
deleted-disc complements simultaneously. -/
abbrev ComplementModelSource :=
  (projectiveModelMap ⁻¹' standardGluing.leftDeletedDiscᶜ) ⊕
    (torusModelMap ⁻¹' standardGluing.rightDeletedDiscᶜ)

/-- Helper for Example 74.8: the simultaneous model presentation maps each branch to its
corresponding deleted-disc complement. -/
noncomputable def complementModelMap : ComplementModelSource →
    standardGluing.LeftComplement ⊕ standardGluing.RightComplement :=
  Sum.map projectiveComplementModelMap torusComplementModelMap

/-- Helper for Example 74.8: the canonical quotient presentation of the deleted-disc
adjunction space from the sum of its two complements. -/
noncomputable def standardGluingPresentation :
    C(standardGluing.LeftComplement ⊕ standardGluing.RightComplement,
      standardGluing.GluedSurface) :=
  ⟨AdjunctionSpace.quotientMap standardGluing.attachingSubset standardGluing.attachingMap,
    AdjunctionSpace.continuous_quotientMap standardGluing.attachingSubset
      standardGluing.attachingMap⟩

/-- Helper for Example 74.8: the canonical presentation of the deleted-disc adjunction is a
quotient map. -/
lemma standardGluingPresentation_isQuotientMap :
    Topology.IsQuotientMap standardGluingPresentation := by
  -- This is precisely the quotient topology used to define the adjunction space.
  exact AdjunctionSpace.quotientMap_isQuotientMap standardGluing.attachingSubset
    standardGluing.attachingMap

/-- Helper for Example 74.8: the fibers of the canonical gluing presentation are exactly the
generated attaching setoid. -/
lemma standardGluingPresentation_eq_iff
    (x y : standardGluing.LeftComplement ⊕ standardGluing.RightComplement) :
    standardGluingPresentation x = standardGluingPresentation y ↔
      AdjunctionSpace.setoid standardGluing.attachingSubset standardGluing.attachingMap x y := by
  -- Equality of quotient representatives is the defining adjunction relation.
  exact AdjunctionSpace.quotientMap_eq_iff standardGluing.attachingSubset
    standardGluing.attachingMap x y

/-- Helper for Example 74.8: signed area relative to the diagonal from the zeroth to the
second hexagon vertex separates the two closed cut pieces. -/
noncomputable def hexagonDiagonalSide (point : hexagon.region) : ℝ :=
  CyclicPolygon.signedAreaRightCLM
    (hexagon.toPolygon.vertices 2 - hexagon.toPolygon.vertices 0)
    (point.1 - hexagon.toPolygon.vertices 0)

/-- Helper for Example 74.8: the signed-area separator varies continuously on the filled
hexagon. -/
lemma continuous_hexagonDiagonalSide : Continuous hexagonDiagonalSide := by
  -- Subtract the fixed diagonal endpoint and apply the continuous signed-area functional.
  exact (CyclicPolygon.signedAreaRightCLM
    (hexagon.toPolygon.vertices 2 - hexagon.toPolygon.vertices 0)).continuous.comp
      (continuous_subtype_val.sub continuous_const)

/-- Helper for Example 74.8: the nonpositive side of the diagonal, kept as a closed tagged
piece. -/
abbrev ProjectiveCutPiece :=
  {point : hexagon.region // hexagonDiagonalSide point ≤ 0}

/-- Helper for Example 74.8: the nonnegative side of the diagonal, kept as a closed tagged
piece. -/
abbrev TorusCutPiece :=
  {point : hexagon.region // 0 ≤ hexagonDiagonalSide point}

/-- Helper for Example 74.8: the common source obtained by retaining separate tags on the two
closed hexagon pieces. -/
abbrev CutSource := ProjectiveCutPiece ⊕ TorusCutPiece

/-- Helper for Example 74.8: the nonpositive diagonal half is closed in the hexagon. -/
lemma projectiveCutPiece_isClosed :
    IsClosed {point : hexagon.region | hexagonDiagonalSide point ≤ 0} := by
  -- It is the inverse image of the closed order relation under continuous functions.
  exact isClosed_le continuous_hexagonDiagonalSide continuous_const

/-- Helper for Example 74.8: the nonnegative diagonal half is closed in the hexagon. -/
lemma torusCutPiece_isClosed :
    IsClosed {point : hexagon.region | 0 ≤ hexagonDiagonalSide point} := by
  -- Reverse the two continuous functions in the same closed-order argument.
  exact isClosed_le continuous_const continuous_hexagonDiagonalSide

/-- Helper for Example 74.8: forgetting the half-space tag reassembles the filled hexagon. -/
def cutReassemble : CutSource → hexagon.region :=
  Sum.elim Subtype.val Subtype.val

/-- Helper for Example 74.8: reassembling the two tagged closed pieces is continuous. -/
lemma continuous_cutReassemble : Continuous cutReassemble := by
  -- Continuity out of a sum is checked on the two subtype inclusions.
  exact Continuous.sumElim continuous_subtype_val continuous_subtype_val

/-- Helper for Example 74.8: every hexagon point occurs in at least one tagged cut piece. -/
lemma cutReassemble_surjective : Function.Surjective cutReassemble := by
  intro point
  -- Totality of the real order selects the nonpositive or nonnegative copy.
  rcases le_total (hexagonDiagonalSide point) 0 with hprojective | htorus
  · exact ⟨Sum.inl ⟨point, hprojective⟩, rfl⟩
  · exact ⟨Sum.inr ⟨point, htorus⟩, rfl⟩

/-- Helper for Example 74.8: forgetting the tag is the quotient reassembly of the two closed
hexagon pieces. -/
lemma cutReassemble_isQuotientMap :
    Topology.IsQuotientMap cutReassemble := by
  -- Compactness of the polygon and closedness of both halves make the continuous surjection
  -- to the Hausdorff hexagon a quotient map.
  letI : CompactSpace hexagon.region := by
    apply isCompact_iff_compactSpace.mp
    rw [hexagon.region_eq_convexHull]
    exact (Set.finite_range hexagon.toPolygon.vertices).isCompact_convexHull ℝ
  letI : CompactSpace ProjectiveCutPiece :=
    projectiveCutPiece_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  letI : CompactSpace TorusCutPiece :=
    torusCutPiece_isClosed.isClosedEmbedding_subtypeVal.compactSpace
  exact Topology.IsQuotientMap.of_surjective_continuous
    cutReassemble_surjective continuous_cutReassemble

/-- Helper for Example 74.8: quotiently reassemble the cut pieces and then paste the labeled
hexagon edges. -/
noncomputable def hexagonCutMap : CutSource → Surface :=
  fun point ↦ Quotient.mk pasting.Identified (cutReassemble point)

/-- Helper for Example 74.8: the cut-source presentation of the hexagonal surface is a
quotient map. -/
lemma hexagonCutMap_isQuotientMap :
    Topology.IsQuotientMap hexagonCutMap := by
  -- The canonical setoid projection is quotient, and quotient maps are closed under
  -- precomposition by the quotient reassembly.
  exact isQuotientMap_quotient_mk'.comp cutReassemble_isQuotientMap

/-- Helper for Example 74.8: the fiber relation of the cut-source map is exactly the edge
pasting relation after reassembly. -/
lemma hexagonCutMap_eq_iff (x y : CutSource) :
    hexagonCutMap x = hexagonCutMap y ↔
      pasting.Identified (cutReassemble x) (cutReassemble y) := by
  -- Equality in the quotient is its defining generated edge-identification relation.
  exact Quotient.eq

end ProjectivePlaneTorus

namespace Topology.IsQuotientMap

universe u₁ u₂ u₃ u₄

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃} {W : Type u₄}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

/-- Helper for Example 74.8: the sum of two quotient maps is a quotient map. -/
lemma sumMap {f : X → Y} {g : Z → W}
    (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g) :
    Topology.IsQuotientMap (Sum.map f g) := by
  -- The sum topology tests openness separately on each summand, where the two quotient-map
  -- characterizations apply independently.
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_,
    hf.surjective.sumMap hg.surjective⟩
  intro subset
  rw [isOpen_sum_iff, isOpen_sum_iff]
  change
    (IsOpen (f ⁻¹' (Sum.inl ⁻¹' subset)) ∧ IsOpen (g ⁻¹' (Sum.inr ⁻¹' subset))) ↔
      IsOpen (Sum.inl ⁻¹' subset) ∧ IsOpen (Sum.inr ⁻¹' subset)
  exact and_congr hf.isCoinducing.isOpen_preimage hg.isCoinducing.isOpen_preimage

end Topology.IsQuotientMap

namespace ProjectivePlaneTorus

/-- Helper for Example 74.8: the simultaneous model map is a quotient presentation of the
sum of the two deleted-disc complements. -/
lemma complementModelMap_isQuotientMap :
    Topology.IsQuotientMap complementModelMap := by
  -- Quotientness is checked independently on the projective and torus summands.
  exact Topology.IsQuotientMap.sumMap
    projectiveComplementModelMap_isQuotientMap torusComplementModelMap_isQuotientMap

/-- Helper for Example 74.8: the simultaneous model presentation is continuous. -/
lemma continuous_complementModelMap : Continuous complementModelMap := by
  -- Continuity is part of the quotient-map interface just established.
  exact complementModelMap_isQuotientMap.continuous

/-- Helper for Example 74.8: package the simultaneous model presentation as a continuous
map. -/
noncomputable def complementModelPresentation :
    C(ComplementModelSource,
      standardGluing.LeftComplement ⊕ standardGluing.RightComplement) :=
  ⟨complementModelMap, continuous_complementModelMap⟩

/-- Helper for Example 74.8: the packaged simultaneous model presentation is a quotient map. -/
lemma complementModelPresentation_isQuotientMap :
    Topology.IsQuotientMap complementModelPresentation := by
  -- Packaging a function as a continuous map does not change its fibers or quotientness.
  exact complementModelMap_isQuotientMap

/-- Helper for Example 74.8: every radius in the projective annulus occurs along the affine
collar radius. -/
lemma exists_projectiveCollarRadius_eq {radius : ℝ}
    (hlower : projectiveInnerRadius ≤ radius) (hupper : radius ≤ 1) :
    ∃ t : unitInterval, projectiveCollarRadius t = radius := by
  -- Normalize the desired radius to the unit interval using the positive annulus width.
  have hwidth : 0 < 1 - projectiveInnerRadius :=
    sub_pos.mpr projectiveInnerRadius_lt_one
  have hparameter_nonneg : 0 ≤
      (radius - projectiveInnerRadius) / (1 - projectiveInnerRadius) :=
    div_nonneg (sub_nonneg.mpr hlower) hwidth.le
  have hparameter_le_one :
      (radius - projectiveInnerRadius) / (1 - projectiveInnerRadius) ≤ 1 := by
    rw [div_le_one hwidth]
    linarith
  have hparameter_mem :
      (radius - projectiveInnerRadius) / (1 - projectiveInnerRadius) ∈
        Set.Icc (0 : ℝ) 1 :=
    ⟨hparameter_nonneg, hparameter_le_one⟩
  let parameter : unitInterval :=
    ⟨(radius - projectiveInnerRadius) / (1 - projectiveInnerRadius), hparameter_mem⟩
  refine ⟨parameter, ?_⟩
  -- Substitution into the affine formula recovers the prescribed radius.
  rw [projectiveCollarRadius_apply]
  dsimp only [parameter]
  field_simp [ne_of_gt hwidth]
  ring

/-- Helper for Example 74.8: the affine projective collar radius determines its interval
parameter uniquely. -/
lemma projectiveCollarRadius_injective :
    Function.Injective projectiveCollarRadius := by
  intro s t hradius
  -- Cancel the strictly positive annulus width in the two affine-radius formulas.
  apply Subtype.ext
  rw [projectiveCollarRadius_apply, projectiveCollarRadius_apply] at hradius
  have hwidth : 0 < 1 - projectiveInnerRadius :=
    sub_pos.mpr projectiveInnerRadius_lt_one
  nlinarith

/-- Helper for Example 74.8: the outer endpoint of the projective collar has unit radius. -/
lemma projectiveCollarRadius_one :
    projectiveCollarRadius 1 = 1 := by
  -- Substitute the endpoint into the affine interpolation formula.
  rw [projectiveCollarRadius_apply]
  norm_num

/-- Helper for Example 74.8: two projective collar disk points agree exactly when their
radial parameters and boundary-circle directions agree. -/
lemma projectiveCollarDiskPoint_eq_iff (x y : CollarSquare) :
    projectiveCollarDiskPoint x = projectiveCollarDiskPoint y ↔
      x.2 = y.2 ∧ boundaryCircleParam x.1 = boundaryCircleParam y.1 := by
  constructor
  · intro hxy
    -- Norms first recover the radial parameter.
    have hradius : projectiveCollarRadius x.2 = projectiveCollarRadius y.2 := by
      calc
        projectiveCollarRadius x.2 = ‖projectiveCollarVector x‖ :=
          (projectiveCollarVector_norm x).symm
        _ = ‖(projectiveCollarDiskPoint x : ModelPlane)‖ := by
          rw [projectiveCollarDiskPoint_coe]
        _ = ‖(projectiveCollarDiskPoint y : ModelPlane)‖ :=
          congrArg (fun point : B² ↦ ‖(point : ModelPlane)‖) hxy
        _ = ‖projectiveCollarVector y‖ := by
          rw [projectiveCollarDiskPoint_coe]
        _ = projectiveCollarRadius y.2 := projectiveCollarVector_norm y
    have hparameter : x.2 = y.2 := projectiveCollarRadius_injective hradius
    have hscale_pos : 0 < 2 * projectiveCollarRadius y.2 := by
      exact mul_pos (by norm_num)
        (projectiveInnerRadius_pos.trans_le
          (projectiveInnerRadius_le_collarRadius y.2))
    have hambient := congrArg (fun point : B² ↦ (point : ModelPlane)) hxy
    rw [projectiveCollarDiskPoint_coe, projectiveCollarDiskPoint_coe,
      projectiveCollarVector_apply, projectiveCollarVector_apply, hparameter] at hambient
    have hdirectionAmbient :
        (boundaryCircleParam x.1 : ModelPlane) =
          (boundaryCircleParam y.1 : ModelPlane) :=
      smul_right_injective ModelPlane (ne_of_gt hscale_pos) hambient
    exact ⟨hparameter, Subtype.ext hdirectionAmbient⟩
  · rintro ⟨hparameter, hdirection⟩
    -- Equal radius and direction make the packaged closed-disk representatives identical.
    apply Subtype.ext
    rw [projectiveCollarDiskPoint_coe, projectiveCollarDiskPoint_coe,
      projectiveCollarVector_apply, projectiveCollarVector_apply, hparameter, hdirection]

/-- Helper for Example 74.8: a projective collar disk point lies on the disk boundary exactly
at the collar's outer radial endpoint. -/
lemma projectiveCollarDiskPoint_isBoundary_iff (x : CollarSquare) :
    ClosedUnitDisk.IsBoundary (projectiveCollarDiskPoint x) ↔ x.2 = 1 := by
  -- The collar norm is its affine radius, whose unique unit value occurs at parameter one.
  rw [closedUnitDisk_isBoundary_iff_norm, projectiveCollarDiskPoint_coe,
    projectiveCollarVector_norm]
  constructor
  · intro hradius
    exact projectiveCollarRadius_injective
      (hradius.trans projectiveCollarRadius_one.symm)
  · intro hparameter
    rw [hparameter, projectiveCollarRadius_one]

/-- Helper for Example 74.8: the boundary-antipodal collar relation is exactly simultaneous
outer-radius membership with opposite boundary-circle directions. -/
lemma projectiveCollarDiskPoint_boundary_antipodal_iff (x y : CollarSquare) :
    ClosedUnitDisk.IsBoundary (projectiveCollarDiskPoint x) ∧
        projectiveCollarDiskPoint y = -projectiveCollarDiskPoint x ↔
      x.2 = 1 ∧ y.2 = 1 ∧
        boundaryCircleParam y.1 = -boundaryCircleParam x.1 := by
  constructor
  · rintro ⟨hxBoundary, hantipodal⟩
    -- Boundary norms force both radial parameters to the outer endpoint.
    have hxParameter : x.2 = 1 :=
      (projectiveCollarDiskPoint_isBoundary_iff x).mp hxBoundary
    have hyBoundary : ClosedUnitDisk.IsBoundary (projectiveCollarDiskPoint y) := by
      rw [closedUnitDisk_isBoundary_iff_norm]
      calc
        ‖(projectiveCollarDiskPoint y : ModelPlane)‖ =
            ‖((-projectiveCollarDiskPoint x : B²) : ModelPlane)‖ :=
          congrArg (fun point : B² ↦ ‖(point : ModelPlane)‖) hantipodal
        _ = ‖(projectiveCollarDiskPoint x : ModelPlane)‖ := by
          rw [closedUnitDisk_neg_coe, norm_neg]
        _ = 1 :=
          (closedUnitDisk_isBoundary_iff_norm
            (projectiveCollarDiskPoint x)).mp hxBoundary
    have hyParameter : y.2 = 1 :=
      (projectiveCollarDiskPoint_isBoundary_iff y).mp hyBoundary
    have hambient :=
      congrArg (fun point : B² ↦ (point : ModelPlane)) hantipodal
    have hscaledDirections :
        (2 : ℝ) • (boundaryCircleParam y.1 : ModelPlane) =
          (2 : ℝ) • (-(boundaryCircleParam x.1 : ModelPlane)) := by
      calc
        (2 : ℝ) • (boundaryCircleParam y.1 : ModelPlane) =
            projectiveCollarVector y := by
          rw [projectiveCollarVector_apply, hyParameter, projectiveCollarRadius_one]
          norm_num
        _ = (projectiveCollarDiskPoint y : ModelPlane) :=
          (projectiveCollarDiskPoint_coe y).symm
        _ = ((-projectiveCollarDiskPoint x : B²) : ModelPlane) := hambient
        _ = -(projectiveCollarDiskPoint x : ModelPlane) :=
          closedUnitDisk_neg_coe (projectiveCollarDiskPoint x)
        _ = -projectiveCollarVector x := by
          rw [projectiveCollarDiskPoint_coe]
        _ = (2 : ℝ) • (-(boundaryCircleParam x.1 : ModelPlane)) := by
          rw [projectiveCollarVector_apply, hxParameter, projectiveCollarRadius_one]
          norm_num
    have htwo_ne : (2 : ℝ) ≠ 0 := by
      norm_num
    have hdirectionAmbient :
        (boundaryCircleParam y.1 : ModelPlane) =
          -(boundaryCircleParam x.1 : ModelPlane) :=
      smul_right_injective ModelPlane htwo_ne hscaledDirections
    exact ⟨hxParameter, hyParameter,
      Subtype.ext (hdirectionAmbient.trans
        (boundaryCircle_neg_coe (boundaryCircleParam x.1)).symm)⟩
  · rintro ⟨hxParameter, hyParameter, hdirection⟩
    -- At unit radius, opposite directions give antipodal closed-disk points.
    constructor
    · exact (projectiveCollarDiskPoint_isBoundary_iff x).mpr hxParameter
    · apply Subtype.ext
      rw [projectiveCollarDiskPoint_coe, projectiveCollarVector_apply,
        hyParameter, projectiveCollarRadius_one,
        closedUnitDisk_neg_coe,
        projectiveCollarDiskPoint_coe, projectiveCollarVector_apply,
        hxParameter, projectiveCollarRadius_one, hdirection]
      norm_num

/-- Helper for Example 74.8: every nonzero plane vector has a standard boundary-circle
direction whose radial rescaling recovers it. -/
lemma exists_scaled_boundaryCircleParam_eq (point : ModelPlane)
    (hpoint : 0 < ‖point‖) :
    ∃ s : unitInterval,
      (2 * ‖point‖) • (boundaryCircleParam s : ModelPlane) = point := by
  -- Normalize the vector to the radius-one-half sphere parameterized by the interval.
  have hscale : 0 < 2 * ‖point‖ := mul_pos (by norm_num) hpoint
  have hnormalized_norm :
      ‖(2 * ‖point‖)⁻¹ • point‖ = (1 / 2 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hscale]
    field_simp [ne_of_gt hscale]
  have hnormalized_mem :
      (2 * ‖point‖)⁻¹ • point ∈
        Metric.sphere (0 : ModelPlane) (1 / 2 : ℝ) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hnormalized_norm
  let normalized : Metric.sphere (0 : ModelPlane) (1 / 2 : ℝ) :=
    ⟨(2 * ‖point‖)⁻¹ • point, hnormalized_mem⟩
  obtain ⟨s, hs⟩ := boundaryCircleParam_isQuotientMap.surjective normalized
  have hs_coe : (boundaryCircleParam s : ModelPlane) =
      (2 * ‖point‖)⁻¹ • point := by
    exact congrArg Subtype.val hs
  refine ⟨s, ?_⟩
  -- The positive scaling factor cancels its reciprocal.
  rw [hs_coe, smul_smul]
  simp only [mul_inv_cancel₀ (ne_of_gt hscale), one_smul]

/-- Helper for Example 74.8: every disk representative of the chosen projective complement
is reached by the explicit collar disk point. -/
lemma exists_projectiveCollarDiskPoint_eq (point : B²)
    (hpoint : projectiveModelMap point ∈ standardGluing.leftDeletedDiscᶜ) :
    ∃ collar : CollarSquare, projectiveCollarDiskPoint collar = point := by
  -- Complement membership and disk membership bound the representative's radial coordinate.
  have hlower : projectiveInnerRadius ≤ ‖(point : ModelPlane)‖ :=
    (projectiveModelComplement_iff_norm point).mp hpoint
  have hupper : ‖(point : ModelPlane)‖ ≤ 1 := by
    -- The representative's subtype certificate is precisely closed-unit-ball membership.
    exact mem_closedBall_zero_iff.mp point.property
  have hnorm_pos : 0 < ‖(point : ModelPlane)‖ :=
    projectiveInnerRadius_pos.trans_le hlower
  obtain ⟨s, hs⟩ :=
    exists_scaled_boundaryCircleParam_eq (point : ModelPlane) hnorm_pos
  obtain ⟨t, ht⟩ := exists_projectiveCollarRadius_eq hlower hupper
  refine ⟨(s, t), ?_⟩
  -- The chosen direction and radius identify the two closed-disk points extensionally.
  apply Subtype.ext
  rw [projectiveCollarDiskPoint_coe, projectiveCollarVector_apply, ht]
  exact hs

/-- Helper for Example 74.8: the explicit projective collar covers the entire deleted-disc
complement. -/
lemma projectiveCollarMap_surjective :
    Function.Surjective projectiveCollarMap := by
  intro target
  -- First choose a representative from the restricted canonical disk presentation.
  obtain ⟨point, hpoint⟩ :=
    projectiveComplementModelMap_isQuotientMap.surjective target
  obtain ⟨collar, hcollar⟩ :=
    exists_projectiveCollarDiskPoint_eq point point.property
  refine ⟨collar, ?_⟩
  -- Equality of representatives gives equality in the complement subtype.
  apply Subtype.ext
  rw [projectiveCollarMap_coe, hcollar]
  rw [← projectiveComplementModelMap_coe point]
  exact congrArg Subtype.val hpoint

/-- Helper for Example 74.8: the explicit projective collar is a quotient presentation of
the deleted-disc complement. -/
lemma projectiveCollarMap_isQuotientMap :
    Topology.IsQuotientMap projectiveCollarMap := by
  -- A continuous surjection from the compact collar square to the Hausdorff complement is
  -- a quotient map.
  exact Topology.IsQuotientMap.of_surjective_continuous
    projectiveCollarMap_surjective projectiveCollarMap.continuous

/-- Helper for Example 74.8: the projective collar fibers are ordinary endpoint-circle
fibers, together with antipodal identifications along the outer disk boundary. -/
lemma projectiveCollarMap_eq_iff (x y : CollarSquare) :
    projectiveCollarMap x = projectiveCollarMap y ↔
      (x.2 = y.2 ∧ unitInterval.endpointSetoid x.1 y.1) ∨
        (x.2 = 1 ∧ y.2 = 1 ∧
          boundaryCircleParam y.1 = -boundaryCircleParam x.1) := by
  constructor
  · intro hxy
    -- Pass through the transported projective quotient to its explicit disk relation.
    have hmodel :
        projectiveModelMap (projectiveCollarDiskPoint x) =
          projectiveModelMap (projectiveCollarDiskPoint y) := by
      calc
        projectiveModelMap (projectiveCollarDiskPoint x) =
            (projectiveCollarMap x : RealProjectivePlane) :=
          (projectiveCollarMap_coe x).symm
        _ = (projectiveCollarMap y : RealProjectivePlane) :=
          congrArg Subtype.val hxy
        _ = projectiveModelMap (projectiveCollarDiskPoint y) :=
          projectiveCollarMap_coe y
    have hquotient :=
      (projectiveModelMap_eq_iff
        (projectiveCollarDiskPoint x) (projectiveCollarDiskPoint y)).mp hmodel
    rcases (DiskAntipodalQuotient.quotientMap_eq_iff
      (projectiveCollarDiskPoint x) (projectiveCollarDiskPoint y)).mp hquotient with
      hsame | hantipodal
    · -- The ordinary disk branch fixes the radius and identifies only interval endpoints.
      have hparameters := (projectiveCollarDiskPoint_eq_iff x y).mp hsame.symm
      exact Or.inl ⟨hparameters.1,
        (boundaryCircleParam_eq_iff x.1 y.1).mp hparameters.2⟩
    · -- The remaining quotient branch is precisely outer-boundary antipodality.
      exact Or.inr
        ((projectiveCollarDiskPoint_boundary_antipodal_iff x y).mp hantipodal)
  · intro hfiber
    -- Rebuild the corresponding disk relation, then transport it to the complement subtype.
    have hquotient :
        DiskAntipodalQuotient.quotientMap (projectiveCollarDiskPoint x) =
          DiskAntipodalQuotient.quotientMap (projectiveCollarDiskPoint y) := by
      apply (DiskAntipodalQuotient.quotientMap_eq_iff
        (projectiveCollarDiskPoint x) (projectiveCollarDiskPoint y)).mpr
      rcases hfiber with hordinary | hantipodal
      · have hdirection : boundaryCircleParam x.1 = boundaryCircleParam y.1 :=
          (boundaryCircleParam_eq_iff x.1 y.1).mpr hordinary.2
        have hdisk :
            projectiveCollarDiskPoint x = projectiveCollarDiskPoint y :=
          (projectiveCollarDiskPoint_eq_iff x y).mpr ⟨hordinary.1, hdirection⟩
        exact Or.inl hdisk.symm
      · exact Or.inr
          ((projectiveCollarDiskPoint_boundary_antipodal_iff x y).mpr hantipodal)
    apply Subtype.ext
    rw [projectiveCollarMap_coe, projectiveCollarMap_coe]
    exact (projectiveModelMap_eq_iff
      (projectiveCollarDiskPoint x) (projectiveCollarDiskPoint y)).mpr hquotient

/-- Helper for Example 74.8: a projective collar point lies over a specified attaching
boundary point exactly at radius zero with the same circle parameter. -/
lemma projectiveCollarMap_eq_boundary_iff (x : CollarSquare) (s : unitInterval) :
    projectiveCollarMap x =
        standardGluing.leftBoundary (boundaryCircleParam s) ↔
      x.2 = 0 ∧ unitInterval.endpointSetoid x.1 s := by
  calc
    projectiveCollarMap x =
        standardGluing.leftBoundary (boundaryCircleParam s) ↔
        projectiveCollarMap x = projectiveCollarMap (s, 0) := by
          -- Replace the boundary point by the verified inner-edge collar value.
          rw [projectiveCollarMap_inner]
    _ ↔ ((x.2 = (s, 0).2 ∧ unitInterval.endpointSetoid x.1 (s, 0).1) ∨
        (x.2 = 1 ∧ (s, 0).2 = 1 ∧
          boundaryCircleParam (s, 0).1 = -boundaryCircleParam x.1)) :=
      projectiveCollarMap_eq_iff x (s, 0)
    _ ↔ x.2 = 0 ∧ unitInterval.endpointSetoid x.1 s := by
      constructor
      · rintro (hordinary | hantipodal)
        · simpa only [Prod.fst, Prod.snd] using hordinary
        · exact (zero_ne_one hantipodal.2.1).elim
      · intro hordinary
        have hordinary' :
            x.2 = (s, 0).2 ∧ unitInterval.endpointSetoid x.1 (s, 0).1 := by
          simpa only [Prod.fst, Prod.snd] using hordinary
        exact Or.inl hordinary'

/-- Helper for Example 74.8: the two collar branches map simultaneously to the two
deleted-disc complements. -/
noncomputable def collarComplementFunction : CollarSource →
    standardGluing.LeftComplement ⊕ standardGluing.RightComplement :=
  Sum.map projectiveCollarMap torusCollarMap

/-- Helper for Example 74.8: the simultaneous collar-to-complement map is continuous. -/
lemma continuous_collarComplementFunction :
    Continuous collarComplementFunction := by
  -- Continuity out of a sum is checked separately on the two verified collar maps.
  exact Continuous.sumElim
    (continuous_inl.comp projectiveCollarMap.continuous)
    (continuous_inr.comp torusCollarMap.continuous)

/-- Helper for Example 74.8: package the simultaneous collar presentation as a continuous
map. -/
noncomputable def collarComplementMap : C(CollarSource,
    standardGluing.LeftComplement ⊕ standardGluing.RightComplement) :=
  ⟨collarComplementFunction, continuous_collarComplementFunction⟩

/-- Helper for Example 74.8: the collar-complement presentation computes to the projective
collar map on the left summand. -/
lemma collarComplementMap_inl (point : CollarSquare) :
    collarComplementMap (Sum.inl point) = Sum.inl (projectiveCollarMap point) := by
  -- The continuous-map wrapper preserves the defining sum-map computation.
  rfl

/-- Helper for Example 74.8: the collar-complement presentation computes to the torus
collar map on the right summand. -/
lemma collarComplementMap_inr (point : CollarSquare) :
    collarComplementMap (Sum.inr point) = Sum.inr (torusCollarMap point) := by
  -- The continuous-map wrapper preserves the defining sum-map computation.
  rfl

/-- Helper for Example 74.8: a projective and torus collar point form one attachment pair
exactly when both lie on their inner edges with the same boundary-circle parameter. -/
lemma collarAttachment_iff (x y : CollarSquare) :
    (∃ a : standardGluing.attachingSubset,
      projectiveCollarMap x = a.1 ∧ torusCollarMap y = standardGluing.attachingMap a) ↔
      x.2 = 0 ∧ y.2 = 0 ∧ unitInterval.endpointSetoid x.1 y.1 := by
  constructor
  · rintro ⟨a, hx, hy⟩
    rcases a.property with ⟨point, hpoint⟩
    obtain ⟨s, hs⟩ := boundaryCircleParam_isQuotientMap.surjective point
    have hxBoundary : projectiveCollarMap x =
        standardGluing.leftBoundary (boundaryCircleParam s) := by
      calc
        projectiveCollarMap x = a.1 := hx
        _ = standardGluing.leftBoundary point := hpoint.symm
        _ = standardGluing.leftBoundary (boundaryCircleParam s) :=
          congrArg standardGluing.leftBoundary hs.symm
    have ha : a = standardGluing.leftBoundaryPoint point := by
      -- The range witness identifies the abstract attaching-subset point with its canonical
      -- boundary parameterization.
      apply Subtype.ext
      rw [standardGluing.leftBoundaryPoint_coe]
      exact hpoint.symm
    have hyBoundary : torusCollarMap y =
        standardGluing.rightBoundary (boundaryCircleParam s) := by
      calc
        torusCollarMap y = standardGluing.attachingMap a := hy
        _ = standardGluing.attachingMap
            (standardGluing.leftBoundaryPoint point) :=
          congrArg standardGluing.attachingMap ha
        _ = standardGluing.rightBoundary
            (standardGluing.boundaryIdentification point) :=
          standardGluing.attachingMap_leftBoundaryPoint point
        _ = standardGluing.rightBoundary point :=
          congrArg standardGluing.rightBoundary
            (standardGluing_boundaryIdentification_apply point)
        _ = standardGluing.rightBoundary (boundaryCircleParam s) :=
          congrArg standardGluing.rightBoundary hs.symm
    have hxParameters := (projectiveCollarMap_eq_boundary_iff x s).mp hxBoundary
    have hyParameters := (torusCollarMap_eq_boundary_iff y s).mp hyBoundary
    have hcommon : unitInterval.endpointSetoid x.1 y.1 :=
      (exists_common_endpointSetoid_iff x.1 y.1).mp
        ⟨s, hxParameters.2, hyParameters.2⟩
    exact ⟨hxParameters.1, hyParameters.1, hcommon⟩
  · rintro ⟨hxRadius, hyRadius, hparameters⟩
    have hxBoundary : projectiveCollarMap x =
        standardGluing.leftBoundary (boundaryCircleParam x.1) :=
      (projectiveCollarMap_eq_boundary_iff x x.1).mpr
        ⟨hxRadius, unitInterval.endpointSetoid.refl x.1⟩
    have hyBoundary : torusCollarMap y =
        standardGluing.rightBoundary (boundaryCircleParam x.1) :=
      (torusCollarMap_eq_boundary_iff y x.1).mpr
        ⟨hyRadius, unitInterval.endpointSetoid.symm hparameters⟩
    have hattaching : standardGluing.attachingMap
        (standardGluing.leftBoundaryPoint (boundaryCircleParam x.1)) =
        standardGluing.rightBoundary (boundaryCircleParam x.1) := by
      calc
        standardGluing.attachingMap
            (standardGluing.leftBoundaryPoint (boundaryCircleParam x.1)) =
            standardGluing.rightBoundary
            (standardGluing.boundaryIdentification (boundaryCircleParam x.1)) :=
          standardGluing.attachingMap_leftBoundaryPoint (boundaryCircleParam x.1)
        _ = standardGluing.rightBoundary (boundaryCircleParam x.1) :=
          congrArg standardGluing.rightBoundary
            (standardGluing_boundaryIdentification_apply (boundaryCircleParam x.1))
    refine ⟨standardGluing.leftBoundaryPoint (boundaryCircleParam x.1), ?_,
      hyBoundary.trans hattaching.symm⟩
    -- The chosen attaching point stores precisely the projective inner-boundary value.
    rw [standardGluing.leftBoundaryPoint_coe]
    exact hxBoundary

/-- Helper for Example 74.8: the adjunction kernel on the common collar source is the
explicit four-case projective, torus, and cross-boundary relation. -/
lemma collarGluingKernel_iff (x y : CollarSource) :
    AdjunctionSpace.setoid standardGluing.attachingSubset standardGluing.attachingMap
        (collarComplementMap x) (collarComplementMap y) ↔
      match x, y with
      | Sum.inl p, Sum.inl q =>
          (p.2 = q.2 ∧ unitInterval.endpointSetoid p.1 q.1) ∨
            (p.2 = 1 ∧ q.2 = 1 ∧
              boundaryCircleParam q.1 = -boundaryCircleParam p.1)
      | Sum.inr p, Sum.inr q =>
          TorusSquare.identified (torusCollarRadialMap p).1
            (torusCollarRadialMap q).1
      | Sum.inl p, Sum.inr q =>
          p.2 = 0 ∧ q.2 = 0 ∧ unitInterval.endpointSetoid p.1 q.1
      | Sum.inr p, Sum.inl q =>
          q.2 = 0 ∧ p.2 = 0 ∧ unitInterval.endpointSetoid q.1 p.1 := by
  have hattachingInjective : Function.Injective standardGluing.attachingMap :=
    standardGluing.attachingMap_injective
  -- Split the collar coproduct, normalize the adjunction closure, and consume the existing
  -- exact fiber theorem for the relevant branch.
  rcases x with x | x <;> rcases y with y | y
  · rw [collarComplementMap_inl, collarComplementMap_inl,
      AdjunctionSpace.setoid_iff_of_injective _ _ hattachingInjective]
    simpa only [Sum.inl.injEq, Sum.inl_ne_inr, and_false, false_and,
      exists_false, or_false]
      using projectiveCollarMap_eq_iff x y
  · rw [collarComplementMap_inl, collarComplementMap_inr,
      AdjunctionSpace.setoid_iff_of_injective _ _ hattachingInjective]
    simpa only [Sum.inl_ne_inr, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inr_ne_inl, false_and, exists_false, false_or, or_false]
      using collarAttachment_iff x y
  · rw [collarComplementMap_inr, collarComplementMap_inl,
      AdjunctionSpace.setoid_iff_of_injective _ _ hattachingInjective]
    simpa only [Sum.inr_ne_inl, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, false_and, exists_false, false_or, or_false]
      using collarAttachment_iff y x
  · rw [collarComplementMap_inr, collarComplementMap_inr,
      AdjunctionSpace.setoid_iff_of_injective _ _ hattachingInjective]
    simpa only [Sum.inr.injEq, Sum.inr_ne_inl, and_false, false_and,
      exists_false, or_false]
      using torusCollarMap_eq_iff x y

/-- Helper for Example 74.8: the two collar branches form a quotient presentation of the
sum of the deleted-disc complements. -/
lemma collarComplementMap_isQuotientMap :
    Topology.IsQuotientMap collarComplementMap := by
  -- Quotientness is checked branchwise using the sum-map theorem.
  exact Topology.IsQuotientMap.sumMap
    projectiveCollarMap_isQuotientMap torusCollarMap_isQuotientMap

end ProjectivePlaneTorus

/-- Example 74.8. The surface obtained by deleting the standard open discs from `P²` and the
torus and gluing their boundary circles is homeomorphic to the regular-hexagon realization with
boundary word `a a b c b⁻¹ c⁻¹`. -/
theorem projectivePlaneTorusGluingHomeomorphicHexagon :
    Nonempty
      (ProjectivePlaneTorus.standardGluing.GluedSurface ≃ₜ ProjectivePlaneTorus.Surface) :=
  by
    -- Route correction: the signed-area cut pieces do not provide coordinates for the
    -- complements.  The two explicit collar maps now give the source presentation, so only
    -- the matching triangle--pentagon hexagon presentation remains to be constructed.
    suffices hhexagonPresentation :
        ∃ hexagonMap : C(ProjectivePlaneTorus.CollarSource,
            ProjectivePlaneTorus.Surface),
          Topology.IsQuotientMap hexagonMap ∧
            ∀ x y,
              AdjunctionSpace.setoid
                  ProjectivePlaneTorus.standardGluing.attachingSubset
                  ProjectivePlaneTorus.standardGluing.attachingMap
                  (ProjectivePlaneTorus.collarComplementMap x)
                  (ProjectivePlaneTorus.collarComplementMap y) ↔
                hexagonMap x = hexagonMap y by
      obtain ⟨hexagonMap, hhexagonQuotient, hcollarKernel⟩ := hhexagonPresentation
      let gluingMap : C(ProjectivePlaneTorus.CollarSource,
          ProjectivePlaneTorus.standardGluing.GluedSurface) :=
        ProjectivePlaneTorus.standardGluingPresentation.comp
          ProjectivePlaneTorus.collarComplementMap
      -- Composing the collar presentation with the canonical adjunction quotient preserves
      -- quotientness.
      have hgluingQuotient : Topology.IsQuotientMap gluingMap := by
        exact ProjectivePlaneTorus.standardGluingPresentation_isQuotientMap.comp
          ProjectivePlaneTorus.collarComplementMap_isQuotientMap
      -- The canonical adjunction fiber formula converts the geometric collar kernel directly
      -- into equality under the hexagon presentation.
      have hkernel (x y : ProjectivePlaneTorus.CollarSource) :
          gluingMap x = gluingMap y ↔
            hexagonMap ((Homeomorph.refl _) x) =
              hexagonMap ((Homeomorph.refl _) y) := by
        dsimp only [gluingMap, ContinuousMap.comp_apply, Homeomorph.refl_apply, id_eq]
        exact (ProjectivePlaneTorus.standardGluingPresentation_eq_iff
          (ProjectivePlaneTorus.collarComplementMap x)
          (ProjectivePlaneTorus.collarComplementMap y)).trans (hcollarKernel x y)
      obtain ⟨homeomorphism, _⟩ :=
        CyclicPolygon.existsHomeomorphOfQuotientPresentations
          gluingMap hexagonMap hgluingQuotient hhexagonQuotient
            (Homeomorph.refl _) hkernel
      exact ⟨homeomorphism⟩
    -- TODO: construct the triangle--pentagon map from the two collar squares onto the hexagon.
    -- Rewrite its kernel goal with `ProjectivePlaneTorus.collarGluingKernel_iff`, then verify
    -- the resulting four explicit projective, torus, and cross-boundary cases.  All source
    -- landing, surjectivity, continuity, quotient, and kernel-normalization obligations are
    -- now discharged by the fixed collar presentation above.
    sorry
