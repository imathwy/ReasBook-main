module

public import Topology_Munkres_2000.Book.Example_74_8.StandardGluing
import all Topology_Munkres_2000.Book.Example_22_5.Torus

public section

namespace ProjectivePlaneTorus

noncomputable section

/-- Helper for Example 74.8: the centered model-plane representative of a point in the
fundamental unit square. -/
noncomputable def torusFundamentalModelPoint
    (point : unitInterval × unitInterval) : ModelPlane :=
  torusModelCoordinates.symm
    (((point.1 : ℝ) - 1 / 2), ((point.2 : ℝ) - 1 / 2))

/-- Helper for Example 74.8: the model point associated to a square point has the prescribed
centered torus coordinates. -/
lemma torusFundamentalModelPoint_coordinates
    (point : unitInterval × unitInterval) :
    torusModelCoordinates (torusFundamentalModelPoint point) =
      (((point.1 : ℝ) - 1 / 2), ((point.2 : ℝ) - 1 / 2)) := by
  -- Applying the coordinate homeomorphism cancels its inverse in the definition.
  exact torusModelCoordinates.apply_symm_apply _

/-- Helper for Example 74.8: the model-point coordinates of every fundamental-square point
have product norm at most one half. -/
lemma torusFundamentalModelPoint_coordinateNorm_le_half
    (point : unitInterval × unitInterval) :
    ‖torusModelCoordinates (torusFundamentalModelPoint point)‖ ≤ (1 / 2 : ℝ) := by
  -- Both centered interval coordinates lie between minus and plus one half.
  rw [torusFundamentalModelPoint_coordinates, Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs]
    apply (abs_le).mpr
    constructor
    · linarith [unitInterval.nonneg point.1]
    · linarith [unitInterval.le_one point.1]
  · rw [Real.norm_eq_abs]
    apply (abs_le).mpr
    constructor
    · linarith [unitInterval.nonneg point.2]
    · linarith [unitInterval.le_one point.2]

/-- Helper for Example 74.8: centered model-plane representatives determine their
fundamental-square points uniquely. -/
lemma torusFundamentalModelPoint_injective :
    Function.Injective torusFundamentalModelPoint := by
  intro x y hxy
  -- Apply the coordinate homeomorphism, then cancel the common centering translation.
  have hcoordinates := congrArg torusModelCoordinates hxy
  rw [torusFundamentalModelPoint_coordinates,
    torusFundamentalModelPoint_coordinates] at hcoordinates
  apply Prod.ext
  · apply Subtype.ext
    have hfirst := congrArg Prod.fst hcoordinates
    dsimp only at hfirst ⊢
    linarith
  · apply Subtype.ext
    have hsecond := congrArg Prod.snd hcoordinates
    dsimp only at hsecond ⊢
    linarith

/-- Helper for Example 74.8: the centered fundamental square maps to the torus by reducing
both translated coordinates modulo one. -/
def torusFundamentalMap
    (point : unitInterval × unitInterval) : UnitAddCircle × UnitAddCircle :=
  ((((point.1 : ℝ) - 1 / 2 : ℝ) : UnitAddCircle),
    (((point.2 : ℝ) - 1 / 2 : ℝ) : UnitAddCircle))

/-- Helper for Example 74.8: the centered fundamental-square map is continuous. -/
lemma continuous_torusFundamentalMap : Continuous torusFundamentalMap := by
  -- Each component subtracts a constant before applying the real-to-circle quotient.
  apply Continuous.prodMk
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_subtype_val.comp continuous_fst).sub continuous_const)
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const)

/-- Helper for Example 74.8: the centered square formula is the global torus model evaluated
at its canonical model-plane representative. -/
lemma torusFundamentalMap_eq_model (point : unitInterval × unitInterval) :
    torusFundamentalMap point = torusModelMap (torusFundamentalModelPoint point) := by
  -- The coordinate homeomorphism cancels its inverse, leaving the two centered coordinates.
  rw [torusModelMap_apply, torusFundamentalModelPoint,
    Homeomorph.apply_symm_apply]
  rfl

/-- Helper for Example 74.8: expose the coordinate formula of the canonical square-to-torus
map at the interface needed for the centered translation. -/
lemma torusSquare_toTorus_apply (point : unitInterval × unitInterval) :
    TorusSquare.toTorus point =
      ((point.1 : UnitAddCircle), (point.2 : UnitAddCircle)) := by
  -- The canonical quotient map is coordinatewise coercion to the additive circle.
  rfl

/-- Helper for Example 74.8: translation by minus one half in each circle coordinate. -/
noncomputable def torusFundamentalTranslation :
    UnitAddCircle × UnitAddCircle ≃ₜ UnitAddCircle × UnitAddCircle :=
  (Homeomorph.subRight (((1 / 2 : ℝ) : UnitAddCircle))).prodCongr
    (Homeomorph.subRight (((1 / 2 : ℝ) : UnitAddCircle)))

/-- Helper for Example 74.8: the centered map is the canonical square quotient followed by
the product translation. -/
lemma torusFundamentalMap_eq_translation (point : unitInterval × unitInterval) :
    torusFundamentalMap point =
      torusFundamentalTranslation (TorusSquare.toTorus point) := by
  -- Coercion from the reals to the additive circle preserves subtraction.
  rw [torusFundamentalMap, torusFundamentalTranslation,
    torusSquare_toTorus_apply]
  exact Prod.ext (AddCircle.coe_sub (1 : ℝ) (point.1 : ℝ) (1 / 2 : ℝ))
    (AddCircle.coe_sub (1 : ℝ) (point.2 : ℝ) (1 / 2 : ℝ))

/-- Helper for Example 74.8: the centered fundamental square is a quotient presentation of
the torus. -/
lemma torusFundamentalMap_isQuotientMap :
    Topology.IsQuotientMap torusFundamentalMap := by
  -- Postcomposition of the canonical square quotient by a homeomorphism remains quotient.
  have hfactor : torusFundamentalMap =
      torusFundamentalTranslation ∘ TorusSquare.toTorus :=
    funext torusFundamentalMap_eq_translation
  rw [hfactor]
  exact torusFundamentalTranslation.isQuotientMap.comp
    TorusSquare.toTorus_isQuotientMap

/-- Helper for Example 74.8: the exact fibers of the centered presentation are the canonical
opposite-edge identifications of the unit square. -/
lemma torusFundamentalMap_eq_iff (x y : unitInterval × unitInterval) :
    torusFundamentalMap x = torusFundamentalMap y ↔ TorusSquare.identified x y := by
  -- Cancel the common target translation and return to the defining kernel of `toTorus`.
  rw [torusFundamentalMap_eq_translation, torusFundamentalMap_eq_translation,
    torusFundamentalTranslation.injective.eq_iff]
  constructor
  · intro hxy
    -- The defining setoid is the kernel of the canonical square map.
    exact hxy
  · intro hidentified
    -- Conversely, a kernel witness is exactly equality under the canonical square map.
    change TorusSquare.toTorus x = TorusSquare.toTorus y at hidentified
    exact hidentified

/-- Helper for Example 74.8: a centered fundamental-square point lies in the chosen torus
disc exactly when its model-plane representative has norm less than one half. -/
lemma torusFundamentalMap_mem_rightDeletedDisc_iff
    (point : unitInterval × unitInterval) :
    torusFundamentalMap point ∈ standardGluing.rightDeletedDisc ↔
      ‖torusFundamentalModelPoint point‖ < (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨coordinate, hcoordinateBall, hcoordinateImage⟩
    -- A deleted-disc representative has both scaled coordinates strictly between the
    -- centered square endpoints.
    have hcoordinateNorm : ‖coordinate‖ < (1 / 2 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hcoordinateBall
    have hcoordinateZeroAbs : |coordinate 0| ≤ ‖coordinate‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le coordinate 0
    have hcoordinateOneAbs : |coordinate 1| ≤ ‖coordinate‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le coordinate 1
    rw [abs_le] at hcoordinateZeroAbs hcoordinateOneAbs
    have hzeroLower : 0 ≤ (1 / 4 : ℝ) * coordinate 0 + 1 / 2 := by
      nlinarith
    have hzeroUpper : (1 / 4 : ℝ) * coordinate 0 + 1 / 2 ≤ 1 := by
      nlinarith
    have honeLower : 0 ≤ (1 / 4 : ℝ) * coordinate 1 + 1 / 2 := by
      nlinarith
    have honeUpper : (1 / 4 : ℝ) * coordinate 1 + 1 / 2 ≤ 1 := by
      nlinarith
    have hzeroMem : (1 / 4 : ℝ) * coordinate 0 + 1 / 2 ∈
        Set.Icc (0 : ℝ) 1 := ⟨hzeroLower, hzeroUpper⟩
    have honeMem : (1 / 4 : ℝ) * coordinate 1 + 1 / 2 ∈
        Set.Icc (0 : ℝ) 1 := ⟨honeLower, honeUpper⟩
    let squarePoint : unitInterval × unitInterval :=
      (⟨(1 / 4 : ℝ) * coordinate 0 + 1 / 2, hzeroMem⟩,
        ⟨(1 / 4 : ℝ) * coordinate 1 + 1 / 2, honeMem⟩)
    have hsquarePointModel : torusFundamentalModelPoint squarePoint = coordinate := by
      -- The constructed square point has exactly the scaled coordinates of `coordinate`.
      apply torusModelCoordinates.injective
      rw [torusFundamentalModelPoint_coordinates, torusModelCoordinates_apply]
      apply Prod.ext
      · dsimp only [squarePoint]
        ring
      · dsimp only [squarePoint]
        ring
    have hsameMap : torusFundamentalMap point =
        torusFundamentalMap squarePoint := by
      -- Compare both square points through the global torus model and the chart witness.
      calc
        torusFundamentalMap point = standardGluing.rightChart coordinate :=
          hcoordinateImage.symm
        _ = torusModelMap coordinate := standardGluing_rightChart_apply coordinate
        _ = torusModelMap (torusFundamentalModelPoint squarePoint) := by
          rw [hsquarePointModel]
        _ = torusFundamentalMap squarePoint :=
          (torusFundamentalMap_eq_model squarePoint).symm
    have hidentified : TorusSquare.identified point squarePoint :=
      (torusFundamentalMap_eq_iff point squarePoint).mp hsameMap
    have hcoordinateRelations :=
      (TorusSquare.identified_iff point squarePoint).mp hidentified
    have hsquarePointZero_ne_zero : squarePoint.1 ≠ 0 := by
      apply ne_of_gt
      change (0 : ℝ) < (1 / 4 : ℝ) * coordinate 0 + 1 / 2
      nlinarith
    have hsquarePointZero_ne_one : squarePoint.1 ≠ 1 := by
      apply ne_of_lt
      change (1 / 4 : ℝ) * coordinate 0 + 1 / 2 < 1
      nlinarith
    have hsquarePointOne_ne_zero : squarePoint.2 ≠ 0 := by
      apply ne_of_gt
      change (0 : ℝ) < (1 / 4 : ℝ) * coordinate 1 + 1 / 2
      nlinarith
    have hsquarePointOne_ne_one : squarePoint.2 ≠ 1 := by
      apply ne_of_lt
      change (1 / 4 : ℝ) * coordinate 1 + 1 / 2 < 1
      nlinarith
    have hfirst : point.1 = squarePoint.1 := by
      -- Since the constructed coordinate is strictly interior, endpoint identification
      -- reduces to ordinary equality.
      rcases (unitInterval.endpointSetoid_iff point.1 squarePoint.1).mp
          hcoordinateRelations.1 with hsame | hzeroOne | honeZero
      · exact hsame
      · exact (hsquarePointZero_ne_one hzeroOne.2).elim
      · exact (hsquarePointZero_ne_zero honeZero.2).elim
    have hsecond : point.2 = squarePoint.2 := by
      -- Apply the same strict-interior argument to the second coordinate.
      rcases (unitInterval.endpointSetoid_iff point.2 squarePoint.2).mp
          hcoordinateRelations.2 with hsame | hzeroOne | honeZero
      · exact hsame
      · exact (hsquarePointOne_ne_one hzeroOne.2).elim
      · exact (hsquarePointOne_ne_zero honeZero.2).elim
    have hpoint : point = squarePoint := Prod.ext hfirst hsecond
    -- The model point is therefore the original deleted-disc representative.
    rw [hpoint, hsquarePointModel]
    exact hcoordinateNorm
  · intro hpointNorm
    -- A model point of norm below one half is itself a chart witness for disc membership.
    refine ⟨torusFundamentalModelPoint point, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right] using hpointNorm
    · rw [standardGluing_rightChart_apply]
      exact (torusFundamentalMap_eq_model point).symm

/-- Helper for Example 74.8: the part of the centered fundamental square mapping outside the
chosen deleted torus disc. -/
abbrev TorusFundamentalComplementSource :=
  torusFundamentalMap ⁻¹' standardGluing.rightDeletedDiscᶜ

/-- Helper for Example 74.8: membership in the centered fundamental-square complement is
equivalent to the model-plane norm being at least one half. -/
lemma torusFundamentalComplement_iff_norm
    (point : unitInterval × unitInterval) :
    point ∈ TorusFundamentalComplementSource ↔
      (1 / 2 : ℝ) ≤ ‖torusFundamentalModelPoint point‖ := by
  -- Negate the strict deleted-disc normal form proved above.
  change torusFundamentalMap point ∉ standardGluing.rightDeletedDisc ↔ _
  rw [torusFundamentalMap_mem_rightDeletedDisc_iff, not_lt]

/-- Helper for Example 74.8: restrict the centered fundamental-square presentation to the
chosen torus complement. -/
noncomputable def torusFundamentalComplementMap :
    TorusFundamentalComplementSource → standardGluing.RightComplement :=
  standardGluing.rightDeletedDiscᶜ.restrictPreimage torusFundamentalMap

/-- Helper for Example 74.8: the restricted fundamental-square presentation preserves its
underlying torus value. -/
lemma torusFundamentalComplementMap_coe (point : TorusFundamentalComplementSource) :
    (torusFundamentalComplementMap point : UnitAddCircle × UnitAddCircle) =
      torusFundamentalMap point := by
  -- Restricting the domain and codomain does not change the underlying map.
  rfl

/-- Helper for Example 74.8: the centered fundamental-square restriction is a quotient
presentation of the chosen deleted-disc complement. -/
lemma torusFundamentalComplementMap_isQuotientMap :
    Topology.IsQuotientMap torusFundamentalComplementMap := by
  -- The deleted chart disc is open because its smaller coordinate ball lies in the chart.
  have hopen : IsOpen standardGluing.rightDeletedDisc := by
    apply standardGluing.rightChart.isOpen_image_of_subset_source Metric.isOpen_ball
    rw [standardGluing.rightSource]
    exact Metric.ball_subset_ball (by norm_num)
  -- Hence the restricted square is closed in the compact unit square.
  have hclosed : IsClosed TorusFundamentalComplementSource :=
    hopen.isClosed_compl.preimage torusFundamentalMap_isQuotientMap.continuous
  -- Local instance justification: the compact-source quotient criterion needs the compactness
  -- instance supplied by this just-proved closed-subspace fact.
  letI : CompactSpace TorusFundamentalComplementSource :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  -- Restrict surjectivity and continuity, then use compact-to-Hausdorff quotientness.
  exact Topology.IsQuotientMap.of_surjective_continuous
    (torusFundamentalMap_isQuotientMap.surjective.restrictPreimage _)
    torusFundamentalMap_isQuotientMap.continuous.restrictPreimage

/-- Helper for Example 74.8: restriction to the torus complement does not change the
canonical opposite-edge fiber relation. -/
lemma torusFundamentalComplementMap_eq_iff
    (x y : TorusFundamentalComplementSource) :
    torusFundamentalComplementMap x = torusFundamentalComplementMap y ↔
      TorusSquare.identified x.1 y.1 := by
  constructor
  · intro hxy
    -- Forget the complement subtype and invoke the global square kernel theorem.
    have hambient := congrArg Subtype.val hxy
    rw [torusFundamentalComplementMap_coe,
      torusFundamentalComplementMap_coe] at hambient
    exact (torusFundamentalMap_eq_iff x.1 y.1).mp hambient
  · intro hidentified
    -- Equal global values give equal complement points by subtype extensionality.
    apply Subtype.ext
    rw [torusFundamentalComplementMap_coe,
      torusFundamentalComplementMap_coe]
    exact (torusFundamentalMap_eq_iff x.1 y.1).mpr hidentified

end

end ProjectivePlaneTorus
