module

public import Topology_Munkres_2000.Book.Definition_76_3
public import Topology_Munkres_2000.Book.Proposition_74_1
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

public section

open scoped Pointwise

namespace CyclicPolygon

/-- Helper for Proposition 76.2: the signed area of a vector with itself vanishes. -/
theorem signedArea_self (u : EuclideanSpace ℝ (Fin 2)) : signedArea u u = 0 := by
  -- Swap the based segment against itself; the second difference is zero.
  have hswap := signedArea_sub_swap u 0 u
  rw [sub_zero, sub_self, ← signedAreaRightCLM_apply] at hswap
  have hzero : signedArea (0 - u) 0 = 0 := by
    rw [← signedAreaRightCLM_apply, map_zero]
  rw [hzero, neg_zero] at hswap
  simpa only [signedAreaRightCLM_apply] using hswap

/-- Helper for Proposition 76.2: the filled region of every cyclic polygon has a
nonempty interior. -/
theorem interior_nonempty {n : ℕ} (poly : CyclicPolygon n) : poly.interior.Nonempty := by
  -- Three successive vertices are not collinear, so their affine span is the plane.
  let i₀ : Fin n := ⟨0, lt_of_lt_of_le (by norm_num) poly.three_le⟩
  let i₁ : Fin n := finRotate n i₀
  let i₂ : Fin n := finRotate n i₁
  let p₀ := poly.toPolygon.vertices i₀
  let p₁ := poly.toPolygon.vertices i₁
  let p₂ := poly.toPolygon.vertices i₂
  have hi₀i₁ : i₀ ≠ i₁ := by
    exact (finRotate_ne_self_of_two_le (poly.three_le.trans' (by omega)) i₀).symm
  have hi₀i₂ : i₀ ≠ i₂ := by
    exact (finRotate_sq_ne_self_of_three_le poly.three_le i₀).symm
  have hi₁i₂ : i₁ ≠ i₂ := by
    exact (finRotate_ne_self_of_two_le (poly.three_le.trans' (by omega)) i₁).symm
  have harea : signedArea (p₁ - p₀) (p₂ - p₀) ≠ 0 := by
    rw [show p₁ = poly.toPolygon.vertices (finRotate n i₀) by rfl]
    intro hzero
    rcases (poly.signedArea_edge_vertex_nonneg_and_eq_zero i₀ i₂).2.mp hzero with
      hi₂i₀ | hi₂i₁
    · exact hi₀i₂ hi₂i₀.symm
    · exact hi₁i₂ hi₂i₁.symm
  have hindependent : AffineIndependent ℝ ![p₀, p₁, p₂] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hcollinear
    have hp₂span : p₂ ∈ line[ℝ, p₀, p₁] := by
      apply hcollinear.mem_affineSpan_of_mem_of_ne
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
      · exact fun hp₀p₁ ↦ hi₀i₁ (poly.vertices_injective hp₀p₁)
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp₂span
    apply harea
    rw [← hr, AffineMap.lineMap_apply_module]
    have hline : (1 - r) • p₀ + r • p₁ - p₀ = r • (p₁ - p₀) := by
      module
    rw [hline, ← signedAreaRightCLM_apply, map_smul, signedAreaRightCLM_apply]
    rw [signedArea_self, smul_zero]
  have htripleSpan : affineSpan ℝ (Set.range ![p₀, p₁, p₂]) = ⊤ := by
    rw [hindependent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    norm_num
  have htripleSubset : Set.range ![p₀, p₁, p₂] ⊆ poly.region := by
    intro point hpoint
    obtain ⟨i, rfl⟩ := hpoint
    fin_cases i
    · exact poly.vertex_mem_region i₀
    · exact poly.vertex_mem_region i₁
    · exact poly.vertex_mem_region i₂
  have hregionSpan : affineSpan ℝ poly.region = ⊤ := by
    apply top_unique
    rw [← htripleSpan]
    exact affineSpan_mono ℝ htripleSubset
  -- Convexity converts full affine span into nonempty topological interior.
  rw [poly.interior_eq_topologicalInterior]
  exact (Convex.interior_nonempty_iff_affineSpan_eq_top poly.convex_region).2 hregionSpan

namespace DirectedEdge

/-- Helper for Proposition 76.2: the canonical filled-region edge point belongs to
the selected directed-edge subset. -/
theorem boundaryToRegion_edgePoint_mem_regionEdge {n : ℕ}
    {poly : CyclicPolygon n} (edge : poly.DirectedEdge) (s : unitInterval) :
    poly.boundaryToRegion (poly.edgePoint edge.index s) ∈ edge.regionEdge := by
  -- Forget the region subtype and use indexed-edge membership of the cyclic point.
  rw [edge.mem_regionEdge_iff, poly.boundaryToRegion_coe]
  exact poly.edgePoint_mem_edgeSet edge.index s

/-- Helper for Proposition 76.2: the cyclicly parameterized point on a directed edge,
viewed in the selected edge subset of the filled polygon. -/
noncomputable def regionEdgePoint {n : ℕ} {poly : CyclicPolygon n}
    (edge : poly.DirectedEdge)
    (s : unitInterval) : edge.regionEdge :=
  ⟨poly.boundaryToRegion (poly.edgePoint edge.index s),
    edge.boundaryToRegion_edgePoint_mem_regionEdge s⟩

/-- Helper for Proposition 76.2: forgetting selected-edge membership recovers the
canonical cyclic edge point in the filled polygon. -/
theorem regionEdgePoint_coe {n : ℕ} {poly : CyclicPolygon n}
    (edge : poly.DirectedEdge) (s : unitInterval) :
    (edge.regionEdgePoint s : poly.region) =
      poly.boundaryToRegion (poly.edgePoint edge.index s) := by
  -- The outer subtype stores only the indexed-edge membership proof.
  rfl

/-- Helper for Proposition 76.2: the selected-edge subtype does not change the
ambient point represented by the canonical cyclic parameter. -/
theorem segmentPoint_regionEdgePoint_coe {n : ℕ} {poly : CyclicPolygon n}
    (edge : poly.DirectedEdge) (s : unitInterval) :
    (edge.segmentPoint (edge.regionEdgePoint s) : EuclideanSpace ℝ (Fin 2)) =
      poly.edgePoint edge.index s := by
  -- Forget the segment and selected-edge subtypes through their public projections.
  rw [edge.segmentPoint_coe, edge.regionEdgePoint_coe,
    poly.boundaryToRegion_coe]

/-- Helper for Proposition 76.2: converting a cyclic edge parameter to the directed
segment parameter reverses it exactly when the directed edge points backwards. -/
theorem segmentPoint_regionEdgePoint {n : ℕ} {poly : CyclicPolygon n}
    (edge : poly.DirectedEdge) (s : unitInterval) :
    edge.segmentPoint (edge.regionEdgePoint s) =
      edge.segment.paramHomeomorph
        (if edge.forward then s else unitInterval.symm s) := by
  -- Compare ambient affine points; the reverse orientation uses parameter `1 - s`.
  apply Subtype.ext
  rw [edge.segmentPoint_regionEdgePoint_coe,
    OrientedSegment.paramHomeomorph_apply, poly.edgePoint_coe_eq_lineMap]
  cases hforward : edge.forward
  · rw [edge.segment_initial, edge.segment_final, edge.initial_eq, edge.final_eq]
    simp only [hforward, Bool.false_eq_true, ↓reduceIte,
      unitInterval.coe_symm_eq]
    rw [AffineMap.lineMap_apply_one_sub]
  · rw [edge.segment_initial, edge.segment_final, edge.initial_eq, edge.final_eq]
    simp only [hforward, ↓reduceIte]

end DirectedEdge

namespace EdgeGluing

/-- Helper for Proposition 76.2: the attaching map has the expected cyclic parameter;
equal directed orientations preserve the parameter and opposite ones reverse it. -/
theorem attachingMap_regionEdgePoint {m n : ℕ} {left : CyclicPolygon m}
    {right : CyclicPolygon n} (gluing : EdgeGluing left right) (s : unitInterval) :
    gluing.attachingMap (gluing.leftEdge.regionEdgePoint s) =
      right.boundaryToRegion
        (right.edgePoint gluing.rightEdge.index
          (if gluing.leftEdge.forward = gluing.rightEdge.forward then s
            else unitInterval.symm s)) := by
  -- The positive segment homeomorphism preserves its directed parameter.
  apply Subtype.ext
  rw [gluing.attachingMap_apply,
    gluing.leftEdge.segmentPoint_regionEdgePoint,
    OrientedSegment.positiveHomeomorph_apply,
    OrientedSegment.paramHomeomorph_apply, right.boundaryToRegion_coe,
    right.edgePoint_coe_eq_lineMap]
  -- Normalize the four direction choices at the ambient affine layer.
  cases hleft : gluing.leftEdge.forward <;>
    cases hright : gluing.rightEdge.forward
  · rw [gluing.rightEdge.segment_initial, gluing.rightEdge.segment_final,
      gluing.rightEdge.initial_eq, gluing.rightEdge.final_eq]
    simp only [hleft, hright, Bool.false_eq_true, ↓reduceIte,
      unitInterval.coe_symm_eq]
    rw [AffineMap.lineMap_apply_one_sub]
  · rw [gluing.rightEdge.segment_initial, gluing.rightEdge.segment_final,
      gluing.rightEdge.initial_eq, gluing.rightEdge.final_eq]
    simp only [hleft, hright, Bool.false_eq_true, ↓reduceIte,
      unitInterval.coe_symm_eq]
  · rw [gluing.rightEdge.segment_initial, gluing.rightEdge.segment_final,
      gluing.rightEdge.initial_eq, gluing.rightEdge.final_eq]
    simp [hleft, hright, unitInterval.coe_symm_eq]
  · rw [gluing.rightEdge.segment_initial, gluing.rightEdge.segment_final,
      gluing.rightEdge.initial_eq, gluing.rightEdge.final_eq]
    simp only [hleft, hright, ↓reduceIte]

/-- Helper for Proposition 76.2: a left-region comparison that agrees with the
attaching map sends every selected cyclic edge parameter to the same parameter on
the replacement polygon. -/
theorem mapsAttachingEdgePoint_of_agreesWithAttachingMap {m n : ℕ}
    {left : CyclicPolygon m} {right : CyclicPolygon n}
    (gluing : EdgeGluing left right) (replacement : CyclicPolygon m)
    (leftHomeomorph : left.region ≃ₜ replacement.region)
    (hvertices : ∀ i : Fin m,
      (leftHomeomorph (left.vertexPoint i) : EuclideanSpace ℝ (Fin 2)) =
        replacement.vertexPoint i)
    (hattaching : ∀ x : gluing.attachingSubset,
      (leftHomeomorph x : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap x)
    (h_oppositeOrientation :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (s : unitInterval) :
    leftHomeomorph (gluing.leftEdge.regionEdgePoint s) =
      replacement.boundaryToRegion
        (replacement.edgePoint gluing.leftEdge.index s) := by
  -- Compute the attaching map at the two endpoints to identify the replacement edge.
  have hattachZero := gluing.attachingMap_regionEdgePoint (0 : unitInterval)
  have hattachOne := gluing.attachingMap_regionEdgePoint (1 : unitInterval)
  rw [if_neg h_oppositeOrientation, unitInterval.symm_zero,
    right.boundaryToRegion_edgePoint_one] at hattachZero
  rw [if_neg h_oppositeOrientation, unitInterval.symm_one,
    right.boundaryToRegion_edgePoint_zero] at hattachOne
  have hleftZero :
      (gluing.leftEdge.regionEdgePoint 0 : left.region) =
        left.vertexPoint gluing.leftEdge.index := by
    rw [gluing.leftEdge.regionEdgePoint_coe,
      left.boundaryToRegion_edgePoint_zero]
  have hleftOne :
      (gluing.leftEdge.regionEdgePoint 1 : left.region) =
        left.vertexPoint (finRotate m gluing.leftEdge.index) := by
    rw [gluing.leftEdge.regionEdgePoint_coe,
      left.boundaryToRegion_edgePoint_one]
  have hinitial :
      replacement.toPolygon.vertices gluing.leftEdge.index =
        right.toPolygon.vertices (finRotate n gluing.rightEdge.index) := by
    -- The left initial endpoint is pasted to the right terminal endpoint.
    calc
      replacement.toPolygon.vertices gluing.leftEdge.index =
          (replacement.vertexPoint gluing.leftEdge.index :
            EuclideanSpace ℝ (Fin 2)) :=
        (replacement.vertexPoint_coe gluing.leftEdge.index).symm
      _ =
          (leftHomeomorph (left.vertexPoint gluing.leftEdge.index) :
            EuclideanSpace ℝ (Fin 2)) := (hvertices gluing.leftEdge.index).symm
      _ = (leftHomeomorph (gluing.leftEdge.regionEdgePoint 0) :
            EuclideanSpace ℝ (Fin 2)) := congrArg
              (fun x : left.region ↦
                (leftHomeomorph x : EuclideanSpace ℝ (Fin 2))) hleftZero.symm
      _ = (gluing.attachingMap (gluing.leftEdge.regionEdgePoint 0) :
            EuclideanSpace ℝ (Fin 2)) :=
        hattaching (gluing.leftEdge.regionEdgePoint 0)
      _ = right.toPolygon.vertices (finRotate n gluing.rightEdge.index) :=
        (congrArg Subtype.val hattachZero).trans
          (right.vertexPoint_coe (finRotate n gluing.rightEdge.index))
  have hfinal :
      replacement.toPolygon.vertices (finRotate m gluing.leftEdge.index) =
        right.toPolygon.vertices gluing.rightEdge.index := by
    -- The left terminal endpoint is pasted to the right initial endpoint.
    calc
      replacement.toPolygon.vertices (finRotate m gluing.leftEdge.index) =
          (replacement.vertexPoint (finRotate m gluing.leftEdge.index) :
            EuclideanSpace ℝ (Fin 2)) :=
        (replacement.vertexPoint_coe (finRotate m gluing.leftEdge.index)).symm
      _ =
          (leftHomeomorph (left.vertexPoint (finRotate m gluing.leftEdge.index)) :
            EuclideanSpace ℝ (Fin 2)) :=
        (hvertices (finRotate m gluing.leftEdge.index)).symm
      _ = (leftHomeomorph (gluing.leftEdge.regionEdgePoint 1) :
            EuclideanSpace ℝ (Fin 2)) := congrArg
              (fun x : left.region ↦
                (leftHomeomorph x : EuclideanSpace ℝ (Fin 2))) hleftOne.symm
      _ = (gluing.attachingMap (gluing.leftEdge.regionEdgePoint 1) :
            EuclideanSpace ℝ (Fin 2)) :=
        hattaching (gluing.leftEdge.regionEdgePoint 1)
      _ = right.toPolygon.vertices gluing.rightEdge.index :=
        (congrArg Subtype.val hattachOne).trans
          (right.vertexPoint_coe gluing.rightEdge.index)
  -- Agreement with the attaching map and affine reversal now identify every parameter.
  apply Subtype.ext
  calc
    (leftHomeomorph (gluing.leftEdge.regionEdgePoint s) :
        EuclideanSpace ℝ (Fin 2)) =
        (gluing.attachingMap (gluing.leftEdge.regionEdgePoint s) :
          EuclideanSpace ℝ (Fin 2)) :=
      hattaching (gluing.leftEdge.regionEdgePoint s)
    _ = (right.boundaryToRegion
          (right.edgePoint gluing.rightEdge.index (unitInterval.symm s)) :
            right.region) := by
      exact congrArg Subtype.val
        (by simpa only [if_neg h_oppositeOrientation] using
          gluing.attachingMap_regionEdgePoint s)
    _ = (replacement.boundaryToRegion
          (replacement.edgePoint gluing.leftEdge.index s) : replacement.region) := by
      rw [right.boundaryToRegion_coe, right.edgePoint_coe_eq_lineMap,
        replacement.boundaryToRegion_coe, replacement.edgePoint_coe_eq_lineMap,
        ← hinitial, ← hfinal, unitInterval.coe_symm_eq]
      rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      module

end EdgeGluing

/-- Helper for Proposition 76.2: the final point of a radial segment is its boundary
endpoint, viewed in the filled region. -/
theorem radialPoint_one {n : ℕ} (poly : CyclicPolygon n) (p : poly.interior)
    (x : poly.boundary) : poly.radialPoint p x 1 = poly.boundaryToRegion x := by
  -- Evaluate the affine radial parameterization at its terminal parameter.
  apply Subtype.ext
  rw [poly.radialPoint_coe_eq_lineMap, poly.boundaryToRegion_coe,
    AffineMap.lineMap_apply_module]
  simp only [unitInterval_coe_one, sub_self, zero_smul, one_smul, zero_add]

/-- Helper for Proposition 76.2: equally indexed cyclic polygons admit a filled-region
homeomorphism preserving the affine parameter on every boundary edge. -/
theorem existsRegionHomeomorphPreservingEdgeParameters {n : ℕ}
    (left right : CyclicPolygon n) :
    ∃ H : left.region ≃ₜ right.region, ∀ (i : Fin n) (s : unitInterval),
      H (left.boundaryToRegion (left.edgePoint i s)) =
        right.boundaryToRegion (right.edgePoint i s) := by
  -- Choose interior base points and radially extend the edge-preserving boundary map.
  classical
  let p : left.interior := Classical.choice left.interior_nonempty.to_subtype
  let q : right.interior := Classical.choice right.interior_nonempty.to_subtype
  obtain ⟨h, hedge, hextension⟩ :=
    existsBoundaryHomeomorphWithRadialExtension left right
  obtain ⟨H, hH⟩ := hextension p q
  refine ⟨H, ?_⟩
  intro i s
  -- Express each boundary point as the endpoint of its radial segment.
  rw [← left.radialPoint_one p (left.edgePoint i s)]
  rw [hH.map_radialPoint, hedge.map_edgePoint]
  exact right.radialPoint_one q (right.edgePoint i s)

/-- Helper for Proposition 76.2: every point on a polygon edge is the canonical
edge point for a unique affine parameter, viewed inside the filled region. -/
theorem exists_boundaryToRegion_edgePoint_eq {n : ℕ} (poly : CyclicPolygon n)
    (i : Fin n) (x : poly.region)
    (hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ poly.edgeSet i) :
    ∃ s : unitInterval, poly.boundaryToRegion (poly.edgePoint i s) = x := by
  rw [poly.edgeSet_def] at hx
  unfold Polygon.edgeSet at hx
  rw [affineSegment_eq_segment, segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, htx⟩ := hx
  let s : unitInterval := ⟨t, ht⟩
  refine ⟨s, ?_⟩
  -- The image witness is exactly the canonical affine edge parameter.
  apply Subtype.ext
  rw [poly.boundaryToRegion_coe, poly.edgePoint_coe_eq_lineMap]
  exact htx

/-- Helper for Proposition 76.2: two maps that agree on the canonical affine
parameterization of one polygon edge agree at every point of that edge. -/
theorem eq_on_edgeSet_of_eq_boundaryToRegion_edgePoint {n : ℕ} {β : Type*}
    (poly : CyclicPolygon n) (i : Fin n) (F G : poly.region → β)
    (hparam : ∀ s : unitInterval,
      F (poly.boundaryToRegion (poly.edgePoint i s)) =
        G (poly.boundaryToRegion (poly.edgePoint i s)))
    (x : poly.region) (hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ poly.edgeSet i) :
    F x = G x := by
  obtain ⟨s, hs⟩ := poly.exists_boundaryToRegion_edgePoint_eq i x hx
  -- Rewrite the arbitrary edge point to its canonical parameterized representative.
  rw [← hs]
  exact hparam s

end CyclicPolygon

namespace CyclicPolygon.EdgeGluing

/-- Helper for Proposition 76.2: replacing the left comparison by another
homeomorphism that agrees on the attaching edge can be absorbed by an automorphism
of the adjunction-space realization. -/
theorem existsCorrectedRealizationHomeomorph {m n : ℕ}
    {left : CyclicPolygon m} {right : CyclicPolygon n}
    (gluing : EdgeGluing left right) {k : ℕ} (replacement : CyclicPolygon m)
    (combined : CyclicPolygon k)
    (oldLeft newLeft : left.region ≃ₜ replacement.region)
    (realization : gluing.Realization ≃ₜ combined.region)
    (hagree : ∀ a : gluing.attachingSubset, oldLeft a = newLeft a)
    (hleft : ∀ x : left.region,
      (realization (gluing.includeLeft x) : EuclideanSpace ℝ (Fin 2)) = oldLeft x)
    (hright : ∀ y : right.region,
      (realization (gluing.includeRight y) : EuclideanSpace ℝ (Fin 2)) = y) :
    ∃ corrected : gluing.Realization ≃ₜ combined.region,
      (∀ x : left.region,
        (corrected (gluing.includeLeft x) : EuclideanSpace ℝ (Fin 2)) = newLeft x) ∧
        ∀ y : right.region,
          (corrected (gluing.includeRight y) : EuclideanSpace ℝ (Fin 2)) = y := by
  let correction : left.region ≃ₜ left.region := newLeft.trans oldLeft.symm
  have hfix : ∀ a : gluing.attachingSubset, correction a = a := by
    intro a
    -- Agreement on the attaching edge makes the comparison change pointwise stationary.
    apply oldLeft.injective
    calc
      oldLeft (correction a) = newLeft a := oldLeft.apply_symm_apply (newLeft a)
      _ = oldLeft a := (hagree a).symm
  obtain ⟨E, hEleft, hEright⟩ :=
    AdjunctionSpace.existsSelfHomeomorphOfFixesAttaching
      gluing.attachingSubset gluing.attachingMap correction hfix
  refine ⟨E.trans realization, ?_, ?_⟩
  · intro x
    -- Precomposition by `E` changes exactly the left comparison.
    calc
      ((E.trans realization) (gluing.includeLeft x) : EuclideanSpace ℝ (Fin 2)) =
          (realization (E (AdjunctionSpace.includeX gluing.attachingSubset
            gluing.attachingMap x)) : EuclideanSpace ℝ (Fin 2)) :=
        congrArg (fun q : gluing.Realization ↦
          (realization (E q) : EuclideanSpace ℝ (Fin 2)))
          (gluing.includeLeft_eq_includeX x)
      _ = (realization (AdjunctionSpace.includeX gluing.attachingSubset
          gluing.attachingMap (correction x)) : EuclideanSpace ℝ (Fin 2)) :=
        congrArg (fun q : gluing.Realization ↦
          (realization q : EuclideanSpace ℝ (Fin 2))) (hEleft x)
      _ = (realization (gluing.includeLeft (correction x)) :
          EuclideanSpace ℝ (Fin 2)) :=
        congrArg (fun q : gluing.Realization ↦
          (realization q : EuclideanSpace ℝ (Fin 2)))
          (gluing.includeLeft_eq_includeX (correction x)).symm
      _ = oldLeft (correction x) := hleft (correction x)
      _ = newLeft x := congrArg Subtype.val (oldLeft.apply_symm_apply (newLeft x))
  · intro y
    -- The correction is the identity on the right summand.
    calc
      ((E.trans realization) (gluing.includeRight y) : EuclideanSpace ℝ (Fin 2)) =
          (realization (E (AdjunctionSpace.includeY gluing.attachingSubset
            gluing.attachingMap y)) : EuclideanSpace ℝ (Fin 2)) :=
        congrArg (fun q : gluing.Realization ↦
          (realization (E q) : EuclideanSpace ℝ (Fin 2)))
          (gluing.includeRight_eq_includeY y)
      _ = (realization (AdjunctionSpace.includeY gluing.attachingSubset
          gluing.attachingMap y) : EuclideanSpace ℝ (Fin 2)) :=
        congrArg (fun q : gluing.Realization ↦
          (realization q : EuclideanSpace ℝ (Fin 2))) (hEright y)
      _ = (realization (gluing.includeRight y) : EuclideanSpace ℝ (Fin 2)) :=
        congrArg (fun q : gluing.Realization ↦
          (realization q : EuclideanSpace ℝ (Fin 2)))
          (gluing.includeRight_eq_includeY y).symm
      _ = y := hright y

end CyclicPolygon.EdgeGluing
