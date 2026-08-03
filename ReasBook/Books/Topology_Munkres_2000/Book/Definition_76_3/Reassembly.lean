module

public import Topology_Munkres_2000.Book.Algorithm_76_1.EdgeGluing
public import Topology_Munkres_2000.Book.Definition_74_1.CyclicPolygon
public import Topology_Munkres_2000.Book.Definition_76_3.Insertion
public import Topology_Munkres_2000.Book.Proposition_74_1
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

public section

open Set

namespace CyclicPolygon

noncomputable section

/-- Helper for Definition 76.3: a cyclic presentation can align any source edge
with any target index while preserving its geometric data. -/
theorem existsEdgeAlignedRotateFrom {n : ℕ} (poly : CyclicPolygon n)
    (source target : Fin n) :
    ∃ reindexed : CyclicPolygon n,
      reindexed.center = poly.center ∧
      reindexed.radius = poly.radius ∧
      reindexed.region = poly.region ∧
      reindexed.toPolygon.vertices target = poly.toPolygon.vertices source ∧
      reindexed.toPolygon.vertices (finRotate n target) =
        poly.toPolygon.vertices (finRotate n source) ∧
      reindexed.edgeSet target = poly.edgeSet source := by
  classical
  -- Translation by the target index is a permutation of the finite cyclic index set.
  have hinjective : Function.Injective (fun start : Fin n ↦ rotatedIndex start target) := by
    intro first second heq
    have hadd : first + target = second + target := by
      simpa only [rotatedIndex_eq_add] using heq
    exact add_right_cancel hadd
  obtain ⟨start, htarget⟩ :=
    Finite.surjective_of_injective hinjective source
  have htarget' : rotatedIndex start target = source := by
    simpa only using htarget
  have hsuccessor : rotatedIndex start (finRotate n target) =
      finRotate n source := by
    calc
      rotatedIndex start (finRotate n target) =
          finRotate n (rotatedIndex start target) :=
        rotatedIndex_finRotate start target
      _ = finRotate n source := congrArg (finRotate n) htarget'
  let reindexed := rotateFrom poly start
  have hvertex : reindexed.toPolygon.vertices target =
      poly.toPolygon.vertices source := by
    dsimp only [reindexed]
    rw [rotateFrom_vertices, htarget']
  have hnextVertex : reindexed.toPolygon.vertices (finRotate n target) =
      poly.toPolygon.vertices (finRotate n source) := by
    dsimp only [reindexed]
    rw [rotateFrom_vertices, hsuccessor]
  refine ⟨reindexed, ?_, ?_, ?_, hvertex, hnextVertex, ?_⟩
  · simpa only [reindexed] using rotateFrom_center poly start
  · simpa only [reindexed] using rotateFrom_radius poly start
  · simpa only [reindexed] using rotateFrom_region poly start
  · -- The distinguished edge follows from its two aligned endpoints.
    unfold edgeSet Polygon.edgeSet
    rw [hvertex, hnextVertex]

/-- Helper for Definition 76.3: the planar signed area of a vector with itself is zero. -/
theorem signedArea_self_eq_zero (u : EuclideanSpace ℝ (Fin 2)) : signedArea u u = 0 := by
  -- Antisymmetry against a zero-based segment reduces the determinant to its negation.
  have hswap := signedArea_sub_swap u 0 u
  rw [sub_zero, sub_self, ← signedAreaRightCLM_apply] at hswap
  have hzero : signedArea (0 - u) 0 = 0 := by
    rw [← signedAreaRightCLM_apply, map_zero]
  rw [hzero, neg_zero] at hswap
  simpa only [signedAreaRightCLM_apply] using hswap

/-- Helper for Definition 76.3: every cyclic polygonal region has nonempty interior. -/
theorem regionInterior_nonempty {n : ℕ} (poly : CyclicPolygon n) :
    poly.interior.Nonempty := by
  -- Three successive cyclic vertices have a nonzero determinant and span the plane.
  let i₀ : Fin n := ⟨0, lt_of_lt_of_le (by norm_num) poly.three_le⟩
  let i₁ : Fin n := finRotate n i₀
  let i₂ : Fin n := finRotate n i₁
  let p₀ := poly.toPolygon.vertices i₀
  let p₁ := poly.toPolygon.vertices i₁
  let p₂ := poly.toPolygon.vertices i₂
  have hi₀i₁ : i₀ ≠ i₁ :=
    (finRotate_ne_self_of_two_le (poly.three_le.trans' (by omega)) i₀).symm
  have hi₀i₂ : i₀ ≠ i₂ :=
    (finRotate_sq_ne_self_of_three_le poly.three_le i₀).symm
  have hi₁i₂ : i₁ ≠ i₂ :=
    (finRotate_ne_self_of_two_le (poly.three_le.trans' (by omega)) i₁).symm
  have harea : signedArea (p₁ - p₀) (p₂ - p₀) ≠ 0 := by
    have hp₁ : p₁ = poly.toPolygon.vertices (finRotate n i₀) := rfl
    rw [hp₁]
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
    rw [signedArea_self_eq_zero, smul_zero]
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
  -- Convexity turns full affine span into nonempty topological interior.
  rw [poly.interior_eq_topologicalInterior]
  exact (Convex.interior_nonempty_iff_affineSpan_eq_top poly.convex_region).2 hregionSpan

/-- Helper for Definition 76.3: every filled cyclic polygonal region is compact. -/
theorem region_isCompact {n : ℕ} (poly : CyclicPolygon n) : IsCompact poly.region := by
  -- The region is the convex hull of its finite vertex set.
  rw [poly.region_eq_convexHull]
  exact Set.finite_range poly.toPolygon.vertices |>.isCompact_convexHull ℝ

/-- Helper for Definition 76.3: the endpoint of a radial segment is its boundary point
viewed in the filled region. -/
theorem radialPoint_one_eq_boundaryToRegion {n : ℕ} (poly : CyclicPolygon n)
    (p : poly.interior) (x : poly.boundary) :
    poly.radialPoint p x 1 = poly.boundaryToRegion x := by
  -- Evaluate the affine radial parameter at its terminal endpoint.
  apply Subtype.ext
  rw [poly.radialPoint_coe_eq_lineMap, poly.boundaryToRegion_coe,
    AffineMap.lineMap_apply_module]
  simp only [unitInterval_coe_one, sub_self, zero_smul, one_smul, zero_add]

/-- Helper for Definition 76.3: equally indexed cyclic polygons admit a region
homeomorphism preserving every vertex and affine edge parameter. -/
theorem existsVertexAndEdgeParameterPreservingRegionHomeomorph {n : ℕ}
    (left right : CyclicPolygon n) :
    ∃ H : left.region ≃ₜ right.region,
      (∀ i : Fin n, H (left.vertexPoint i) = right.vertexPoint i) ∧
      ∀ (i : Fin n) (s : unitInterval),
        H (left.boundaryToRegion (left.edgePoint i s)) =
          right.boundaryToRegion (right.edgePoint i s) := by
  classical
  let p : left.interior := Classical.choice left.regionInterior_nonempty.to_subtype
  let q : right.interior := Classical.choice right.regionInterior_nonempty.to_subtype
  obtain ⟨h, hedge, hextension⟩ :=
    existsBoundaryHomeomorphWithRadialExtension left right
  obtain ⟨H, hH⟩ := hextension p q
  refine ⟨H, ?_, ?_⟩
  · intro i
    -- Vertices are parameter-zero edge points, so edge preservation fixes them.
    calc
      H (left.vertexPoint i) =
          H (left.boundaryToRegion (left.edgePoint i 0)) :=
        congrArg H (left.boundaryToRegion_edgePoint_zero i).symm
      _ = right.boundaryToRegion (right.edgePoint i 0) := by
        rw [← left.radialPoint_one_eq_boundaryToRegion p (left.edgePoint i 0)]
        rw [hH.map_radialPoint, hedge.map_edgePoint]
        exact right.radialPoint_one_eq_boundaryToRegion q (right.edgePoint i 0)
      _ = right.vertexPoint i := right.boundaryToRegion_edgePoint_zero i
  · intro i s
    -- Express the boundary point as the radial endpoint before applying the extension law.
    rw [← left.radialPoint_one_eq_boundaryToRegion p (left.edgePoint i s)]
    rw [hH.map_radialPoint, hedge.map_edgePoint]
    exact right.radialPoint_one_eq_boundaryToRegion q (right.edgePoint i s)

/-- Helper for Definition 76.3: every point of one cyclic edge has a canonical affine
parameter when viewed in the filled region. -/
theorem existsEdgePointParameter {n : ℕ} (poly : CyclicPolygon n) (i : Fin n)
    (x : poly.region) (hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ poly.edgeSet i) :
    ∃ s : unitInterval, poly.boundaryToRegion (poly.edgePoint i s) = x := by
  rw [poly.edgeSet_def] at hx
  unfold Polygon.edgeSet at hx
  rw [affineSegment_eq_segment, segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, htx⟩ := hx
  let s : unitInterval := ⟨t, ht⟩
  refine ⟨s, ?_⟩
  -- The segment-image witness is precisely the canonical cyclic parameterization.
  apply Subtype.ext
  rw [poly.boundaryToRegion_coe, poly.edgePoint_coe_eq_lineMap]
  exact htx

namespace DirectedEdge

/-- Helper for Definition 76.3: a cyclic edge parameter belongs to the selected
directed-edge subset. -/
theorem cyclicRegionPoint_mem {n : ℕ} {poly : CyclicPolygon n}
    (edge : poly.DirectedEdge) (s : unitInterval) :
    poly.boundaryToRegion (poly.edgePoint edge.index s) ∈ edge.regionEdge := by
  -- Forget the region subtype and use membership in the indexed cyclic edge.
  rw [edge.mem_regionEdge_iff, poly.boundaryToRegion_coe]
  exact poly.edgePoint_mem_edgeSet edge.index s

/-- Helper for Definition 76.3: the cyclicly parameterized point in a selected
directed edge. -/
noncomputable def cyclicRegionPoint {n : ℕ} {poly : CyclicPolygon n}
    (edge : poly.DirectedEdge) (s : unitInterval) : edge.regionEdge :=
  ⟨poly.boundaryToRegion (poly.edgePoint edge.index s), edge.cyclicRegionPoint_mem s⟩

/-- Helper for Definition 76.3: forgetting selected-edge membership recovers the
canonical filled-region edge point. -/
theorem cyclicRegionPoint_coe {n : ℕ} {poly : CyclicPolygon n}
    (edge : poly.DirectedEdge) (s : unitInterval) :
    (edge.cyclicRegionPoint s : poly.region) =
      poly.boundaryToRegion (poly.edgePoint edge.index s) := by
  -- The outer subtype changes only the edge-membership proof.
  rfl

/-- Helper for Definition 76.3: a selected cyclic edge parameter is the directed
segment parameter, reversed exactly for a backward edge. -/
theorem segmentPoint_cyclicRegionPoint {n : ℕ} {poly : CyclicPolygon n}
    (edge : poly.DirectedEdge) (s : unitInterval) :
    edge.segmentPoint (edge.cyclicRegionPoint s) =
      edge.segment.paramHomeomorph
        (if edge.forward then s else unitInterval.symm s) := by
  -- Compare ambient affine points and normalize the two orientation cases.
  apply Subtype.ext
  rw [edge.segmentPoint_coe, edge.cyclicRegionPoint_coe,
    poly.boundaryToRegion_coe, OrientedSegment.paramHomeomorph_apply,
    poly.edgePoint_coe_eq_lineMap]
  cases hforward : edge.forward
  · rw [edge.segment_initial, edge.segment_final, edge.initial_eq, edge.final_eq]
    simp only [hforward, Bool.false_eq_true, ↓reduceIte, unitInterval.coe_symm_eq]
    rw [AffineMap.lineMap_apply_one_sub]
  · rw [edge.segment_initial, edge.segment_final, edge.initial_eq, edge.final_eq]
    simp only [hforward, ↓reduceIte]

end DirectedEdge

end

end CyclicPolygon

namespace CyclicPolygon.Cut

noncomputable section

variable {n : ℕ}

/-- Helper for Definition 76.3: the regions on the two sides of a cyclic diagonal
meet exactly in their common diagonal edge. -/
theorem regionsInterEqDiagonal (poly : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1) :
    (left poly k hk₁).region ∩ (right poly k hk₁ hk₂).region =
      (left poly k hk₁).edgeSet (Fin.last k.val) := by
  ext x
  constructor
  · intro hx
    -- Each cut region supplies one of the two opposite diagonal inequalities.
    have hleftSupport :
        x ∈ (left poly k hk₁).supportingHalfspace (Fin.last k.val) := by
      rw [(left poly k hk₁).region_eq_iInter_supportingHalfspace] at hx
      exact Set.mem_iInter.mp hx.1 (Fin.last k.val)
    have hrightSupport :
        x ∈ (right poly k hk₁ hk₂).supportingHalfspace 0 := by
      rw [(right poly k hk₁ hk₂).region_eq_iInter_supportingHalfspace] at hx
      exact Set.mem_iInter.mp hx.2 0
    have hnonpos :=
      (mem_left_diagonal_supportingHalfspace_iff poly k hk₁ x).mp hleftSupport
    have hnonneg :=
      (mem_right_diagonal_supportingHalfspace_iff poly k hk₁ hk₂ x).mp
        hrightSupport
    have hdiagonal : CyclicPolygon.signedArea
        (poly.toPolygon.vertices k - poly.toPolygon.vertices (indexZero poly))
        (x - poly.toPolygon.vertices (indexZero poly)) = 0 :=
      le_antisymm hnonpos hnonneg
    -- The left closing edge reverses that diagonal, so its determinant also vanishes.
    rw [(left poly k hk₁).mem_edgeSet_iff_mem_region_and_signedArea_eq_zero]
    refine ⟨hx.1, ?_⟩
    rw [finRotate_last, left_apply, left_apply]
    have hlast : leftIndex k (Fin.last k.val) = k := by
      apply Fin.ext
      simp only [leftIndex_val, Fin.val_last]
    have hzero : leftIndex k 0 = indexZero poly := by
      apply Fin.ext
      simp only [leftIndex_val, Fin.val_zero, indexZero_val]
    rw [hlast, hzero, signedArea_sub_swap, hdiagonal, neg_zero]
  · intro hx
    -- The common-edge theorem puts the same diagonal in the right cut region.
    refine ⟨(left poly k hk₁).edgeSet_subset_region (Fin.last k.val) hx, ?_⟩
    apply (right poly k hk₁ hk₂).edgeSet_subset_region 0
    rw [← commonEdge poly k hk₁ hk₂]
    exact hx

end

end CyclicPolygon.Cut

namespace CyclicPolygon

noncomputable section

/-- Helper for Definition 76.3: the initial edge of the right cut after first-gap
insertion is the original polygon's initial edge. -/
theorem insertedRightCut_edgeSet_zero {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) :
    (CyclicPolygon.Cut.right (insertInFirstGap hm poly) (sharedIndex hm poly)
      (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)).edgeSet 0 =
        poly.edgeSet (CyclicPolygon.Cut.indexZero poly) := by
  have hzero : Fin.cast (insertedRightCount hm poly)
      (0 : Fin (m + n - 2 - (sharedIndex hm poly).val + 1)) =
        CyclicPolygon.Cut.indexZero poly := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_zero, CyclicPolygon.Cut.indexZero_val]
  have hsuccessor : Fin.cast (insertedRightCount hm poly)
      (finRotate (m + n - 2 - (sharedIndex hm poly).val + 1) 0) =
        finRotate n (CyclicPolygon.Cut.indexZero poly) := by
    rw [finCast_finRotate]
    exact congrArg (finRotate n) hzero
  -- Compute the two endpoints through the right-cut vertex interface.
  unfold edgeSet Polygon.edgeSet
  rw [insertedRightCut_vertices, insertedRightCut_vertices, hzero, hsuccessor]

/-- Helper for Definition 76.3: first-gap insertion yields a replacement polygon
whose closing edge is the reversed initial edge of the original polygon. -/
theorem existsFirstGapInsertionCut {m n : ℕ} (hm : 3 ≤ m)
    (poly : CyclicPolygon n) :
    ∃ (replacement : CyclicPolygon m) (combined : CyclicPolygon (m + n - 2))
        (closingEdge : Fin m),
      replacement.center = poly.center ∧
      replacement.radius = poly.radius ∧
      replacement.toPolygon.vertices closingEdge =
        poly.toPolygon.vertices
          (finRotate n (CyclicPolygon.Cut.indexZero poly)) ∧
      replacement.toPolygon.vertices (finRotate m closingEdge) =
        poly.toPolygon.vertices (CyclicPolygon.Cut.indexZero poly) ∧
      combined.region = replacement.region ∪ poly.region ∧
      replacement.region ∩ poly.region =
        poly.edgeSet (CyclicPolygon.Cut.indexZero poly) := by
  let combined := insertInFirstGap hm poly
  let k := sharedIndex hm poly
  let leftPart := CyclicPolygon.Cut.left combined k (sharedIndex_one_lt hm poly)
  let rightPart := CyclicPolygon.Cut.right combined k
    (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)
  have hleftCount : k.val + 1 = m := by
    dsimp only [k]
    rw [sharedIndex_val]
    omega
  let replacement := castVertexCount hleftCount leftPart
  let closingEdge : Fin m := Fin.cast hleftCount (Fin.last k.val)
  have hclosingSuccessor : finRotate m closingEdge =
      Fin.cast hleftCount (0 : Fin (k.val + 1)) := by
    dsimp only [closingEdge]
    rw [← finCast_finRotate, finRotate_last]
  have hfirstSuccessor : firstVertexIndex poly =
      finRotate n (CyclicPolygon.Cut.indexZero poly) := by
    exact firstVertexIndex_eq_finRotate_indexZero poly
  have hleftLast : CyclicPolygon.Cut.leftIndex k (Fin.last k.val) = k := by
    apply Fin.ext
    simp only [CyclicPolygon.Cut.leftIndex_val, Fin.val_last]
  have hleftZero : CyclicPolygon.Cut.leftIndex k 0 =
      CyclicPolygon.Cut.indexZero combined := by
    apply Fin.ext
    simp only [CyclicPolygon.Cut.leftIndex_val, Fin.val_zero,
      CyclicPolygon.Cut.indexZero_val]
  have hclosingVertex : replacement.toPolygon.vertices closingEdge =
      poly.toPolygon.vertices
        (finRotate n (CyclicPolygon.Cut.indexZero poly)) := by
    -- The last left-cut vertex is the old first successor.
    calc
      replacement.toPolygon.vertices closingEdge =
          leftPart.toPolygon.vertices (Fin.last k.val) := by
        exact castVertexCount_vertices hleftCount leftPart (Fin.last k.val)
      _ = combined.toPolygon.vertices
          (CyclicPolygon.Cut.leftIndex k (Fin.last k.val)) := by
        exact CyclicPolygon.Cut.left_apply combined k
          (sharedIndex_one_lt hm poly) (Fin.last k.val)
      _ = combined.toPolygon.vertices k :=
        congrArg combined.toPolygon.vertices hleftLast
      _ = poly.toPolygon.vertices (firstVertexIndex poly) := by
        exact insertInFirstGap_vertex_shared hm poly
      _ = poly.toPolygon.vertices
          (finRotate n (CyclicPolygon.Cut.indexZero poly)) :=
        congrArg poly.toPolygon.vertices hfirstSuccessor
  have hzeroVertex : replacement.toPolygon.vertices (finRotate m closingEdge) =
      poly.toPolygon.vertices (CyclicPolygon.Cut.indexZero poly) := by
    -- The successor of the closing edge wraps to the unchanged zero vertex.
    calc
      replacement.toPolygon.vertices (finRotate m closingEdge) =
          replacement.toPolygon.vertices
            (Fin.cast hleftCount (0 : Fin (k.val + 1))) :=
        congrArg replacement.toPolygon.vertices hclosingSuccessor
      _ = leftPart.toPolygon.vertices 0 := by
        exact castVertexCount_vertices hleftCount leftPart 0
      _ = combined.toPolygon.vertices (CyclicPolygon.Cut.leftIndex k 0) := by
        exact CyclicPolygon.Cut.left_apply combined k
          (sharedIndex_one_lt hm poly) 0
      _ = combined.toPolygon.vertices (CyclicPolygon.Cut.indexZero combined) :=
        congrArg combined.toPolygon.vertices hleftZero
      _ = poly.toPolygon.vertices (CyclicPolygon.Cut.indexZero poly) := by
        exact insertInFirstGap_vertex_zero hm poly
  have hcenter : replacement.center = poly.center := by
    calc
      replacement.center = leftPart.center := castVertexCount_center hleftCount leftPart
      _ = combined.center := CyclicPolygon.Cut.left_center combined k
        (sharedIndex_one_lt hm poly)
      _ = poly.center := insertInFirstGap_center hm poly
  have hradius : replacement.radius = poly.radius := by
    calc
      replacement.radius = leftPart.radius := castVertexCount_radius hleftCount leftPart
      _ = combined.radius := CyclicPolygon.Cut.left_radius combined k
        (sharedIndex_one_lt hm poly)
      _ = poly.radius := insertInFirstGap_radius hm poly
  have hunion : combined.region = replacement.region ∪ poly.region := by
    -- Rewrite the cut decomposition through the count cast and the right-cut region API.
    calc
      combined.region = leftPart.region ∪ rightPart.region := by
        exact CyclicPolygon.Cut.region_eq_union combined k
          (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)
      _ = replacement.region ∪ poly.region := by
        dsimp only [replacement, rightPart, combined, k]
        rw [castVertexCount_region, insertedRightCut_region]
  have hintersection : replacement.region ∩ poly.region =
      poly.edgeSet (CyclicPolygon.Cut.indexZero poly) := by
    -- The cut intersection is its common diagonal, computed on the right as edge zero.
    calc
      replacement.region ∩ poly.region = leftPart.region ∩ rightPart.region := by
        dsimp only [replacement, rightPart, combined, k]
        rw [castVertexCount_region, insertedRightCut_region]
      _ = leftPart.edgeSet (Fin.last k.val) := by
        exact CyclicPolygon.Cut.regionsInterEqDiagonal combined k
          (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)
      _ = rightPart.edgeSet 0 := by
        exact CyclicPolygon.Cut.commonEdge combined k
          (sharedIndex_one_lt hm poly) (sharedIndex_lt_last hm poly)
      _ = poly.edgeSet (CyclicPolygon.Cut.indexZero poly) :=
        insertedRightCut_edgeSet_zero hm poly
  refine ⟨replacement, combined, closingEdge, hcenter, hradius,
    hclosingVertex, hzeroVertex, hunion, hintersection⟩

/-- Helper for Definition 76.3: insert the replacement polygon's extra vertices into
the distinguished angular gap of the right polygon, producing the cyclic union. -/
theorem existsCyclicEdgeInsertion {m n : ℕ} (hm : 3 ≤ m)
    (right : CyclicPolygon n) (replacementEdge : Fin m) (rightEdge : Fin n) :
    ∃ (replacement : CyclicPolygon m) (combined : CyclicPolygon (m + n - 2)),
      replacement.center = right.center ∧
      replacement.radius = right.radius ∧
      replacement.toPolygon.vertices replacementEdge =
        right.toPolygon.vertices (finRotate n rightEdge) ∧
      replacement.toPolygon.vertices (finRotate m replacementEdge) =
        right.toPolygon.vertices rightEdge ∧
      combined.region = replacement.region ∪ right.region ∧
      replacement.region ∩ right.region = right.edgeSet rightEdge := by
    -- Normalize the selected right edge to zero, where the insertion interface applies.
    obtain ⟨normalizedRight, hrightCenter, hrightRadius, hrightRegion,
        hrightZero, hrightSuccessor, hrightEdge⟩ :=
      existsEdgeAlignedRotateFrom right rightEdge
        (CyclicPolygon.Cut.indexZero right)
    have hnormalizedZero : CyclicPolygon.Cut.indexZero normalizedRight =
        CyclicPolygon.Cut.indexZero right := by
      apply Fin.ext
      rw [CyclicPolygon.Cut.indexZero_val, CyclicPolygon.Cut.indexZero_val]
    have hrightZero' : normalizedRight.toPolygon.vertices
        (CyclicPolygon.Cut.indexZero normalizedRight) =
          right.toPolygon.vertices rightEdge := by
      calc
        normalizedRight.toPolygon.vertices
            (CyclicPolygon.Cut.indexZero normalizedRight) =
          normalizedRight.toPolygon.vertices
            (CyclicPolygon.Cut.indexZero right) :=
          congrArg normalizedRight.toPolygon.vertices hnormalizedZero
        _ = right.toPolygon.vertices rightEdge := hrightZero
    have hrightSuccessor' : normalizedRight.toPolygon.vertices
        (finRotate n (CyclicPolygon.Cut.indexZero normalizedRight)) =
          right.toPolygon.vertices (finRotate n rightEdge) := by
      calc
        normalizedRight.toPolygon.vertices
            (finRotate n (CyclicPolygon.Cut.indexZero normalizedRight)) =
          normalizedRight.toPolygon.vertices
            (finRotate n (CyclicPolygon.Cut.indexZero right)) :=
          congrArg normalizedRight.toPolygon.vertices
            (congrArg (finRotate n) hnormalizedZero)
        _ = right.toPolygon.vertices (finRotate n rightEdge) := hrightSuccessor
    have hrightEdge' : normalizedRight.edgeSet
        (CyclicPolygon.Cut.indexZero normalizedRight) = right.edgeSet rightEdge := by
      calc
        normalizedRight.edgeSet (CyclicPolygon.Cut.indexZero normalizedRight) =
            normalizedRight.edgeSet (CyclicPolygon.Cut.indexZero right) :=
          congrArg normalizedRight.edgeSet hnormalizedZero
        _ = right.edgeSet rightEdge := hrightEdge
    obtain ⟨baseReplacement, combined, closingEdge, hbaseCenter, hbaseRadius,
        hbaseClosing, hbaseZero, hbaseUnion, hbaseIntersection⟩ :=
      existsFirstGapInsertionCut hm normalizedRight
    -- Reindex the inserted left cut so its closing edge has the requested index.
    obtain ⟨replacement, hreplacementCenter, hreplacementRadius,
        hreplacementRegion, hreplacementClosing, hreplacementSuccessor, _⟩ :=
      existsEdgeAlignedRotateFrom baseReplacement closingEdge replacementEdge
    have hcenter : replacement.center = right.center := by
      calc
        replacement.center = baseReplacement.center := hreplacementCenter
        _ = normalizedRight.center := hbaseCenter
        _ = right.center := hrightCenter
    have hradius : replacement.radius = right.radius := by
      calc
        replacement.radius = baseReplacement.radius := hreplacementRadius
        _ = normalizedRight.radius := hbaseRadius
        _ = right.radius := hrightRadius
    have hinitial : replacement.toPolygon.vertices replacementEdge =
        right.toPolygon.vertices (finRotate n rightEdge) := by
      calc
        replacement.toPolygon.vertices replacementEdge =
            baseReplacement.toPolygon.vertices closingEdge := hreplacementClosing
        _ = normalizedRight.toPolygon.vertices
            (finRotate n (CyclicPolygon.Cut.indexZero normalizedRight)) := hbaseClosing
        _ = right.toPolygon.vertices (finRotate n rightEdge) := hrightSuccessor'
    have hfinal : replacement.toPolygon.vertices (finRotate m replacementEdge) =
        right.toPolygon.vertices rightEdge := by
      calc
        replacement.toPolygon.vertices (finRotate m replacementEdge) =
            baseReplacement.toPolygon.vertices (finRotate m closingEdge) :=
          hreplacementSuccessor
        _ = normalizedRight.toPolygon.vertices
            (CyclicPolygon.Cut.indexZero normalizedRight) := hbaseZero
        _ = right.toPolygon.vertices rightEdge := hrightZero'
    have hunion : combined.region = replacement.region ∪ right.region := by
      calc
        combined.region = baseReplacement.region ∪ normalizedRight.region := hbaseUnion
        _ = replacement.region ∪ right.region := by
          rw [← hreplacementRegion, hrightRegion]
    have hintersection : replacement.region ∩ right.region =
        right.edgeSet rightEdge := by
      calc
        replacement.region ∩ right.region =
            baseReplacement.region ∩ normalizedRight.region := by
          rw [hreplacementRegion, ← hrightRegion]
        _ = normalizedRight.edgeSet (CyclicPolygon.Cut.indexZero normalizedRight) :=
          hbaseIntersection
        _ = right.edgeSet rightEdge := hrightEdge'
    exact ⟨replacement, combined, hcenter, hradius, hinitial, hfinal,
      hunion, hintersection⟩

end


end CyclicPolygon

namespace CyclicPolygon.EdgeGluing

noncomputable section

/-- Helper for Definition 76.3: the attaching map preserves the cyclic edge parameter
for equal orientations and reverses it for opposite orientations. -/
theorem attachingMap_cyclicRegionPoint {m n : ℕ} {left : CyclicPolygon m}
    {right : CyclicPolygon n} (gluing : EdgeGluing left right) (s : unitInterval) :
    gluing.attachingMap (gluing.leftEdge.cyclicRegionPoint s) =
      right.boundaryToRegion
        (right.edgePoint gluing.rightEdge.index
          (if gluing.leftEdge.forward = gluing.rightEdge.forward then s
            else unitInterval.symm s)) := by
  -- The positive segment homeomorphism uses the same directed parameter on both edges.
  apply Subtype.ext
  rw [gluing.attachingMap_apply,
    gluing.leftEdge.segmentPoint_cyclicRegionPoint,
    OrientedSegment.positiveHomeomorph_apply,
    OrientedSegment.paramHomeomorph_apply, right.boundaryToRegion_coe,
    right.edgePoint_coe_eq_lineMap]
  cases hleft : gluing.leftEdge.forward <;>
    cases hright : gluing.rightEdge.forward
  · rw [gluing.rightEdge.segment_initial, gluing.rightEdge.segment_final,
      gluing.rightEdge.initial_eq, gluing.rightEdge.final_eq]
    simp only [hright, Bool.false_eq_true, ↓reduceIte,
      unitInterval.coe_symm_eq]
    rw [AffineMap.lineMap_apply_one_sub]
  · rw [gluing.rightEdge.segment_initial, gluing.rightEdge.segment_final,
      gluing.rightEdge.initial_eq, gluing.rightEdge.final_eq]
    simp only [hright, Bool.false_eq_true, ↓reduceIte,
      unitInterval.coe_symm_eq]
  · rw [gluing.rightEdge.segment_initial, gluing.rightEdge.segment_final,
      gluing.rightEdge.initial_eq, gluing.rightEdge.final_eq]
    simp [hright, unitInterval.coe_symm_eq]
  · rw [gluing.rightEdge.segment_initial, gluing.rightEdge.segment_final,
      gluing.rightEdge.initial_eq, gluing.rightEdge.final_eq]
    simp only [hright, ↓reduceIte]

/-- Helper for Definition 76.3: an indexed parameter-preserving region homeomorphism
agrees with the attaching map when the replacement edge is the reversed right edge. -/
theorem regionHomeomorphAgreesWithAttachingMapOfReversedEdge
    {m n : ℕ} {left : CyclicPolygon m} {right : CyclicPolygon n}
    (gluing : EdgeGluing left right) (replacement : CyclicPolygon m)
    (H : left.region ≃ₜ replacement.region)
    (hparameters : ∀ (i : Fin m) (s : unitInterval),
      H (left.boundaryToRegion (left.edgePoint i s)) =
        replacement.boundaryToRegion (replacement.edgePoint i s))
    (hinitial : replacement.toPolygon.vertices gluing.leftEdge.index =
      right.toPolygon.vertices (finRotate n gluing.rightEdge.index))
    (hfinal : replacement.toPolygon.vertices (finRotate m gluing.leftEdge.index) =
      right.toPolygon.vertices gluing.rightEdge.index)
    (h_oppositeOrientation :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward) :
    ∀ x : gluing.attachingSubset,
      (H x : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap x := by
  intro x
  obtain ⟨s, hs⟩ := left.existsEdgePointParameter gluing.leftEdge.index x.1 x.2
  have hx : gluing.leftEdge.cyclicRegionPoint s = x := by
    apply Subtype.ext
    exact hs
  rw [← hx]
  -- Both maps now have explicit affine formulas with reversed endpoints.
  calc
    (H (gluing.leftEdge.cyclicRegionPoint s) : EuclideanSpace ℝ (Fin 2)) =
        (H (left.boundaryToRegion (left.edgePoint gluing.leftEdge.index s)) :
          EuclideanSpace ℝ (Fin 2)) := by
      rw [gluing.leftEdge.cyclicRegionPoint_coe]
    _ = (replacement.boundaryToRegion
          (replacement.edgePoint gluing.leftEdge.index s) : replacement.region) :=
      congrArg Subtype.val (hparameters gluing.leftEdge.index s)
    _ = (right.boundaryToRegion
          (right.edgePoint gluing.rightEdge.index (unitInterval.symm s)) :
            right.region) := by
      rw [replacement.boundaryToRegion_coe,
        replacement.edgePoint_coe_eq_lineMap, right.boundaryToRegion_coe,
        right.edgePoint_coe_eq_lineMap, unitInterval.coe_symm_eq,
        hinitial, hfinal, AffineMap.lineMap_apply_one_sub]
    _ = (gluing.attachingMap (gluing.leftEdge.cyclicRegionPoint s) : right.region) := by
      exact congrArg Subtype.val
        (by simpa only [if_neg h_oppositeOrientation] using
          (gluing.attachingMap_cyclicRegionPoint s).symm)

/-- Helper for Definition 76.3: compatible maps from two polygonal regions identify
their adjunction-space realization with a cyclic region equal to their planar union. -/
theorem existsRealizationHomeomorphOfRegionUnion
    {m n k : ℕ} {left : CyclicPolygon m} {right : CyclicPolygon n}
    (gluing : EdgeGluing left right) (replacement : CyclicPolygon m)
    (combined : CyclicPolygon k) (H : left.region ≃ₜ replacement.region)
    (h_oppositeOrientation :
      gluing.leftEdge.forward ≠ gluing.rightEdge.forward)
    (hattaching : ∀ a : gluing.attachingSubset,
      (H a : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap a)
    (hunion : combined.region = replacement.region ∪ right.region)
    (hinter : replacement.region ∩ right.region =
      right.edgeSet gluing.rightEdge.index) :
    ∃ homeomorph : gluing.Realization ≃ₜ combined.region,
      (∀ x : left.region,
        (homeomorph (gluing.includeLeft x) : EuclideanSpace ℝ (Fin 2)) = H x) ∧
      ∀ y : right.region,
        (homeomorph (gluing.includeRight y) : EuclideanSpace ℝ (Fin 2)) = y := by
  have hreplacement : replacement.region ⊆ combined.region := by
    rw [hunion]
    exact subset_union_left
  have hright : right.region ⊆ combined.region := by
    rw [hunion]
    exact subset_union_right
  let leftMap : C(left.region, combined.region) :=
    ⟨fun x ↦ ⟨H x, hreplacement (H x).property⟩,
      (continuous_subtype_val.comp H.continuous).subtype_mk _⟩
  let rightMap : C(right.region, combined.region) :=
    ⟨fun y ↦ ⟨y, hright y.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hleftMapCoe (x : left.region) :
      (leftMap x : EuclideanSpace ℝ (Fin 2)) = H x := by
    rfl
  have hrightMapCoe (y : right.region) :
      (rightMap y : EuclideanSpace ℝ (Fin 2)) = y := by
    rfl
  have hglue : ∀ a : gluing.attachingSubset,
      leftMap a = rightMap (gluing.attachingMap a) := by
    intro a
    -- Compatibility is exactly the ambient attaching-map equality.
    apply Subtype.ext
    calc
      (leftMap a : EuclideanSpace ℝ (Fin 2)) = H a := hleftMapCoe a
      _ = gluing.attachingMap a := hattaching a
      _ = (rightMap (gluing.attachingMap a) : EuclideanSpace ℝ (Fin 2)) :=
        (hrightMapCoe (gluing.attachingMap a)).symm
  let gluedMap : gluing.Realization → combined.region :=
    AdjunctionSpace.lift gluing.attachingSubset gluing.attachingMap leftMap rightMap hglue
  have hgluedContinuous : Continuous gluedMap := by
    -- Continuity follows from the adjunction-space quotient eliminator.
    exact AdjunctionSpace.continuous_lift gluing.attachingSubset gluing.attachingMap
      leftMap rightMap hglue
  have hgluedSurjective : Function.Surjective gluedMap := by
    intro z
    have hzUnion : (z : EuclideanSpace ℝ (Fin 2)) ∈
        replacement.region ∪ right.region := by
      rw [← hunion]
      exact z.property
    rcases hzUnion with hzReplacement | hzRight
    · let zReplacement : replacement.region := ⟨z, hzReplacement⟩
      obtain ⟨x, hx⟩ := H.surjective zReplacement
      refine ⟨gluing.includeLeft x, ?_⟩
      apply Subtype.ext
      dsimp only [gluedMap]
      rw [gluing.includeLeft_eq_includeX, AdjunctionSpace.lift_includeX,
        hleftMapCoe]
      exact congrArg Subtype.val hx
    · let zRight : right.region := ⟨z, hzRight⟩
      refine ⟨gluing.includeRight zRight, ?_⟩
      apply Subtype.ext
      dsimp only [gluedMap]
      rw [gluing.includeRight_eq_includeY, AdjunctionSpace.lift_includeY,
        hrightMapCoe]
  have hcross (x : left.region) (y : right.region)
      (hxy : leftMap x = rightMap y) :
      AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap x =
        AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap y := by
    have hambient : (H x : EuclideanSpace ℝ (Fin 2)) = y := by
      calc
        (H x : EuclideanSpace ℝ (Fin 2)) =
            (leftMap x : EuclideanSpace ℝ (Fin 2)) := (hleftMapCoe x).symm
        _ = (rightMap y : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hxy
        _ = y := hrightMapCoe y
    have hintersection : (H x : EuclideanSpace ℝ (Fin 2)) ∈
        replacement.region ∩ right.region :=
      ⟨(H x).property, hambient ▸ y.property⟩
    rw [hinter] at hintersection
    obtain ⟨t, ht⟩ := right.existsEdgePointParameter gluing.rightEdge.index y
      (hambient ▸ hintersection)
    let a : gluing.attachingSubset :=
      gluing.leftEdge.cyclicRegionPoint (unitInterval.symm t)
    have hattachingPoint : gluing.attachingMap a = y := by
      calc
        gluing.attachingMap a = right.boundaryToRegion
            (right.edgePoint gluing.rightEdge.index
              (unitInterval.symm (unitInterval.symm t))) := by
          simpa only [a, if_neg h_oppositeOrientation] using
            gluing.attachingMap_cyclicRegionPoint (unitInterval.symm t)
        _ = right.boundaryToRegion (right.edgePoint gluing.rightEdge.index t) := by
          rw [unitInterval.symm_symm]
        _ = y := ht
    have ha : (a : left.region) = x := by
      apply H.injective
      apply Subtype.ext
      calc
        (H a : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap a := hattaching a
        _ = y := congrArg Subtype.val hattachingPoint
        _ = H x := hambient.symm
    calc
      AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap x =
          AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap a :=
        congrArg (AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap)
          ha.symm
      _ = AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap
          (gluing.attachingMap a) :=
        AdjunctionSpace.glue gluing.attachingSubset gluing.attachingMap a
      _ = AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap y :=
        congrArg (AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap)
          hattachingPoint
  have hgluedInjective : Function.Injective gluedMap := by
    intro q₁ q₂ hq
    rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
      gluing.attachingSubset gluing.attachingMap q₁ with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
        gluing.attachingSubset gluing.attachingMap q₂ with ⟨x', rfl⟩ | ⟨y, rfl⟩
      · dsimp only [gluedMap] at hq
        rw [AdjunctionSpace.lift_includeX, AdjunctionSpace.lift_includeX] at hq
        have hxx : x = x' := by
          apply H.injective
          apply Subtype.ext
          calc
            (H x : EuclideanSpace ℝ (Fin 2)) =
                (leftMap x : EuclideanSpace ℝ (Fin 2)) := (hleftMapCoe x).symm
            _ = (leftMap x' : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hq
            _ = (H x' : EuclideanSpace ℝ (Fin 2)) := hleftMapCoe x'
        rw [hxx]
      · dsimp only [gluedMap] at hq
        rw [AdjunctionSpace.lift_includeX, AdjunctionSpace.lift_includeY] at hq
        exact hcross x y hq
    · rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
        gluing.attachingSubset gluing.attachingMap q₂ with ⟨x, rfl⟩ | ⟨y', rfl⟩
      · dsimp only [gluedMap] at hq
        rw [AdjunctionSpace.lift_includeY, AdjunctionSpace.lift_includeX] at hq
        exact (hcross x y hq.symm).symm
      · dsimp only [gluedMap] at hq
        rw [AdjunctionSpace.lift_includeY, AdjunctionSpace.lift_includeY] at hq
        have hyy : y = y' := by
          apply Subtype.ext
          calc
            (y : EuclideanSpace ℝ (Fin 2)) =
                (rightMap y : EuclideanSpace ℝ (Fin 2)) := (hrightMapCoe y).symm
            _ = (rightMap y' : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hq
            _ = (y' : EuclideanSpace ℝ (Fin 2)) := hrightMapCoe y'
        rw [hyy]
  letI : CompactSpace left.region := isCompact_iff_compactSpace.mp left.region_isCompact
  letI : CompactSpace right.region := isCompact_iff_compactSpace.mp right.region_isCompact
  letI : CompactSpace gluing.Realization := Quotient.compactSpace
  have hhomeomorph : IsHomeomorph gluedMap :=
    (isHomeomorph_iff_continuous_bijective).2
      ⟨hgluedContinuous, hgluedInjective, hgluedSurjective⟩
  let homeomorph : gluing.Realization ≃ₜ combined.region :=
    hhomeomorph.homeomorph gluedMap
  refine ⟨homeomorph, ?_, ?_⟩
  · intro x
    -- Compute the quotient lift on the left summand.
    dsimp only [homeomorph]
    rw [IsHomeomorph.homeomorph_apply]
    dsimp only [gluedMap]
    rw [gluing.includeLeft_eq_includeX, AdjunctionSpace.lift_includeX,
      hleftMapCoe]
  · intro y
    -- Compute the quotient lift on the right summand.
    dsimp only [homeomorph]
    rw [IsHomeomorph.homeomorph_apply]
    dsimp only [gluedMap]
    rw [gluing.includeRight_eq_includeY, AdjunctionSpace.lift_includeY,
      hrightMapCoe]

end

end CyclicPolygon.EdgeGluing
