module

public import Topology_Munkres_2000.Book.Definition_76_1.Cut
public import Topology_Munkres_2000.Book.Proposition_74_1.Segments
public import Topology_Munkres_2000.Book.Proposition_76_2.ReassemblyCorrection

public section

namespace CyclicPolygon

/-- Helper for Proposition 76.2: every filled cyclic polygonal region is compact. -/
theorem isCompact_region {n : ℕ} (poly : CyclicPolygon n) : IsCompact poly.region := by
  -- The region is the convex hull of the finite vertex set.
  rw [poly.region_eq_convexHull]
  exact Set.finite_range poly.toPolygon.vertices |>.isCompact_convexHull ℝ

end CyclicPolygon

namespace CyclicPolygon.Cut

noncomputable section

variable {n : ℕ}

/-- Helper for Proposition 76.2: include the left cut region into the original
filled polygonal region. -/
def leftRegionInclusion (poly : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val) :
    C((left poly k hk₁).region, poly.region) :=
  ⟨fun x ↦ ⟨x, left_region_subset poly k hk₁ x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Helper for Proposition 76.2: left-region inclusion preserves ambient points. -/
theorem leftRegionInclusion_coe (poly : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (x : (left poly k hk₁).region) :
    (leftRegionInclusion poly k hk₁ x : EuclideanSpace ℝ (Fin 2)) = x := by
  -- The inclusion changes only the region-membership proof.
  rfl

/-- Helper for Proposition 76.2: include the right cut region into the original
filled polygonal region. -/
def rightRegionInclusion (poly : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val)
    (hk₂ : k.val < n - 1) : C((right poly k hk₁ hk₂).region, poly.region) :=
  ⟨fun x ↦ ⟨x, right_region_subset poly k hk₁ hk₂ x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Helper for Proposition 76.2: right-region inclusion preserves ambient points. -/
theorem rightRegionInclusion_coe (poly : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1)
    (x : (right poly k hk₁ hk₂).region) :
    (rightRegionInclusion poly k hk₁ hk₂ x : EuclideanSpace ℝ (Fin 2)) = x := by
  -- The inclusion changes only the region-membership proof.
  rfl

/-- Helper for Proposition 76.2: the closing edge of the left cut and the initial
edge of the right cut carry opposite cyclic parameters pointwise. -/
theorem left_closing_edgePoint_eq_right_initial_symm (poly : CyclicPolygon n)
    (k : Fin n) (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1)
    (s : unitInterval) :
    ((left poly k hk₁).edgePoint (Fin.last k.val) s :
        EuclideanSpace ℝ (Fin 2)) =
      ((right poly k hk₁ hk₂).edgePoint 0 (unitInterval.symm s) :
        EuclideanSpace ℝ (Fin 2)) := by
  -- Normalize both cut edges to the same diagonal with reversed endpoints.
  rw [(left poly k hk₁).edgePoint_coe_eq_lineMap,
    (right poly k hk₁ hk₂).edgePoint_coe_eq_lineMap,
    finRotate_last, finRotate_apply_zero, left_apply, left_apply,
    right_apply, right_apply]
  have hn : 0 < n := by omega
  have htail : 0 < n - k.val := by omega
  have hleftLast : leftIndex k (Fin.last k.val) = k := by
    apply Fin.ext
    simp only [leftIndex_val, Fin.val_last]
  have hleftZero : leftIndex k 0 = ⟨0, hn⟩ := by
    apply Fin.ext
    simp only [leftIndex_val, Fin.val_zero]
  have hrightZero : rightIndex k 0 = ⟨0, hn⟩ := by
    apply Fin.ext
    simpa only using rightIndex_zero k
  have hrightOne : rightIndex k 1 = k := by
    have hsucc : (⟨0, htail⟩ : Fin (n - k.val)).succ = 1 := by
      apply Fin.ext
      rw [Fin.val_succ]
      have honeLt : 1 < n - k.val + 1 := by omega
      exact (Nat.mod_eq_of_lt honeLt).symm
    rw [← hsucc]
    apply Fin.ext
    simpa only [Nat.add_zero] using rightIndex_succ k ⟨0, htail⟩
  rw [hleftLast, hleftZero, hrightZero, hrightOne,
    unitInterval.coe_symm_eq, AffineMap.lineMap_apply_one_sub]

/-- Helper for Proposition 76.2: the two filled regions produced by a diagonal cut
meet exactly in their common cut edge. -/
theorem left_region_inter_right_region (poly : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1) :
    (left poly k hk₁).region ∩ (right poly k hk₁ hk₂).region =
      (left poly k hk₁).edgeSet (Fin.last k.val) := by
  ext x
  constructor
  · intro hx
    -- Membership in the two cut pieces puts the diagonal determinant on both sides of zero.
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
    -- The left closing edge uses the reverse orientation of the same diagonal.
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
    -- The common edge is contained in each cut region.
    refine ⟨(left poly k hk₁).edgeSet_subset_region (Fin.last k.val) hx, ?_⟩
    apply (right poly k hk₁ hk₂).edgeSet_subset_region 0
    rw [← commonEdge poly k hk₁ hk₂]
    exact hx

end

end CyclicPolygon.Cut

namespace CyclicPolygon.EdgeGluing

noncomputable section

/-- Helper for Proposition 76.2: compatible homeomorphisms from the two glued
regions to the two sides of a diagonal cut assemble to a homeomorphism from the
adjunction-space realization to the uncut polygon. -/
theorem existsHomeomorphToCut {m n kSides : ℕ} {left : CyclicPolygon m}
    {right : CyclicPolygon n} (gluing : EdgeGluing left right)
    (poly : CyclicPolygon kSides) (k : Fin kSides)
    (hk₁ : 1 < k.val) (hk₂ : k.val < kSides - 1)
    (leftHomeomorph : left.region ≃ₜ (Cut.left poly k hk₁).region)
    (rightHomeomorph : right.region ≃ₜ (Cut.right poly k hk₁ hk₂).region)
    (hleftEdge : ∀ s : unitInterval,
      leftHomeomorph (left.boundaryToRegion
        (left.edgePoint gluing.leftEdge.index s)) =
          (Cut.left poly k hk₁).boundaryToRegion
            ((Cut.left poly k hk₁).edgePoint (Fin.last k.val) s))
    (hrightEdge : ∀ s : unitInterval,
      rightHomeomorph (right.boundaryToRegion
        (right.edgePoint gluing.rightEdge.index (unitInterval.symm s))) =
          (Cut.right poly k hk₁ hk₂).boundaryToRegion
            ((Cut.right poly k hk₁ hk₂).edgePoint 0
              (unitInterval.symm s)))
    (hattaching : ∀ s : unitInterval,
      gluing.attachingMap (gluing.leftEdge.regionEdgePoint s) =
        right.boundaryToRegion
          (right.edgePoint gluing.rightEdge.index (unitInterval.symm s))) :
    ∃ homeomorph : gluing.Realization ≃ₜ poly.region,
      (∀ x : left.region,
        (homeomorph (gluing.includeLeft x) : EuclideanSpace ℝ (Fin 2)) =
          leftHomeomorph x) ∧
      ∀ y : right.region,
        (homeomorph (gluing.includeRight y) : EuclideanSpace ℝ (Fin 2)) =
          rightHomeomorph y := by
  let leftMap : C(left.region, poly.region) :=
    (Cut.leftRegionInclusion poly k hk₁).comp
      ⟨leftHomeomorph, leftHomeomorph.continuous⟩
  let rightMap : C(right.region, poly.region) :=
    (Cut.rightRegionInclusion poly k hk₁ hk₂).comp
      ⟨rightHomeomorph, rightHomeomorph.continuous⟩
  have hleftMapCoe (x : left.region) :
      (leftMap x : EuclideanSpace ℝ (Fin 2)) = leftHomeomorph x := by
    -- The left cut inclusion changes only membership in the ambient polygon.
    dsimp only [leftMap]
    rw [ContinuousMap.comp_apply, Cut.leftRegionInclusion_coe]
    rfl
  have hrightMapCoe (y : right.region) :
      (rightMap y : EuclideanSpace ℝ (Fin 2)) = rightHomeomorph y := by
    -- The right cut inclusion changes only membership in the ambient polygon.
    dsimp only [rightMap]
    rw [ContinuousMap.comp_apply, Cut.rightRegionInclusion_coe]
    rfl
  have hglue : ∀ a : gluing.attachingSubset,
      leftMap a = rightMap (gluing.attachingMap a) := by
    intro a
    obtain ⟨s, hs⟩ := left.exists_boundaryToRegion_edgePoint_eq
      gluing.leftEdge.index a a.property
    have ha : a = gluing.leftEdge.regionEdgePoint s := by
      apply Subtype.ext
      rw [gluing.leftEdge.regionEdgePoint_coe]
      exact hs.symm
    subst a
    -- Both cut-side images are the same point of the common diagonal.
    apply Subtype.ext
    calc
      (leftMap (gluing.leftEdge.regionEdgePoint s) : EuclideanSpace ℝ (Fin 2)) =
          (leftHomeomorph (left.boundaryToRegion
            (left.edgePoint gluing.leftEdge.index s)) :
              EuclideanSpace ℝ (Fin 2)) := by
        rw [hleftMapCoe, gluing.leftEdge.regionEdgePoint_coe]
      _ = ((Cut.left poly k hk₁).boundaryToRegion
          ((Cut.left poly k hk₁).edgePoint (Fin.last k.val) s) :
            (Cut.left poly k hk₁).region) := congrArg Subtype.val (hleftEdge s)
      _ = ((Cut.right poly k hk₁ hk₂).boundaryToRegion
          ((Cut.right poly k hk₁ hk₂).edgePoint 0 (unitInterval.symm s)) :
            (Cut.right poly k hk₁ hk₂).region) := by
        rw [(Cut.left poly k hk₁).boundaryToRegion_coe,
          (Cut.right poly k hk₁ hk₂).boundaryToRegion_coe]
        exact Cut.left_closing_edgePoint_eq_right_initial_symm poly k hk₁ hk₂ s
      _ = (rightHomeomorph (right.boundaryToRegion
          (right.edgePoint gluing.rightEdge.index (unitInterval.symm s))) :
            EuclideanSpace ℝ (Fin 2)) :=
        congrArg Subtype.val (hrightEdge s).symm
      _ = (rightHomeomorph
          (gluing.attachingMap (gluing.leftEdge.regionEdgePoint s)) :
            EuclideanSpace ℝ (Fin 2)) := congrArg
        (fun y : right.region ↦ (rightHomeomorph y : EuclideanSpace ℝ (Fin 2)))
        (hattaching s).symm
      _ = (rightMap
          (gluing.attachingMap (gluing.leftEdge.regionEdgePoint s)) :
            EuclideanSpace ℝ (Fin 2)) :=
        (hrightMapCoe (gluing.attachingMap
          (gluing.leftEdge.regionEdgePoint s))).symm
  let gluedMap : gluing.Realization → poly.region :=
    AdjunctionSpace.lift gluing.attachingSubset gluing.attachingMap leftMap rightMap hglue
  have hgluedContinuous : Continuous gluedMap := by
    -- Continuity follows from the adjunction-space quotient eliminator.
    exact AdjunctionSpace.continuous_lift gluing.attachingSubset gluing.attachingMap
      leftMap rightMap hglue
  have hgluedSurjective : Function.Surjective gluedMap := by
    intro z
    have hzUnion : (z : EuclideanSpace ℝ (Fin 2)) ∈
        (Cut.left poly k hk₁).region ∪
          (Cut.right poly k hk₁ hk₂).region := by
      rw [← Cut.region_eq_union poly k hk₁ hk₂]
      exact z.property
    rcases hzUnion with hzLeft | hzRight
    · let zLeft : (Cut.left poly k hk₁).region := ⟨z, hzLeft⟩
      obtain ⟨x, hx⟩ := leftHomeomorph.surjective zLeft
      refine ⟨gluing.includeLeft x, ?_⟩
      apply Subtype.ext
      dsimp only [gluedMap]
      rw [gluing.includeLeft_eq_includeX,
        AdjunctionSpace.lift_includeX, hleftMapCoe]
      exact congrArg Subtype.val hx
    · let zRight : (Cut.right poly k hk₁ hk₂).region := ⟨z, hzRight⟩
      obtain ⟨y, hy⟩ := rightHomeomorph.surjective zRight
      refine ⟨gluing.includeRight y, ?_⟩
      apply Subtype.ext
      dsimp only [gluedMap]
      rw [gluing.includeRight_eq_includeY,
        AdjunctionSpace.lift_includeY, hrightMapCoe]
      exact congrArg Subtype.val hy
  have hcross (x : left.region) (y : right.region)
      (hxy : leftMap x = rightMap y) :
      AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap x =
        AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap y := by
    have hambient : (leftHomeomorph x : EuclideanSpace ℝ (Fin 2)) =
        rightHomeomorph y := by
      calc
        (leftHomeomorph x : EuclideanSpace ℝ (Fin 2)) =
            (leftMap x : EuclideanSpace ℝ (Fin 2)) := (hleftMapCoe x).symm
        _ = (rightMap y : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hxy
        _ = (rightHomeomorph y : EuclideanSpace ℝ (Fin 2)) := hrightMapCoe y
    have hintersection : (leftHomeomorph x : EuclideanSpace ℝ (Fin 2)) ∈
        (Cut.left poly k hk₁).region ∩
          (Cut.right poly k hk₁ hk₂).region := by
      exact ⟨(leftHomeomorph x).property, hambient ▸ (rightHomeomorph y).property⟩
    rw [Cut.left_region_inter_right_region poly k hk₁ hk₂] at hintersection
    obtain ⟨s, hs⟩ := (Cut.left poly k hk₁).exists_boundaryToRegion_edgePoint_eq
      (Fin.last k.val) (leftHomeomorph x) hintersection
    have hsource : left.boundaryToRegion
        (left.edgePoint gluing.leftEdge.index s) = x := by
      apply leftHomeomorph.injective
      calc
        leftHomeomorph (left.boundaryToRegion
            (left.edgePoint gluing.leftEdge.index s)) =
            (Cut.left poly k hk₁).boundaryToRegion
              ((Cut.left poly k hk₁).edgePoint (Fin.last k.val) s) := hleftEdge s
        _ = leftHomeomorph x := hs
    have hxEdge : (x : EuclideanSpace ℝ (Fin 2)) ∈
        left.edgeSet gluing.leftEdge.index := by
      rw [← hsource, left.boundaryToRegion_coe]
      exact left.edgePoint_mem_edgeSet gluing.leftEdge.index s
    let a : gluing.attachingSubset := ⟨x, hxEdge⟩
    have ha : (a : left.region) = x := by rfl
    have hrightMap : rightMap (gluing.attachingMap a) = rightMap y := by
      calc
        rightMap (gluing.attachingMap a) = leftMap a := (hglue a).symm
        _ = leftMap x := congrArg leftMap ha
        _ = rightMap y := hxy
    have hrightPoint : gluing.attachingMap a = y := by
      apply rightHomeomorph.injective
      apply Subtype.ext
      calc
        (rightHomeomorph (gluing.attachingMap a) : EuclideanSpace ℝ (Fin 2)) =
            (rightMap (gluing.attachingMap a) : EuclideanSpace ℝ (Fin 2)) :=
          (hrightMapCoe (gluing.attachingMap a)).symm
        _ = (rightMap y : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hrightMap
        _ = (rightHomeomorph y : EuclideanSpace ℝ (Fin 2)) := hrightMapCoe y
    calc
      AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap x =
          AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap a :=
        congrArg (AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap) ha.symm
      _ = AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap
          (gluing.attachingMap a) :=
        AdjunctionSpace.glue gluing.attachingSubset gluing.attachingMap a
      _ = AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap y :=
        congrArg (AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap) hrightPoint
  have hgluedInjective : Function.Injective gluedMap := by
    intro q₁ q₂ hq
    rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
      gluing.attachingSubset gluing.attachingMap q₁ with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
        gluing.attachingSubset gluing.attachingMap q₂ with ⟨x', rfl⟩ | ⟨y, rfl⟩
      · dsimp only [gluedMap] at hq
        rw [AdjunctionSpace.lift_includeX,
          AdjunctionSpace.lift_includeX] at hq
        have hxx : x = x' := by
          apply leftHomeomorph.injective
          apply Subtype.ext
          calc
            (leftHomeomorph x : EuclideanSpace ℝ (Fin 2)) =
                (leftMap x : EuclideanSpace ℝ (Fin 2)) := (hleftMapCoe x).symm
            _ = (leftMap x' : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hq
            _ = (leftHomeomorph x' : EuclideanSpace ℝ (Fin 2)) := hleftMapCoe x'
        rw [hxx]
      · dsimp only [gluedMap] at hq
        rw [AdjunctionSpace.lift_includeX,
          AdjunctionSpace.lift_includeY] at hq
        exact hcross x y hq
    · rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
        gluing.attachingSubset gluing.attachingMap q₂ with ⟨x, rfl⟩ | ⟨y', rfl⟩
      · dsimp only [gluedMap] at hq
        rw [AdjunctionSpace.lift_includeY,
          AdjunctionSpace.lift_includeX] at hq
        exact (hcross x y hq.symm).symm
      · dsimp only [gluedMap] at hq
        rw [AdjunctionSpace.lift_includeY,
          AdjunctionSpace.lift_includeY] at hq
        have hyy : y = y' := by
          apply rightHomeomorph.injective
          apply Subtype.ext
          calc
            (rightHomeomorph y : EuclideanSpace ℝ (Fin 2)) =
                (rightMap y : EuclideanSpace ℝ (Fin 2)) := (hrightMapCoe y).symm
            _ = (rightMap y' : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hq
            _ = (rightHomeomorph y' : EuclideanSpace ℝ (Fin 2)) := hrightMapCoe y'
        rw [hyy]
  letI : CompactSpace left.region := isCompact_iff_compactSpace.mp left.isCompact_region
  letI : CompactSpace right.region := isCompact_iff_compactSpace.mp right.isCompact_region
  letI : CompactSpace gluing.Realization := Quotient.compactSpace
  have hhomeomorph : IsHomeomorph gluedMap :=
    (isHomeomorph_iff_continuous_bijective).2
      ⟨hgluedContinuous, hgluedInjective, hgluedSurjective⟩
  let homeomorph : gluing.Realization ≃ₜ poly.region :=
    hhomeomorph.homeomorph gluedMap
  refine ⟨homeomorph, ?_, ?_⟩
  · intro x
    -- Compute the quotient lift on the left summand and forget cut membership.
    dsimp only [homeomorph]
    rw [IsHomeomorph.homeomorph_apply]
    dsimp only [gluedMap]
    rw [gluing.includeLeft_eq_includeX, AdjunctionSpace.lift_includeX,
      hleftMapCoe]
  · intro y
    -- Compute the quotient lift on the right summand and forget cut membership.
    dsimp only [homeomorph]
    rw [IsHomeomorph.homeomorph_apply]
    dsimp only [gluedMap]
    rw [gluing.includeRight_eq_includeY, AdjunctionSpace.lift_includeY,
      hrightMapCoe]

end

end CyclicPolygon.EdgeGluing
