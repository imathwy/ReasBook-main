module

public import Topology_Munkres_2000.Book.Definition_76_2.Gluing

public section

open Set
open scoped Pointwise

namespace CyclicPolygon.Cut

noncomputable section

/-- Helper for Definition 76.2: the filled region of a cyclic polygon is compact. -/
private theorem regionIsCompact {n : ℕ} (P : CyclicPolygon n) : IsCompact P.region := by
  -- Express the region as the convex hull of its finite vertex range.
  rw [P.region_eq_convexHull]
  exact Set.finite_range P.toPolygon.vertices |>.isCompact_convexHull ℝ

/-- Helper for Definition 76.2: right translation of a set is its pointwise additive
translate. -/
private theorem image_addRight_eq_vadd (translation : EuclideanSpace ℝ (Fin 2))
    (s : Set (EuclideanSpace ℝ (Fin 2))) :
    Homeomorph.addRight translation '' s = translation +ᵥ s := by
  ext point
  simp only [Homeomorph.coe_addRight, Set.mem_image, Set.mem_vadd_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hsum : translation + x = x + translation := add_comm translation x
    have hvadd : translation +ᵥ x = x + translation := by
      simpa only [vadd_eq_add] using hsum
    exact ⟨x, hx, hvadd⟩
  · rintro ⟨x, hx, rfl⟩
    have hsum : x + translation = translation + x := add_comm x translation
    have hvadd : x +ᵥ translation = translation + x := by
      simpa only [vadd_eq_add] using hsum
    exact ⟨x, hx, hvadd⟩

/-- Helper for Definition 76.2: two cyclic polygonal regions can be separated by
translating the first one. -/
private theorem existsDisjointTranslatedRegion {m n : ℕ}
    (A : CyclicPolygon m) (B : CyclicPolygon n) :
    ∃ translation : EuclideanSpace ℝ (Fin 2),
      Disjoint (A.translate translation).region B.region := by
  -- Compact subsets of the noncompact plane admit a disjoint pointwise translate.
  obtain ⟨translation, hdisjoint⟩ :=
    exists_disjoint_vadd_of_isCompact (regionIsCompact B) (regionIsCompact A)
  refine ⟨translation, ?_⟩
  rw [A.translate_region, image_addRight_eq_vadd]
  exact hdisjoint.symm

/-- Helper for Definition 76.2: the two regions of a diagonal cut meet exactly in
their common diagonal edge. -/
private theorem cutRegionsInterEqLeftDiagonal {n : ℕ} (P : CyclicPolygon n)
    (k : Fin n) (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1) :
    (left P k hk₁).region ∩ (right P k hk₁ hk₂).region =
      (left P k hk₁).edgeSet (Fin.last k.val) := by
  ext x
  constructor
  · intro hx
    -- The two region inequalities put the diagonal signed area on both sides of zero.
    have hleftSupport :
        x ∈ (left P k hk₁).supportingHalfspace (Fin.last k.val) := by
      rw [(left P k hk₁).region_eq_iInter_supportingHalfspace] at hx
      exact Set.mem_iInter.mp hx.1 (Fin.last k.val)
    have hrightSupport : x ∈ (right P k hk₁ hk₂).supportingHalfspace 0 := by
      rw [(right P k hk₁ hk₂).region_eq_iInter_supportingHalfspace] at hx
      exact Set.mem_iInter.mp hx.2 0
    have hnonpos :=
      (mem_left_diagonal_supportingHalfspace_iff P k hk₁ x).mp hleftSupport
    have hnonneg :=
      (mem_right_diagonal_supportingHalfspace_iff P k hk₁ hk₂ x).mp hrightSupport
    have hdiagonal : CyclicPolygon.signedArea
        (P.toPolygon.vertices k - P.toPolygon.vertices (indexZero P))
        (x - P.toPolygon.vertices (indexZero P)) = 0 :=
      le_antisymm hnonpos hnonneg
    rw [(left P k hk₁).mem_edgeSet_iff_mem_region_and_signedArea_eq_zero]
    refine ⟨hx.1, ?_⟩
    rw [finRotate_last, left_apply, left_apply]
    have hlast : leftIndex k (Fin.last k.val) = k := by
      apply Fin.ext
      simp only [leftIndex_val, Fin.val_last]
    have hzero : leftIndex k 0 = indexZero P := by
      apply Fin.ext
      simp only [leftIndex_val, Fin.val_zero, indexZero_val]
    rw [hlast, hzero, signedArea_sub_swap, hdiagonal, neg_zero]
  · intro hx
    -- The common-edge identity places every diagonal point in the right cut region too.
    refine ⟨(left P k hk₁).edgeSet_subset_region (Fin.last k.val) hx, ?_⟩
    apply (right P k hk₁ hk₂).edgeSet_subset_region 0
    rw [← commonEdge P k hk₁ hk₂]
    exact hx

/-- Helper for Definition 76.2: the attaching map reaches every point of its
distinguished target edge. -/
private theorem attachingMapSurjectiveOnRightEdge {m n : ℕ}
    {left : CyclicPolygon m} {right : CyclicPolygon n}
    (gluing : EdgeGluing left right) (y : right.region)
    (hy : (y : EuclideanSpace ℝ (Fin 2)) ∈ right.edgeSet gluing.rightEdge.index) :
    ∃ a : gluing.attachingSubset, gluing.attachingMap a = y := by
  let targetPoint : gluing.rightEdge.segment.carrier :=
    ⟨y, gluing.rightEdge.segment_carrier.symm ▸ hy⟩
  let sourcePoint : gluing.leftEdge.segment.carrier :=
    (gluing.leftEdge.segment.positiveHomeomorph gluing.rightEdge.segment).symm targetPoint
  have hsourceEdge : (sourcePoint : EuclideanSpace ℝ (Fin 2)) ∈
      left.edgeSet gluing.leftEdge.index := by
    rw [← gluing.leftEdge.segment_carrier]
    exact sourcePoint.property
  have hsourceRegion : (sourcePoint : EuclideanSpace ℝ (Fin 2)) ∈ left.region :=
    left.edgeSet_subset_region gluing.leftEdge.index hsourceEdge
  let sourceRegionPoint : left.region := ⟨sourcePoint, hsourceRegion⟩
  have hsourceSelected : sourceRegionPoint ∈ gluing.leftEdge.regionEdge := hsourceEdge
  let a : gluing.attachingSubset := ⟨sourceRegionPoint, hsourceSelected⟩
  refine ⟨a, ?_⟩
  -- The positive segment homeomorphism cancels its inverse at the chosen target point.
  apply Subtype.ext
  rw [gluing.attachingMap_apply]
  have hsegment : gluing.leftEdge.segmentPoint a = sourcePoint := by
    apply Subtype.ext
    rw [gluing.leftEdge.segmentPoint_coe]
  calc
    (gluing.leftEdge.segment.positiveHomeomorph gluing.rightEdge.segment
        (gluing.leftEdge.segmentPoint a) : EuclideanSpace ℝ (Fin 2)) =
        gluing.leftEdge.segment.positiveHomeomorph gluing.rightEdge.segment
          sourcePoint := congrArg Subtype.val (congrArg
            (gluing.leftEdge.segment.positiveHomeomorph gluing.rightEdge.segment) hsegment)
    _ = targetPoint := congrArg Subtype.val
      ((gluing.leftEdge.segment.positiveHomeomorph gluing.rightEdge.segment).apply_symm_apply
        targetPoint)
    _ = y := rfl

/-- Helper for Definition 76.2: a compatible replacement of one polygonal region,
together with an exact union and intersection description, realizes the corresponding
adjunction space. -/
private theorem realizationHomeomorphicToUnion {m n : ℕ}
    {left : CyclicPolygon m} {right : CyclicPolygon n}
    (gluing : EdgeGluing left right)
    (replacement combined : Set (EuclideanSpace ℝ (Fin 2)))
    (H : left.region ≃ₜ replacement)
    (hattaching : ∀ a : gluing.attachingSubset,
      (H a : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap a)
    (hunion : combined = replacement ∪ right.region)
    (hinter : replacement ∩ right.region = right.edgeSet gluing.rightEdge.index) :
    Nonempty (combined ≃ₜ gluing.Realization) := by
  have hreplacement : replacement ⊆ combined := by
    rw [hunion]
    exact subset_union_left
  have hright : right.region ⊆ combined := by
    rw [hunion]
    exact subset_union_right
  let leftMap : C(left.region, combined) :=
    ⟨fun x ↦ ⟨H x, hreplacement (H x).property⟩,
      (continuous_subtype_val.comp H.continuous).subtype_mk _⟩
  let rightMap : C(right.region, combined) :=
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
    apply Subtype.ext
    calc
      (leftMap a : EuclideanSpace ℝ (Fin 2)) = H a := hleftMapCoe a
      _ = gluing.attachingMap a := hattaching a
      _ = (rightMap (gluing.attachingMap a) : EuclideanSpace ℝ (Fin 2)) :=
        (hrightMapCoe (gluing.attachingMap a)).symm
  let gluedMap : gluing.Realization → combined :=
    AdjunctionSpace.lift gluing.attachingSubset gluing.attachingMap leftMap rightMap hglue
  have hgluedContinuous : Continuous gluedMap := by
    -- The quotient eliminator supplies continuity from the two compatible summand maps.
    exact AdjunctionSpace.continuous_lift gluing.attachingSubset gluing.attachingMap
      leftMap rightMap hglue
  have hgluedSurjective : Function.Surjective gluedMap := by
    intro z
    have hzUnion : (z : EuclideanSpace ℝ (Fin 2)) ∈ replacement ∪ right.region := by
      rw [← hunion]
      exact z.property
    rcases hzUnion with hzReplacement | hzRight
    · let zReplacement : replacement := ⟨z, hzReplacement⟩
      obtain ⟨x, hx⟩ := H.surjective zReplacement
      refine ⟨gluing.includeLeft x, ?_⟩
      apply Subtype.ext
      dsimp only [gluedMap]
      rw [gluing.includeLeft_eq_includeX, AdjunctionSpace.lift_includeX, hleftMapCoe]
      exact congrArg Subtype.val hx
    · let zRight : right.region := ⟨z, hzRight⟩
      refine ⟨gluing.includeRight zRight, ?_⟩
      apply Subtype.ext
      dsimp only [gluedMap]
      rw [gluing.includeRight_eq_includeY, AdjunctionSpace.lift_includeY, hrightMapCoe]
  have hcross (x : left.region) (y : right.region) (hxy : leftMap x = rightMap y) :
      AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap x =
        AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap y := by
    have hambient : (H x : EuclideanSpace ℝ (Fin 2)) = y := by
      calc
        (H x : EuclideanSpace ℝ (Fin 2)) =
            (leftMap x : EuclideanSpace ℝ (Fin 2)) := (hleftMapCoe x).symm
        _ = (rightMap y : EuclideanSpace ℝ (Fin 2)) := congrArg Subtype.val hxy
        _ = y := hrightMapCoe y
    have hintersection : (H x : EuclideanSpace ℝ (Fin 2)) ∈
        replacement ∩ right.region :=
      ⟨(H x).property, hambient ▸ y.property⟩
    rw [hinter] at hintersection
    obtain ⟨a, ha⟩ := attachingMapSurjectiveOnRightEdge gluing y
      (hambient ▸ hintersection)
    have hsource : (a : left.region) = x := by
      apply H.injective
      apply Subtype.ext
      calc
        (H a : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap a := hattaching a
        _ = y := congrArg Subtype.val ha
        _ = H x := hambient.symm
    calc
      AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap x =
          AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap a :=
        congrArg (AdjunctionSpace.includeX gluing.attachingSubset gluing.attachingMap)
          hsource.symm
      _ = AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap
          (gluing.attachingMap a) :=
        AdjunctionSpace.glue gluing.attachingSubset gluing.attachingMap a
      _ = AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap y :=
        congrArg (AdjunctionSpace.includeY gluing.attachingSubset gluing.attachingMap) ha
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
  letI : CompactSpace left.region := isCompact_iff_compactSpace.mp (regionIsCompact left)
  letI : CompactSpace right.region := isCompact_iff_compactSpace.mp (regionIsCompact right)
  letI : CompactSpace gluing.Realization := Quotient.compactSpace
  have hhomeomorph : IsHomeomorph gluedMap :=
    (isHomeomorph_iff_continuous_bijective).2
      ⟨hgluedContinuous, hgluedInjective, hgluedSurjective⟩
  -- The compact-to-Hausdorff comparison is constructed in the quotient-to-union direction.
  exact ⟨(hhomeomorph.homeomorph gluedMap).symm⟩

/-- Helper for Definition 76.2: inverse translation takes affine interpolation between
translated endpoints back to interpolation between the original endpoints. -/
private theorem inverseTranslation_lineMap (translation a b : EuclideanSpace ℝ (Fin 2))
    (t : ℝ) :
    (Homeomorph.addRight translation).symm
        (AffineMap.lineMap (Homeomorph.addRight translation a)
          (Homeomorph.addRight translation b) t) =
      AffineMap.lineMap a b t := by
  -- Expand only the affine formula and cancel the common translation vector.
  rw [Homeomorph.addRight_symm]
  simp only [Homeomorph.coe_addRight, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  module

/-- Helper for Definition 76.2: membership in a translated cyclic region is equivalent
to membership of the inverse-translated point in the original region. -/
private theorem mem_translatedRegion_iff_inverseTranslation_mem {n : ℕ}
    (P : CyclicPolygon n) (translation x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ (P.translate translation).region ↔
      (Homeomorph.addRight translation).symm x ∈ P.region := by
  rw [P.translate_region]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [Homeomorph.symm_apply_apply] using hz
  · intro hx
    refine ⟨(Homeomorph.addRight translation).symm x, hx, ?_⟩
    exact (Homeomorph.addRight translation).apply_symm_apply x

/-- Helper for Definition 76.2: undoing the separating translation on the selected
left diagonal agrees with the canonical positive attaching map to the right diagonal. -/
private theorem inverseTranslationAgreesWithCutAttachingMap {n : ℕ}
    (P : CyclicPolygon n) (k : Fin n) (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1)
    (translation : EuclideanSpace ℝ (Fin 2))
    (h_disjoint : Disjoint ((left P k hk₁).translate translation).region
      (right P k hk₁ hk₂).region)
    (a : (edgeGluing P k hk₁ hk₂ translation h_disjoint).attachingSubset) :
    (Homeomorph.addRight translation).symm (a : EuclideanSpace ℝ (Fin 2)) =
      ((edgeGluing P k hk₁ hk₂ translation h_disjoint).attachingMap a :
        EuclideanSpace ℝ (Fin 2)) := by
  let gluing := edgeGluing P k hk₁ hk₂ translation h_disjoint
  have hleftEdge : gluing.leftEdge =
      ({ index := Fin.last k.val, forward := false } :
        ((left P k hk₁).translate translation).DirectedEdge) :=
    edgeGluing_leftEdge P k hk₁ hk₂ translation h_disjoint
  have hrightEdge : gluing.rightEdge =
      ({ index := 0, forward := true } : (right P k hk₁ hk₂).DirectedEdge) :=
    edgeGluing_rightEdge P k hk₁ hk₂ translation h_disjoint
  obtain ⟨t, ht⟩ := gluing.leftEdge.segment.paramHomeomorph.surjective
    (gluing.leftEdge.segmentPoint a)
  have hn : 0 < n := indexZero_isLt P
  have htail : 0 < n - k.val := by
    omega
  have hleftLast : leftIndex k (Fin.last k.val) = k := by
    apply Fin.ext
    simp only [leftIndex_val, Fin.val_last]
  have hleftZero : leftIndex k 0 = indexZero P := by
    apply Fin.ext
    simp only [leftIndex_val, Fin.val_zero, indexZero_val]
  have hrightZero : rightIndex k 0 = indexZero P := by
    apply Fin.ext
    simpa only [indexZero_val] using rightIndex_zero k
  have hrightOne : rightIndex k 1 = k := by
    have hsucc : (⟨0, htail⟩ : Fin (n - k.val)).succ = 1 := by
      apply Fin.ext
      rw [Fin.val_succ]
      have honeLt : 1 < n - k.val + 1 := by
        omega
      exact (Nat.mod_eq_of_lt honeLt).symm
    rw [← hsucc]
    apply Fin.ext
    simpa only [Nat.add_zero] using rightIndex_succ k ⟨0, htail⟩
  have hsourceInitial : gluing.leftEdge.segment.initial =
      Homeomorph.addRight translation (P.toPolygon.vertices (indexZero P)) := by
    rw [gluing.leftEdge.segment_initial, gluing.leftEdge.initial_eq]
    rw [hleftEdge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [finRotate_last, CyclicPolygon.translate_apply, left_apply, hleftZero]
  have hsourceFinal : gluing.leftEdge.segment.final =
      Homeomorph.addRight translation (P.toPolygon.vertices k) := by
    rw [gluing.leftEdge.segment_final, gluing.leftEdge.final_eq]
    rw [hleftEdge]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [CyclicPolygon.translate_apply, left_apply, hleftLast]
  have htargetInitial : gluing.rightEdge.segment.initial =
      P.toPolygon.vertices (indexZero P) := by
    rw [gluing.rightEdge.segment_initial, gluing.rightEdge.initial_eq]
    rw [hrightEdge]
    simp only [↓reduceIte]
    rw [right_apply, hrightZero]
  have htargetFinal : gluing.rightEdge.segment.final = P.toPolygon.vertices k := by
    rw [gluing.rightEdge.segment_final, gluing.rightEdge.final_eq]
    rw [hrightEdge]
    simp only [↓reduceIte]
    rw [finRotate_apply_zero, right_apply, hrightOne]
  -- Both sides preserve the same affine parameter on the diagonal.
  calc
    (Homeomorph.addRight translation).symm (a : EuclideanSpace ℝ (Fin 2)) =
        (Homeomorph.addRight translation).symm
          (gluing.leftEdge.segment.paramHomeomorph t : EuclideanSpace ℝ (Fin 2)) := by
      rw [ht, gluing.leftEdge.segmentPoint_coe]
    _ = (gluing.rightEdge.segment.paramHomeomorph t : EuclideanSpace ℝ (Fin 2)) := by
      rw [OrientedSegment.paramHomeomorph_apply, OrientedSegment.paramHomeomorph_apply,
        hsourceInitial, hsourceFinal, htargetInitial, htargetFinal,
        inverseTranslation_lineMap]
    _ = (gluing.leftEdge.segment.positiveHomeomorph gluing.rightEdge.segment
          (gluing.leftEdge.segmentPoint a) : EuclideanSpace ℝ (Fin 2)) := by
      rw [← ht, OrientedSegment.positiveHomeomorph_apply]
    _ = (gluing.attachingMap a : EuclideanSpace ℝ (Fin 2)) := by
      rw [gluing.attachingMap_apply]

/-- For an explicit translation separating the two cut regions, positively gluing the
translated edge from `q₀` to `qₖ` to the right edge from `p₀` to `pₖ` recovers
`P.region` up to homeomorphism. -/
theorem regionHomeomorphicRealization {n : ℕ} (P : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1)
    (translation : EuclideanSpace ℝ (Fin 2))
    (h_disjoint : Disjoint ((left P k hk₁).translate translation).region
      (right P k hk₁ hk₂).region) :
    Nonempty (P.region ≃ₜ (edgeGluing P k hk₁ hk₂ translation h_disjoint).Realization) := by
  let gluing := edgeGluing P k hk₁ hk₂ translation h_disjoint
  let H : ((left P k hk₁).translate translation).region ≃ₜ (left P k hk₁).region :=
    (Homeomorph.addRight translation).symm.subtype
      (fun x ↦ mem_translatedRegion_iff_inverseTranslation_mem
        (left P k hk₁) translation x)
  have hHCoe (x : ((left P k hk₁).translate translation).region) :
      (H x : EuclideanSpace ℝ (Fin 2)) =
        (Homeomorph.addRight translation).symm x := by
    rfl
  have hattaching : ∀ a : gluing.attachingSubset,
      (H a : EuclideanSpace ℝ (Fin 2)) = gluing.attachingMap a := by
    intro a
    rw [hHCoe]
    exact inverseTranslationAgreesWithCutAttachingMap P k hk₁ hk₂ translation
      h_disjoint a
  have hunion : P.region = (left P k hk₁).region ∪ (right P k hk₁ hk₂).region :=
    region_eq_union P k hk₁ hk₂
  have hinter : (left P k hk₁).region ∩ (right P k hk₁ hk₂).region =
      (right P k hk₁ hk₂).edgeSet gluing.rightEdge.index := by
    rw [cutRegionsInterEqLeftDiagonal P k hk₁ hk₂, commonEdge P k hk₁ hk₂]
    -- Normalize the opaque gluing projection through its owner-side computation rule.
    rw [edgeGluing_rightEdge P k hk₁ hk₂ translation h_disjoint]
  -- Apply the quotient-to-union interface to inverse translation and the exact cut equations.
  exact realizationHomeomorphicToUnion gluing (left P k hk₁).region P.region H
    hattaching hunion hinter

/-- Definition 76.2: The left polygon from the canonical cut can be translated to a
region disjoint from the right polygon. Positively gluing its translated diagonal to
the right diagonal then recovers `P.region` up to homeomorphism. -/
theorem existsSeparatingTranslation {n : ℕ} (P : CyclicPolygon n) (k : Fin n)
    (hk₁ : 1 < k.val) (hk₂ : k.val < n - 1) :
    ∃ (translation : EuclideanSpace ℝ (Fin 2))
      (h_disjoint : Disjoint ((left P k hk₁).translate translation).region
        (right P k hk₁ hk₂).region),
      Nonempty
        (P.region ≃ₜ (edgeGluing P k hk₁ hk₂ translation h_disjoint).Realization) := by
  -- First separate the compact cut regions, then invoke the fixed-translation comparison.
  obtain ⟨translation, h_disjoint⟩ :=
    existsDisjointTranslatedRegion (left P k hk₁) (right P k hk₁ hk₂)
  exact ⟨translation, h_disjoint,
    regionHomeomorphicRealization P k hk₁ hk₂ translation h_disjoint⟩

end

end CyclicPolygon.Cut
