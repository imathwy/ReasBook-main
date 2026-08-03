module

public import Topology_Munkres_2000.Book.Exercise_36_5.Charts
public import Topology_Munkres_2000.Book.Exercise_64_1.ArcFamily

public section

open Set

universe u v

/-- Helper for Exercise 64.1: a finite closed cover by Hausdorff subspaces with
subsingleton pairwise intersections has Hausdorff union. -/
private lemma t2Space_of_finite_closed_cover_of_subsingleton_inter
    {X : Type u} {ι : Type v} [TopologicalSpace X] [Finite ι]
    (F : ι → Set X) [∀ i, T2Space (F i)]
    (h_closed : ∀ i, IsClosed (F i)) (h_cover : ⋃ i, F i = Set.univ)
    (h_inter : ∀ {i j}, i ≠ j → (F i ∩ F j).Subsingleton) :
    T2Space X := by
  classical
  -- Each part of the ambient diagonal is closed in its product rectangle.
  have h_piece_closed (i j : ι) :
      IsClosed ((Prod.map ((↑) : F i → X) ((↑) : F j → X)) ''
        {z : F i × F j | (z.1 : X) = z.2}) := by
    have h_embedding : Topology.IsClosedEmbedding
        (Prod.map ((↑) : F i → X) ((↑) : F j → X)) :=
      (h_closed i).isClosedEmbedding_subtypeVal.prodMap
        (h_closed j).isClosedEmbedding_subtypeVal
    rw [← h_embedding.isClosed_iff_image_isClosed]
    by_cases hij : i = j
    · subst j
      have h_equal_piece :
          {z : F i × F i | (z.1 : X) = z.2} = diagonal (F i) := by
        ext z
        simp only [mem_setOf_eq, mem_diagonal_iff, Subtype.ext_iff]
      rw [h_equal_piece]
      exact isClosed_diagonal
    · have h_subsingleton :
          {z : F i × F j | (z.1 : X) = z.2}.Subsingleton := by
        intro a ha b hb
        have ha_inter : (a.1 : X) ∈ F i ∩ F j := by
          exact ⟨a.1.property, ha ▸ a.2.property⟩
        have hb_inter : (b.1 : X) ∈ F i ∩ F j := by
          exact ⟨b.1.property, hb ▸ b.2.property⟩
        have hab : (a.1 : X) = b.1 := h_inter hij ha_inter hb_inter
        apply Prod.ext
        · exact Subtype.ext hab
        · exact Subtype.ext (ha.symm.trans (hab.trans hb))
      exact h_subsingleton.isClosed
  -- The cover decomposes the whole diagonal into the finitely many closed pieces above.
  have h_diagonal : diagonal X = ⋃ p : ι × ι,
      (Prod.map ((↑) : F p.1 → X) ((↑) : F p.2 → X)) ''
        {z : F p.1 × F p.2 | (z.1 : X) = z.2} := by
    ext z
    constructor
    · intro hz
      have hz_eq : z.1 = z.2 := mem_diagonal_iff.mp hz
      have hz_first : z.1 ∈ ⋃ i, F i := by
        rw [h_cover]
        exact mem_univ z.1
      have hz_second : z.2 ∈ ⋃ i, F i := by
        rw [h_cover]
        exact mem_univ z.2
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz_first
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hz_second
      refine mem_iUnion.mpr ⟨(i, j), ?_⟩
      refine ⟨(⟨z.1, hzi⟩, ⟨z.2, hzj⟩), hz_eq, ?_⟩
      rfl
    · intro hz
      obtain ⟨p, hp⟩ := mem_iUnion.mp hz
      obtain ⟨w, hw, rfl⟩ := hp
      exact mem_diagonal_iff.mpr hw
  rw [t2_iff_isClosed_diagonal, h_diagonal]
  exact isClosed_iUnion_of_finite fun p ↦ h_piece_closed p.1 p.2

/-- Exercise 64.1 (1). A space covered by finitely many arcs that meet only at common
endpoints is Hausdorff exactly when every arc in the cover is closed. -/
theorem hausdorff_iff_arcs_closed {X : Type u} {ι : Type v} [TopologicalSpace X]
    [Finite ι] (A : ι → Set X) [∀ i, Topology.IsArc (A i)]
    (h_cover : ⋃ i, A i = Set.univ) (h_meet : Topology.ArcFamily.MeetAtEndpoints A) :
    T2Space X ↔ ∀ i, IsClosed (A i) := by
  constructor
  · intro hT2 i
    letI : T2Space X := hT2
    obtain ⟨e⟩ := (inferInstance : Topology.IsArc (A i)).homeomorphic_unitInterval
    -- Arc coordinates transport compactness from the unit interval, so Hausdorffness closes it.
    exact (isCompact_iff_compactSpace.mpr e.symm.compactSpace).isClosed
  · intro h_closed
    classical
    letI : ∀ i, T2Space (A i) := fun i ↦
      (Classical.choice
        (inferInstance : Topology.IsArc (A i)).homeomorphic_unitInterval).symm.t2Space
    -- The endpoint hypothesis supplies precisely the subsingleton intersections for gluing.
    exact t2Space_of_finite_closed_cover_of_subsingleton_inter A h_closed h_cover
      (fun hij ↦ Topology.ArcFamily.inter_subsingleton A h_meet hij)

namespace LineWithTwoOrigins

namespace SplitInterval

/-- The left half of the bounded split interval, containing the origin `p`. -/
@[expose] def leftSegment : Set LineWithTwoOrigins
  | .point x _ => x ∈ Icc (-1) 0
  | .origin .p => True
  | .origin .q => False

/-- The right half of the bounded split interval, containing the origin `q`. -/
@[expose] def rightSegment : Set LineWithTwoOrigins
  | .point x _ => x ∈ Icc 0 1
  | .origin .p => False
  | .origin .q => True

/-- The bounded split interval inside the line with two origins. -/
@[expose] def carrier : Set LineWithTwoOrigins := leftSegment ∪ rightSegment

end SplitInterval

/-- The bounded split interval, regarded as a subspace of the line with two origins. -/
abbrev SplitInterval := SplitInterval.carrier

namespace SplitInterval

/-- The left arc in the bounded split interval. -/
@[expose] def leftArc : Set LineWithTwoOrigins.SplitInterval :=
  Subtype.val ⁻¹' leftSegment

/-- The right arc in the bounded split interval. -/
@[expose] def rightArc : Set LineWithTwoOrigins.SplitInterval :=
  Subtype.val ⁻¹' rightSegment

/-- The two arcs covering the bounded split interval. -/
@[expose] def arcs (i : Fin 2) : Set LineWithTwoOrigins.SplitInterval :=
  if i = 0 then leftArc else rightArc

/-- Helper for Exercise 64.1: the deleted-origin homeomorphism computes as the real
coordinate map. -/
private lemma removeOriginHomeomorphReal_apply (o : Origin)
    (z : {z : LineWithTwoOrigins | z ≠ origin o}) :
    removeOriginHomeomorphReal o z = toReal z := by
  -- The chart inverse formula supplies the missing public computation rule for its forward map.
  have h_inverse : (removeOriginHomeomorphReal o).symm (toReal z) = z := by
    apply Subtype.ext
    simpa only [realHomeomorphEuclideanOne.symm_apply_apply] using
      chartLeftInv o z z.property
  calc
    removeOriginHomeomorphReal o z =
        removeOriginHomeomorphReal o ((removeOriginHomeomorphReal o).symm (toReal z)) :=
      congrArg (removeOriginHomeomorphReal o) h_inverse.symm
    _ = toReal z := (removeOriginHomeomorphReal o).apply_symm_apply (toReal z)

/-- Helper for Exercise 64.1: away from `q`, membership in the left segment is the
coordinate condition `toReal z ∈ Icc (-1) 0`. -/
private lemma mem_leftSegment_iff_toReal {z : LineWithTwoOrigins}
    (hz : z ≠ origin .q) : z ∈ leftSegment ↔ toReal z ∈ Icc (-1) 0 := by
  -- The only exceptional coordinate-zero point is the deleted origin `q`.
  cases z with
  | point x hx =>
      calc
        point x hx ∈ leftSegment ↔ x ∈ Icc (-1) 0 :=
          iff_of_eq (leftSegment.eq_1 x hx)
        _ ↔ toReal (point x hx) ∈ Icc (-1) 0 := by rw [toReal_point]
  | origin o =>
      cases o with
      | p =>
          calc
            origin .p ∈ leftSegment ↔ True := iff_of_eq leftSegment.eq_2
            _ ↔ toReal (origin .p) ∈ Icc (-1) 0 := by
              rw [toReal_origin]
              norm_num
      | q => exact (hz rfl).elim

/-- Helper for Exercise 64.1: away from `p`, membership in the right segment is the
coordinate condition `toReal z ∈ Icc 0 1`. -/
private lemma mem_rightSegment_iff_toReal {z : LineWithTwoOrigins}
    (hz : z ≠ origin .p) : z ∈ rightSegment ↔ toReal z ∈ Icc 0 1 := by
  -- The deleted origin `p` is the sole coordinate-zero exception on this side.
  cases z with
  | point x hx =>
      calc
        point x hx ∈ rightSegment ↔ x ∈ Icc 0 1 :=
          iff_of_eq (rightSegment.eq_1 x hx)
        _ ↔ toReal (point x hx) ∈ Icc 0 1 := by rw [toReal_point]
  | origin o =>
      cases o with
      | p => exact (hz rfl).elim
      | q =>
          calc
            origin .q ∈ rightSegment ↔ True := iff_of_eq rightSegment.eq_3
            _ ↔ toReal (origin .q) ∈ Icc 0 1 := by
              rw [toReal_origin]
              norm_num

/-- Helper for Exercise 64.1: the left arc has the standard unit-interval coordinates. -/
private lemma leftArc_homeomorphic_unitInterval :
    Nonempty (leftArc ≃ₜ unitInterval) := by
  -- First flatten the nested subtype from the bounded interval to the ambient left segment.
  have h_left_carrier : leftSegment ⊆ Set.range
      ((↑) : LineWithTwoOrigins.SplitInterval → LineWithTwoOrigins) := by
    intro z hz
    have hz_carrier : z ∈ carrier := Or.inl hz
    exact ⟨⟨z, hz_carrier⟩, rfl⟩
  have e_flat : leftArc ≃ₜ leftSegment :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange h_left_carrier
  -- The left segment avoids `q`, so deleted-origin coordinates are available on all of it.
  have h_left_deleted :
      leftSegment ⊆ Set.range ((↑) : {z : LineWithTwoOrigins | z ≠ origin .q} →
        LineWithTwoOrigins) := by
    intro z hz
    have hzq : z ≠ origin .q := by
      cases z with
      | point x hx => exact point_ne_origin x hx .q
      | origin o =>
          cases o with
          | p =>
              intro h
              exact Origin.noConfusion (origin.inj h)
          | q => exact hz.elim
    exact ⟨⟨z, hzq⟩, rfl⟩
  have e_deleted :
      {z : {z : LineWithTwoOrigins | z ≠ origin .q} |
        (z : LineWithTwoOrigins) ∈ leftSegment} ≃ₜ leftSegment :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange h_left_deleted
  -- In the deleted-origin chart, the segment is exactly the real interval `[-1, 0]`.
  have h_coordinate (z : {z : LineWithTwoOrigins | z ≠ origin .q}) :
      (z : LineWithTwoOrigins) ∈ leftSegment ↔
        removeOriginHomeomorphReal .q z ∈ Icc (-1) 0 := by
    rw [removeOriginHomeomorphReal_apply]
    exact mem_leftSegment_iff_toReal z.property
  have e_coordinate :
      {z : {z : LineWithTwoOrigins | z ≠ origin .q} |
        (z : LineWithTwoOrigins) ∈ leftSegment} ≃ₜ Icc (-1 : ℝ) 0 :=
    (removeOriginHomeomorphReal .q).subtype h_coordinate
  exact ⟨e_flat.trans (e_deleted.symm.trans
    (e_coordinate.trans (iccHomeoI (-1 : ℝ) 0 neg_one_lt_zero)))⟩

/-- Helper for Exercise 64.1: the right arc has the standard unit-interval coordinates. -/
private lemma rightArc_homeomorphic_unitInterval :
    Nonempty (rightArc ≃ₜ unitInterval) := by
  -- Flatten the nested subtype and then pass to the chart obtained by deleting `p`.
  have h_right_carrier : rightSegment ⊆ Set.range
      ((↑) : LineWithTwoOrigins.SplitInterval → LineWithTwoOrigins) := by
    intro z hz
    have hz_carrier : z ∈ carrier := Or.inr hz
    exact ⟨⟨z, hz_carrier⟩, rfl⟩
  have e_flat : rightArc ≃ₜ rightSegment :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange h_right_carrier
  have h_right_deleted :
      rightSegment ⊆ Set.range ((↑) : {z : LineWithTwoOrigins | z ≠ origin .p} →
        LineWithTwoOrigins) := by
    intro z hz
    have hzp : z ≠ origin .p := by
      cases z with
      | point x hx => exact point_ne_origin x hx .p
      | origin o =>
          cases o with
          | p => exact hz.elim
          | q =>
              intro h
              exact Origin.noConfusion (origin.inj h)
    exact ⟨⟨z, hzp⟩, rfl⟩
  have e_deleted :
      {z : {z : LineWithTwoOrigins | z ≠ origin .p} |
        (z : LineWithTwoOrigins) ∈ rightSegment} ≃ₜ rightSegment :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange h_right_deleted
  -- Deleted-origin coordinates identify the remaining predicate with `[0, 1]`.
  have h_coordinate (z : {z : LineWithTwoOrigins | z ≠ origin .p}) :
      (z : LineWithTwoOrigins) ∈ rightSegment ↔
        removeOriginHomeomorphReal .p z ∈ Icc 0 1 := by
    rw [removeOriginHomeomorphReal_apply]
    exact mem_rightSegment_iff_toReal z.property
  have e_coordinate :
      {z : {z : LineWithTwoOrigins | z ≠ origin .p} |
        (z : LineWithTwoOrigins) ∈ rightSegment} ≃ₜ Icc (0 : ℝ) 1 :=
    (removeOriginHomeomorphReal .p).subtype h_coordinate
  exact ⟨e_flat.trans (e_deleted.symm.trans
    (e_coordinate.trans (iccHomeoI (0 : ℝ) 1 zero_lt_one)))⟩

/-- Each member of the canonical two-set cover of the bounded split interval is an arc. -/
instance instIsArc (i : Fin 2) : Topology.IsArc (arcs i) := by
  -- The finite enumeration reduces the family to the two coordinate lemmas above.
  constructor
  fin_cases i
  · exact leftArc_homeomorphic_unitInterval
  · exact rightArc_homeomorphic_unitInterval

/-- The canonical two arcs cover the bounded split interval. -/
theorem arcs_cover : ⋃ i, arcs i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  -- The carrier definition assigns every point to at least one of the two indexed arcs.
  rcases x.property with hleft | hright
  · exact mem_iUnion.mpr ⟨0, hleft⟩
  · exact mem_iUnion.mpr ⟨1, hright⟩

/-- Helper for Exercise 64.1: the ambient left and right segments are disjoint. -/
private lemma leftSegment_inter_rightSegment : leftSegment ∩ rightSegment = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  rcases hz with ⟨hleft, hright⟩
  -- Ordinary points would have coordinate zero, while each origin is omitted by one segment.
  cases z with
  | point x hx =>
      have hxleft : x ∈ Icc (-1) 0 :=
        (iff_of_eq (leftSegment.eq_1 x hx)).mp hleft
      have hxright : x ∈ Icc 0 1 :=
        (iff_of_eq (rightSegment.eq_1 x hx)).mp hright
      exact hx (le_antisymm hxleft.2 hxright.1)
  | origin o =>
      cases o with
      | p => exact (iff_of_eq rightSegment.eq_2).mp hright
      | q => exact (iff_of_eq leftSegment.eq_3).mp hleft

/-- Helper for Exercise 64.1: the two canonical arcs have empty intersection. -/
private lemma leftArc_inter_rightArc : leftArc ∩ rightArc = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  -- Forgetting the bounded-interval subtype sends a common point to both ambient segments.
  exact Set.eq_empty_iff_forall_notMem.mp leftSegment_inter_rightSegment x
    ⟨hx.1, hx.2⟩

/-- Helper for Exercise 64.1: distinct members of the two-arc family are disjoint. -/
private lemma arcs_inter_eq_empty {i j : Fin 2} (hij : i ≠ j) :
    arcs i ∩ arcs j = ∅ := by
  -- There are only the two possible orders of the left and right arcs.
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact leftArc_inter_rightArc
  · calc
      rightArc ∩ leftArc = leftArc ∩ rightArc := inter_comm rightArc leftArc
      _ = ∅ := leftArc_inter_rightArc
  · exact (hij rfl).elim

/-- The canonical two arcs satisfy the common-endpoint intersection condition. -/
theorem arcs_meetAtEndpoints : Topology.ArcFamily.MeetAtEndpoints arcs := by
  -- Route correction: use the owner module's constructor because the imported predicate is opaque.
  refine Topology.ArcFamily.meetAtEndpoints_of arcs ?_ ?_
  · intro i j hij
    -- Distinct members are disjoint, hence their intersection is subsingleton.
    rw [arcs_inter_eq_empty hij]
    exact subsingleton_empty
  · intro i j hij x hxi hxj
    -- A hypothetical common point lies in the already-proved empty intersection.
    have hx : x ∈ arcs i ∩ arcs j := ⟨hxi, hxj⟩
    rw [arcs_inter_eq_empty hij] at hx
    exact hx.elim

/-- Helper for Exercise 64.1: the second origin belongs to the bounded split interval. -/
private lemma originQ_mem_carrier : origin .q ∈ carrier := by
  -- The second origin is the distinguished endpoint of the right segment.
  have hright : origin .q ∈ rightSegment :=
    (iff_of_eq rightSegment.eq_3).mpr True.intro
  exact Or.inr hright

/-- Helper for Exercise 64.1: the second origin lies in the ambient closure of the left
segment. -/
private lemma originQ_mem_closure_leftSegment : origin .q ∈ closure leftSegment := by
  rw [basis_isTopologicalBasis.mem_closure_iff]
  intro s hs hqs
  -- An ambient interval contains no origin; a neighborhood of `q` contains a small
  -- negative ordinary point from the left segment.
  rcases mem_basis_iff.mp hs with
      ⟨l, r, _, _, rfl⟩ | ⟨o, a, ha, rfl⟩
  · exact (origin_not_mem_interval .q l r hqs).elim
  · rcases mem_originNeighborhood_iff.mp hqs with hinterval | horigin
    · exact (origin_not_mem_interval .q (-a) a hinterval).elim
    · have ho : Origin.q = o := origin.inj horigin
      subst o
      let c : ℝ := min a 1 / 2
      have hmin_pos : 0 < min a 1 := lt_min ha zero_lt_one
      have hc_pos : 0 < c := by
        dsimp [c]
        positivity
      have hc_lt_a : c < a := by
        dsimp [c]
        have hmin_le_a : min a 1 ≤ a := min_le_left a 1
        linarith
      have hc_le_one : c ≤ 1 := by
        dsimp [c]
        have hmin_le_one : min a 1 ≤ 1 := min_le_right a 1
        linarith
      have hnegative_ne : -c ≠ 0 := neg_ne_zero.mpr (ne_of_gt hc_pos)
      have hnegative_ne_q : point (-c) hnegative_ne ≠ origin .q :=
        point_ne_origin (-c) hnegative_ne .q
      have hleft_lower : (-1 : ℝ) ≤ -c := neg_le_neg hc_le_one
      have hleft_upper : -c ≤ 0 := neg_nonpos.mpr hc_pos.le
      have hleft_coordinate : toReal (point (-c) hnegative_ne) ∈ Icc (-1) 0 := by
        rw [toReal_point]
        exact ⟨hleft_lower, hleft_upper⟩
      have hleft : point (-c) hnegative_ne ∈ leftSegment :=
        (mem_leftSegment_iff_toReal hnegative_ne_q).mpr hleft_coordinate
      have hlower : -a < -c := neg_lt_neg hc_lt_a
      have hupper : -c < a := (neg_lt_zero.mpr hc_pos).trans ha
      have hinterval_mem : point (-c) hnegative_ne ∈ interval (-a) a :=
        (point_mem_interval_iff hnegative_ne).mpr ⟨hlower, hupper⟩
      have hneighborhood : point (-c) hnegative_ne ∈ originNeighborhood .q a :=
        mem_originNeighborhood_iff.mpr (Or.inl hinterval_mem)
      exact ⟨point (-c) hnegative_ne, hneighborhood, hleft⟩

/-- Helper for Exercise 64.1: forgetting the split-interval subtype maps the left arc
onto the ambient left segment. -/
private lemma image_val_leftArc :
    ((↑) : LineWithTwoOrigins.SplitInterval → LineWithTwoOrigins) '' leftArc = leftSegment := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    have hz_carrier : z ∈ carrier := Or.inl hz
    refine ⟨⟨z, hz_carrier⟩, ?_, rfl⟩
    exact hz

/-- Helper for Exercise 64.1: the left arc is not closed in the bounded split interval. -/
private lemma not_isClosed_leftArc : ¬ IsClosed leftArc := by
  intro hclosed
  let qSplit : LineWithTwoOrigins.SplitInterval := ⟨origin .q, originQ_mem_carrier⟩
  -- Subtype closure transports the ambient limit point to the bounded interval.
  have hclosure : qSplit ∈ closure leftArc := by
    rw [closure_subtype, image_val_leftArc]
    exact originQ_mem_closure_leftSegment
  have hnotmem : qSplit ∉ leftArc := by
    intro hmem
    have hfalse : False := (iff_of_eq leftSegment.eq_3).mp hmem
    exact hfalse.elim
  rw [hclosed.closure_eq] at hclosure
  exact hnotmem hclosure

/-- Exercise 64.1 (2). The bounded split interval is a finite union of arcs satisfying
the common-endpoint condition, but it is not Hausdorff. -/
theorem notHausdorff : ¬ T2Space LineWithTwoOrigins.SplitInterval := by
  intro hT2
  -- The criterion from part (1) would make the left member of the canonical cover closed.
  have hclosed : ∀ i, IsClosed (arcs i) :=
    (hausdorff_iff_arcs_closed arcs arcs_cover arcs_meetAtEndpoints).mp hT2
  exact not_isClosed_leftArc (hclosed 0)

end SplitInterval

end LineWithTwoOrigins
