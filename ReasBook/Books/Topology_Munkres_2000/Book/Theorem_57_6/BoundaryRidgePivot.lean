module

public import Topology_Munkres_2000.Book.Remark_50_3.CubicalIncidence

public section

noncomputable section

namespace StandardSphere.CubicalTucker

/-- Helper for Theorem 57.6: reflect a boundary shared facet and exchange its
top and bottom boundary tags. -/
def BoundarySharedFacet.reflect {d m : ℕ} :
    BoundarySharedFacet d m → BoundarySharedFacet d m :=
  fun
  | Sum.inl top => Sum.inr (SharedFacet.reflectTopBoundary top)
  | Sum.inr bottom => Sum.inl (SharedFacet.reflectBottomBoundary bottom)

/-- Helper for Theorem 57.6: reflecting a top-tagged facet produces the
corresponding reflected bottom-tagged facet. -/
theorem BoundarySharedFacet.reflect_inl {d m : ℕ}
    (top : TopBoundaryNormalizedSharedFacet d m) :
    BoundarySharedFacet.reflect (Sum.inl top) =
      Sum.inr (SharedFacet.reflectTopBoundary top) := by
  -- Evaluate the top branch of boundary reflection.
  rfl

/-- Helper for Theorem 57.6: reflecting a bottom-tagged facet produces the
corresponding reflected top-tagged facet. -/
theorem BoundarySharedFacet.reflect_inr {d m : ℕ}
    (bottom : BottomBoundaryNormalizedSharedFacet d m) :
    BoundarySharedFacet.reflect (Sum.inr bottom) =
      Sum.inl (SharedFacet.reflectBottomBoundary bottom) := by
  -- Evaluate the bottom branch of boundary reflection.
  rfl

/-- Helper for Theorem 57.6: reflecting a boundary shared facet twice returns
the original tagged facet. -/
theorem BoundarySharedFacet.reflect_involutive {d m : ℕ} :
    Function.Involutive
      (BoundarySharedFacet.reflect : BoundarySharedFacet d m →
        BoundarySharedFacet d m) := by
  -- Reduce each boundary tag to the corresponding owner-level inverse law.
  intro facet
  cases facet with
  | inl top =>
      exact congrArg Sum.inl
        (SharedFacet.reflectBottomBoundary_reflectTopBoundary top)
  | inr bottom =>
      exact congrArg Sum.inr
        (SharedFacet.reflectTopBoundary_reflectBottomBoundary bottom)

/-- Helper for Theorem 57.6: boundary-facet reflection negates every vertex
and reverses its staircase index. -/
theorem BoundarySharedFacet.reflect_vertex {d m : ℕ}
    (facet : BoundarySharedFacet d m) (j : Fin (d + 1)) :
    facet.reflect.vertex j = centeredGridNeg (facet.vertex (Fin.rev j)) := by
  -- Forget the boundary tag and apply the normalized shared-facet formula.
  cases facet with
  | inl top =>
      rw [BoundarySharedFacet.reflect_inl,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.reflectTopBoundary_val]
      exact SharedFacet.reflect_vertex top.1 j
  | inr bottom =>
      rw [BoundarySharedFacet.reflect_inr,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.reflectBottomBoundary_val]
      exact SharedFacet.reflect_vertex bottom.1 j

/-- Helper for Theorem 57.6: every boundary facet lies in the closed positive
hemisphere, or its reflected facet does. -/
theorem BoundarySharedFacet.positive_or_reflect_positive {d m : ℕ}
    (facet : BoundarySharedFacet d m) :
    (∀ j, centeredGridPositiveHemisphere (facet.vertex j)) ∨
      ∀ j, centeredGridPositiveHemisphere (facet.reflect.vertex j) := by
  -- If one vertex is strictly below the equator, all vertices of this simplex
  -- are at or below it; reflection therefore puts the whole facet above it.
  by_cases hpositive : ∀ j, centeredGridPositiveHemisphere (facet.vertex j)
  · exact Or.inl hpositive
  · right
    push Not at hpositive
    obtain ⟨j, hj⟩ := hpositive
    intro k
    rw [facet.reflect_vertex k, centeredGridNeg_positiveHemisphere_iff]
    have hjlt : (facet.vertex j 0).1 < m := by
      exact Nat.lt_of_not_ge (fun hjge ↦
        hj ((centeredGridPositiveHemisphere_iff _).mpr hjge))
    have hneighbor :=
      facet.normalizedFacet.1.vertices_neighbor j (Fin.rev k) (0 : Fin (d + 1))
    rw [← facet.vertex_eq_normalizedFacet,
      ← facet.vertex_eq_normalizedFacet] at hneighbor
    exact (centeredGridNegativeHemisphere_iff _).mpr (by omega)

/-- Helper for Theorem 57.6: an extreme normalized facet has a vertex away
from the equator when the centered grid has positive radius. -/
theorem SharedFacet.exists_vertex_ne_equator_of_level_extreme {d m : ℕ}
    (hm : 0 < m) (facet : NormalizedSharedFacet d m)
    (hlevel : facet.1.level.1 = 0 ∨ facet.1.level.1 = 2 * m) :
    ∃ j : Fin (d + 1), (facet.1.vertex j 0).1 ≠ m := by
  -- If the hemisphere coordinate is fixed, its extreme level is not the
  -- equator; otherwise its first and last vertices differ by one there.
  by_cases hfixed : (0 : Fin (d + 1)) = facet.1.fixed
  · refine ⟨0, ?_⟩
    rw [facet.1.vertex_value, if_pos hfixed]
    omega
  · by_contra hall
    push Not at hall
    have hrank : facet.1.leadingOrder.symm (0 : Fin (d + 1)) ≠ 0 :=
      facet.1.leadingOrder_symm_ne_zero hfixed
    have hrankPos :
        0 < (facet.1.leadingOrder.symm (0 : Fin (d + 1))).1 :=
      Fin.pos_iff_ne_zero.mpr hrank
    have hrankLt :=
      (facet.1.leadingOrder.symm (0 : Fin (d + 1))).isLt
    have hfirst := hall (0 : Fin (d + 1))
    have hlast := hall (Fin.last d)
    rw [facet.1.vertex_value, if_neg hfixed,
      if_neg (by simp only [Fin.val_zero]; omega)] at hfirst
    rw [facet.1.vertex_value, if_neg hfixed,
      if_pos (by simp only [Fin.val_last]; omega)] at hlast
    omega

/-- Helper for Theorem 57.6: a positive boundary facet and its reflection
cannot both lie in the positive hemisphere at positive grid radius. -/
theorem BoundarySharedFacet.not_positive_and_reflect_positive {d m : ℕ}
    (hm : 0 < m) (facet : BoundarySharedFacet d m) :
    ¬((∀ j, centeredGridPositiveHemisphere (facet.vertex j)) ∧
      ∀ j, centeredGridPositiveHemisphere (facet.reflect.vertex j)) := by
  -- Both hemisphere conditions would put every original vertex exactly on
  -- the equator, contradicting the extreme-facet vertex supplied above.
  rintro ⟨hpositive, hreflectPositive⟩
  have hallEquator (j : Fin (d + 1)) : (facet.vertex j 0).1 = m := by
    apply Nat.le_antisymm
    · apply (centeredGridNegativeHemisphere_iff _).mp
      apply (centeredGridNeg_positiveHemisphere_iff _).mp
      simpa only [facet.reflect_vertex, Fin.rev_rev] using
        hreflectPositive (Fin.rev j)
    · exact (centeredGridPositiveHemisphere_iff _).mp (hpositive j)
  cases facet with
  | inl top =>
      obtain ⟨j, hj⟩ :=
        SharedFacet.exists_vertex_ne_equator_of_level_extreme hm top.1
          (Or.inr top.2)
      apply hj
      simpa only [BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl] using hallEquator j
  | inr bottom =>
      obtain ⟨j, hj⟩ :=
        SharedFacet.exists_vertex_ne_equator_of_level_extreme hm bottom.1
          (Or.inl bottom.2)
      apply hj
      simpa only [BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr] using hallEquator j

/-- Helper for Theorem 57.6: choose the positive representative of a boundary
facet reflection orbit and record whether reflection was required. -/
def boundaryFacetHemisphereSplit {d m : ℕ}
    (facet : BoundarySharedFacet d m) :
    PositiveHemisphereBoundaryFacet d m ⊕
      PositiveHemisphereBoundaryFacet d m :=
  @dite (PositiveHemisphereBoundaryFacet d m ⊕
      PositiveHemisphereBoundaryFacet d m)
    (∀ j, centeredGridPositiveHemisphere (facet.vertex j)) (Classical.dec _)
    (fun hpositive ↦ Sum.inl ⟨facet, hpositive⟩)
    (fun hpositive ↦ Sum.inr ⟨facet.reflect,
      facet.positive_or_reflect_positive.resolve_left hpositive⟩)

/-- Helper for Theorem 57.6: forget the hemisphere branch, reflecting the
representative recorded in the second branch. -/
def boundaryFacetHemisphereJoin {d m : ℕ} :
    PositiveHemisphereBoundaryFacet d m ⊕
        PositiveHemisphereBoundaryFacet d m →
      BoundarySharedFacet d m :=
  Sum.elim Subtype.val (fun facet ↦ facet.1.reflect)

/-- Helper for Theorem 57.6: splitting and then joining a boundary facet
returns that facet. -/
theorem boundaryFacetHemisphereJoin_split {d m : ℕ}
    (facet : BoundarySharedFacet d m) :
    boundaryFacetHemisphereJoin (boundaryFacetHemisphereSplit facet) =
      facet := by
  -- The positive branch is unchanged; the other branch reflects twice.
  unfold boundaryFacetHemisphereSplit
  split_ifs
  · rfl
  · exact facet.reflect_involutive

/-- Helper for Theorem 57.6: joining and then splitting a tagged positive
representative preserves its hemisphere branch. -/
theorem boundaryFacetHemisphereSplit_join {d m : ℕ} (hm : 0 < m)
    (facet : PositiveHemisphereBoundaryFacet d m ⊕
      PositiveHemisphereBoundaryFacet d m) :
    boundaryFacetHemisphereSplit (boundaryFacetHemisphereJoin facet) =
      facet := by
  -- A first-branch representative is positive.  A second-branch
  -- representative must select the reflected branch by exclusivity.
  cases facet with
  | inl facet =>
      simp only [boundaryFacetHemisphereJoin, Sum.elim_inl]
      unfold boundaryFacetHemisphereSplit
      rw [dif_pos facet.2]
  | inr facet =>
      simp only [boundaryFacetHemisphereJoin, Sum.elim_inr]
      have hnotPositive :
          ¬∀ j, centeredGridPositiveHemisphere (facet.1.reflect.vertex j) := by
        intro hreflect
        exact facet.1.not_positive_and_reflect_positive hm ⟨facet.2, hreflect⟩
      unfold boundaryFacetHemisphereSplit
      rw [dif_neg hnotPositive]
      apply congrArg Sum.inr
      apply Subtype.ext
      exact facet.1.reflect_involutive

/-- Helper for Theorem 57.6: all boundary facets are canonically two copies
of the facets in the positive closed hemisphere. -/
def boundaryFacetHemisphereEquiv {d m : ℕ} (hm : 0 < m) :
    BoundarySharedFacet d m ≃
      PositiveHemisphereBoundaryFacet d m ⊕
        PositiveHemisphereBoundaryFacet d m :=
  { toFun := boundaryFacetHemisphereSplit
    invFun := boundaryFacetHemisphereJoin
    left_inv := boundaryFacetHemisphereJoin_split
    right_inv := boundaryFacetHemisphereSplit_join hm }

/-- Helper for Theorem 57.6: a positive facet selects the first hemisphere
branch without changing its boundary-facet data. -/
theorem boundaryFacetHemisphereEquiv_apply_of_positive {d m : ℕ}
    (hm : 0 < m) (facet : BoundarySharedFacet d m)
    (hpositive : ∀ j, centeredGridPositiveHemisphere (facet.vertex j)) :
    boundaryFacetHemisphereEquiv hm facet = Sum.inl ⟨facet, hpositive⟩ := by
  -- Evaluate the branch selected by the supplied positivity certificate.
  change boundaryFacetHemisphereSplit facet = _
  unfold boundaryFacetHemisphereSplit
  rw [dif_pos hpositive]

/-- Helper for Theorem 57.6: a nonpositive facet selects the reflected second
hemisphere branch. -/
theorem boundaryFacetHemisphereEquiv_apply_of_not_positive {d m : ℕ}
    (hm : 0 < m) (facet : BoundarySharedFacet d m)
    (hpositive : ¬∀ j, centeredGridPositiveHemisphere (facet.vertex j)) :
    boundaryFacetHemisphereEquiv hm facet =
      Sum.inr ⟨facet.reflect,
        facet.positive_or_reflect_positive.resolve_left hpositive⟩ := by
  -- Evaluate the complementary branch of the canonical decomposition.
  change boundaryFacetHemisphereSplit facet = _
  unfold boundaryFacetHemisphereSplit
  rw [dif_neg hpositive]

/-- Helper for Theorem 57.6: an ambient boundary-ridge occurrence consists of
an extreme shared facet and one omitted vertex of its staircase enumeration. -/
structure BoundaryFaceOccurrence (d m : ℕ) where
  facet : BoundarySharedFacet d m
  omitted : Fin (d + 1)
deriving DecidableEq

/-- Helper for Theorem 57.6: rebuilding an ambient occurrence from its two
projections returns the original occurrence. -/
theorem BoundaryFaceOccurrence.mk_eq_self {d m : ℕ}
    (occurrence : BoundaryFaceOccurrence d m) :
    BoundaryFaceOccurrence.mk occurrence.facet occurrence.omitted = occurrence := by
  -- Eliminate the two-field record so both projections compute directly.
  cases occurrence
  rfl

/-- Helper for Theorem 57.6: projecting a newly built ambient occurrence
recovers the original facet-position pair. -/
theorem BoundaryFaceOccurrence.projections_mk_eq {d m : ℕ}
    (data : BoundarySharedFacet d m × Fin (d + 1)) :
    ((BoundaryFaceOccurrence.mk data.1 data.2).facet,
      (BoundaryFaceOccurrence.mk data.1 data.2).omitted) = data := by
  -- Eliminate the product so the constructor projections compute directly.
  cases data
  rfl

/-- Helper for Theorem 57.6: ambient boundary-ridge occurrences are the
product of a boundary facet and an omitted position. -/
def boundaryFaceOccurrenceEquiv (d m : ℕ) :
    BoundaryFaceOccurrence d m ≃ BoundarySharedFacet d m × Fin (d + 1) :=
  { toFun := fun occurrence ↦ (occurrence.facet, occurrence.omitted)
    invFun := fun data ↦ ⟨data.1, data.2⟩
    left_inv := BoundaryFaceOccurrence.mk_eq_self
    right_inv := BoundaryFaceOccurrence.projections_mk_eq }

/-- Helper for Theorem 57.6: ambient boundary-ridge occurrences form a finite
type. -/
noncomputable instance boundaryFaceOccurrenceFintype (d m : ℕ) :
    Fintype (BoundaryFaceOccurrence d m) :=
  Fintype.ofEquiv (BoundarySharedFacet d m × Fin (d + 1))
    (boundaryFaceOccurrenceEquiv d m).symm

/-- Helper for Theorem 57.6: enumerate the retained vertices of an ambient
boundary-ridge occurrence. -/
def BoundaryFaceOccurrence.vertex {d m : ℕ}
    (occurrence : BoundaryFaceOccurrence d m) (j : Fin d) :
    CenteredGrid (d + 1) m :=
  occurrence.facet.vertex (occurrence.omitted.succAbove j)

/-- Helper for Theorem 57.6: an ambient occurrence vertex is the stored
boundary-facet vertex at the surviving index. -/
theorem BoundaryFaceOccurrence.vertex_eq_facetVertex {d m : ℕ}
    (occurrence : BoundaryFaceOccurrence d m) (j : Fin d) :
    occurrence.vertex j =
      occurrence.facet.vertex (occurrence.omitted.succAbove j) := by
  -- Expose the owner computation rule without requiring clients to unfold it.
  rfl

/-- Helper for Theorem 57.6: the unordered vertex set retained by an ambient
boundary-ridge occurrence. -/
def BoundaryFaceOccurrence.ridgeVertexSet {d m : ℕ}
    (occurrence : BoundaryFaceOccurrence d m) :
    Finset (CenteredGrid (d + 1) m) :=
  Finset.univ.image occurrence.vertex

/-- Helper for Theorem 57.6: the unordered ambient ridge is the finite image
of its retained-vertex enumeration. -/
theorem BoundaryFaceOccurrence.ridgeVertexSet_eq_vertexImage {d m : ℕ}
    (occurrence : BoundaryFaceOccurrence d m) :
    occurrence.ridgeVertexSet = Finset.univ.image occurrence.vertex := by
  -- Expose the owner computation rule for finite-image arguments.
  rfl

/-- Helper for Theorem 57.6: an ambient boundary-ridge enumeration has no
repeated vertices. -/
theorem BoundaryFaceOccurrence.vertex_injective {d m : ℕ}
    (occurrence : BoundaryFaceOccurrence d m) :
    Function.Injective occurrence.vertex := by
  -- Compose the injective boundary-facet enumeration with deletion of one index.
  exact occurrence.facet.vertex_injective.comp Fin.succAbove_right_injective

/-- Helper for Theorem 57.6: every ambient boundary ridge has exactly `d`
distinct vertices. -/
theorem BoundaryFaceOccurrence.ridgeVertexSet_card {d m : ℕ}
    (occurrence : BoundaryFaceOccurrence d m) :
    occurrence.ridgeVertexSet.card = d := by
  -- Count the image of the injective retained-vertex enumeration.
  rw [BoundaryFaceOccurrence.ridgeVertexSet,
    Finset.card_image_of_injective Finset.univ occurrence.vertex_injective]
  exact Fintype.card_fin d

/-- Helper for Theorem 57.6: every retained ambient ridge vertex belongs to
the complete vertex set of its boundary cofacet. -/
theorem BoundaryFaceOccurrence.ridgeVertexSet_subset_facetVertexSet
    {d m : ℕ} (occurrence : BoundaryFaceOccurrence d m) :
    occurrence.ridgeVertexSet ⊆ Finset.univ.image occurrence.facet.vertex := by
  -- A retained vertex is the facet vertex at its surviving `succAbove` index.
  intro vertex hvertex
  unfold BoundaryFaceOccurrence.ridgeVertexSet at hvertex
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hvertex
  exact Finset.mem_image.mpr
    ⟨occurrence.omitted.succAbove j, Finset.mem_univ _, rfl⟩

/-- Helper for Theorem 57.6: forgetting a positive-hemisphere certificate
produces the corresponding ambient boundary-ridge occurrence. -/
def PositiveHemisphereFaceOccurrence.toBoundary {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    BoundaryFaceOccurrence d m :=
  ⟨occurrence.facet.1, occurrence.omitted⟩

/-- Helper for Theorem 57.6: forgetting positivity preserves the underlying
ambient boundary facet. -/
theorem PositiveHemisphereFaceOccurrence.toBoundary_facet {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.toBoundary.facet = occurrence.facet.1 := by
  -- Evaluate the facet projection at the owner of `toBoundary`.
  rfl

/-- Helper for Theorem 57.6: forgetting positivity preserves the omitted
ridge position. -/
theorem PositiveHemisphereFaceOccurrence.toBoundary_omitted {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.toBoundary.omitted = occurrence.omitted := by
  -- Evaluate the omission projection at the owner of `toBoundary`.
  rfl

/-- Helper for Theorem 57.6: forgetting the hemisphere certificate does not
change any retained ridge vertex. -/
theorem PositiveHemisphereFaceOccurrence.toBoundary_vertex {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) (j : Fin d) :
    occurrence.toBoundary.vertex j = occurrence.vertex j := by
  -- Both occurrence types use the same facet and omitted-index projections.
  exact (occurrence.vertex_eq_facetVertex j).symm

/-- Helper for Theorem 57.6: forgetting the hemisphere certificate preserves
the unordered retained ridge. -/
theorem PositiveHemisphereFaceOccurrence.toBoundary_ridgeVertexSet {d m : ℕ}
    (occurrence : PositiveHemisphereFaceOccurrence d m) :
    occurrence.toBoundary.ridgeVertexSet = occurrence.ridgeVertexSet := by
  -- Upgrade the pointwise vertex computation to equality of finite images.
  unfold BoundaryFaceOccurrence.ridgeVertexSet
  rw [occurrence.ridgeVertexSet_eq_facetImage]
  apply Finset.image_congr
  intro j _
  exact (occurrence.toBoundary_vertex j).trans
    (occurrence.vertex_eq_facetVertex j)

/-- Helper for Theorem 57.6: swap the adjacent active directions around an
internal omitted vertex of a shared facet. -/
def SharedFacet.internalRidgeMate {d m : ℕ} (facet : SharedFacet d m)
    (omitted : Fin (d + 1)) (hzero : omitted ≠ 0)
    (hlast : omitted ≠ Fin.last d) : SharedFacet d m :=
  { facet with
    activeOrder := facet.activeOrder *
      Equiv.swap (omitted.pred hzero) (omitted.castPred hlast) }

/-- Helper for Theorem 57.6: swapping the same two internal active directions
twice restores the shared facet. -/
theorem SharedFacet.internalRidgeMate_involutive {d m : ℕ}
    (facet : SharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    (facet.internalRidgeMate omitted hzero hlast).internalRidgeMate
        omitted hzero hlast = facet := by
  -- All fields but the active order are unchanged, and the swap squares to one.
  cases facet
  simp [SharedFacet.internalRidgeMate, mul_assoc]

/-- Helper for Theorem 57.6: the adjacent-order internal mate is distinct
from the original shared facet. -/
theorem SharedFacet.internalRidgeMate_ne {d m : ℕ}
    (facet : SharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    facet.internalRidgeMate omitted hzero hlast ≠ facet := by
  -- Equality would force the two distinct active ranks adjacent to the omission
  -- to have the same image under the original active order.
  intro hfixed
  have horder := congrArg SharedFacet.activeOrder hfixed
  have happly := congrArg
    (fun order : Equiv.Perm (Fin d) ↦ order (omitted.pred hzero)) horder
  have hadjacent : omitted.castPred hlast = omitted.pred hzero := by
    apply facet.activeOrder.injective
    simpa [SharedFacet.internalRidgeMate, Equiv.Perm.mul_apply] using happly
  have hvalue := congrArg Fin.val hadjacent
  have hpositive : 0 < omitted.1 := Fin.pos_iff_ne_zero.mpr hzero
  simp only [Fin.coe_castPred, Fin.val_pred] at hvalue
  omega

/-- Helper for Theorem 57.6: the adjacent-order mate preserves every rank
cut retained after deleting an internal vertex. -/
theorem SharedFacet.internalRidgeMate_rank_lt_succAbove_iff {d m : ℕ}
    (facet : SharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d)
    {i : Fin (d + 1)} (hi : i ≠ facet.fixed) (j : Fin d) :
    (((facet.internalRidgeMate omitted hzero hlast).leadingOrder.symm i).1 <
        (omitted.succAbove j).1 + 1) ↔
      (facet.leadingOrder.symm i).1 < (omitted.succAbove j).1 + 1 := by
  -- Write the old nonfixed rank as a successor in the active-coordinate order.
  obtain ⟨r, hr⟩ := Fin.exists_succ_eq_of_ne_zero
    (facet.leadingOrder_symm_ne_zero hi)
  have hmate :
      (facet.internalRidgeMate omitted hzero hlast).leadingOrder.symm i =
        (Equiv.swap (omitted.pred hzero) (omitted.castPred hlast) r).succ := by
    -- Applying the mate order cancels the adjacent swap and returns `i`.
    apply (facet.internalRidgeMate omitted hzero hlast).leadingOrder.injective
    rw [(facet.internalRidgeMate omitted hzero hlast).leadingOrder.apply_symm_apply]
    rw [(facet.internalRidgeMate omitted hzero hlast).leadingOrder_succ]
    simp only [SharedFacet.internalRidgeMate, Equiv.Perm.mul_apply,
      Equiv.swap_apply_self]
    rw [← facet.leadingOrder_succ, hr, facet.leadingOrder.apply_symm_apply]
  -- Cancel the common successor offset, then use retained-cut invariance.
  simpa only [hmate, ← hr, Fin.val_succ, Nat.add_lt_add_iff_right] using
    internalFaceMate_rank_lt_succAbove_iff omitted hzero hlast r j

/-- Helper for Theorem 57.6: swapping the active directions adjacent to an
internal omission preserves every retained shared-facet vertex. -/
theorem SharedFacet.internalRidgeMate_vertex {d m : ℕ}
    (facet : SharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) (j : Fin d) :
    (facet.internalRidgeMate omitted hzero hlast).vertex
        (omitted.succAbove j) =
      facet.vertex (omitted.succAbove j) := by
  -- Compare coordinates; the fixed coordinate is unchanged, and every active
  -- coordinate uses the rank-cut equivalence above.
  funext i
  apply Fin.ext
  rw [(facet.internalRidgeMate omitted hzero hlast).vertex_value,
    facet.vertex_value]
  have hfixed :
      (facet.internalRidgeMate omitted hzero hlast).fixed = facet.fixed := rfl
  have hlevel :
      (facet.internalRidgeMate omitted hzero hlast).level = facet.level := rfl
  have hcorner :
      (facet.internalRidgeMate omitted hzero hlast).corner = facet.corner := rfl
  rw [hfixed, hlevel, hcorner]
  by_cases hi : i = facet.fixed
  · simp only [hi, if_pos]
  · simp only [hi, if_false]
    have hcut :=
      facet.internalRidgeMate_rank_lt_succAbove_iff omitted hzero hlast hi j
    by_cases hretained :
        (facet.leadingOrder.symm i).1 < (omitted.succAbove j).1 + 1
    · have hmateRetained := hcut.mpr hretained
      simp only [hmateRetained, hretained, if_pos]
    · have hmateRetained :
          ¬(((facet.internalRidgeMate omitted hzero hlast).leadingOrder.symm i).1 <
            (omitted.succAbove j).1 + 1) := fun h ↦ hretained (hcut.mp h)
      simp only [hmateRetained, hretained, if_false]

/-- Helper for Theorem 57.6: the internal adjacent-order swap preserves the
normalization certificate of a shared facet. -/
def SharedFacet.internalNormalizedRidgeMate {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    NormalizedSharedFacet d m :=
  ⟨facet.1.internalRidgeMate omitted hzero hlast, facet.2⟩

/-- Helper for Theorem 57.6: the normalized internal adjacent-order mate is
an involution. -/
theorem SharedFacet.internalNormalizedRidgeMate_involutive {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    SharedFacet.internalNormalizedRidgeMate
        (SharedFacet.internalNormalizedRidgeMate facet omitted hzero hlast)
        omitted hzero hlast = facet := by
  -- Subtype equality reduces to the already proved shared-facet involution.
  apply Subtype.ext
  exact facet.1.internalRidgeMate_involutive omitted hzero hlast

/-- Helper for Theorem 57.6: the normalized internal adjacent-order mate has
no fixed point. -/
theorem SharedFacet.internalNormalizedRidgeMate_ne {d m : ℕ}
    (facet : NormalizedSharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    SharedFacet.internalNormalizedRidgeMate facet omitted hzero hlast ≠ facet := by
  -- Equality of normalized facets would identify their underlying raw facets.
  intro hfixed
  exact facet.1.internalRidgeMate_ne omitted hzero hlast
    (congrArg Subtype.val hfixed)

/-- Helper for Theorem 57.6: apply the internal adjacent-order mate without
changing the extreme boundary tag. -/
def BoundarySharedFacet.internalRidgeMate {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    BoundarySharedFacet d m :=
  match facet with
  | Sum.inl top => Sum.inl
      ⟨SharedFacet.internalNormalizedRidgeMate top.1 omitted hzero hlast, top.2⟩
  | Sum.inr bottom => Sum.inr
      ⟨SharedFacet.internalNormalizedRidgeMate bottom.1 omitted hzero hlast,
        bottom.2⟩

/-- Helper for Theorem 57.6: the internally paired boundary facet returns
after applying the same adjacent-order swap twice. -/
theorem BoundarySharedFacet.internalRidgeMate_involutive {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    (facet.internalRidgeMate omitted hzero hlast).internalRidgeMate
        omitted hzero hlast = facet := by
  -- Each boundary-tag branch reduces to normalized-facet involutivity.
  cases facet with
  | inl top =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact SharedFacet.internalNormalizedRidgeMate_involutive
        top.1 omitted hzero hlast
  | inr bottom =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact SharedFacet.internalNormalizedRidgeMate_involutive
        bottom.1 omitted hzero hlast

/-- Helper for Theorem 57.6: the internally paired boundary facet is distinct
from its original adjacent-order presentation. -/
theorem BoundarySharedFacet.internalRidgeMate_ne {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) :
    facet.internalRidgeMate omitted hzero hlast ≠ facet := by
  -- Injectivity of each sum tag exposes the normalized fixed-point contradiction.
  cases facet with
  | inl top =>
      intro hfixed
      have htop := Sum.inl.inj hfixed
      exact SharedFacet.internalNormalizedRidgeMate_ne top.1 omitted hzero hlast
        (congrArg Subtype.val htop)
  | inr bottom =>
      intro hfixed
      have hbottom := Sum.inr.inj hfixed
      exact SharedFacet.internalNormalizedRidgeMate_ne bottom.1 omitted hzero hlast
        (congrArg Subtype.val hbottom)

/-- Helper for Theorem 57.6: the tagged boundary-facet mate preserves every
vertex retained after an internal omission. -/
theorem BoundarySharedFacet.internalRidgeMate_vertex {d m : ℕ}
    (facet : BoundarySharedFacet d m) (omitted : Fin (d + 1))
    (hzero : omitted ≠ 0) (hlast : omitted ≠ Fin.last d) (j : Fin d) :
    (facet.internalRidgeMate omitted hzero hlast).vertex
        (omitted.succAbove j) =
      facet.vertex (omitted.succAbove j) := by
  -- Remove the boundary tag and invoke the raw shared-facet vertex theorem.
  cases facet with
  | inl top =>
      simpa only [BoundarySharedFacet.internalRidgeMate,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inl,
        SharedFacet.internalNormalizedRidgeMate] using
        top.1.1.internalRidgeMate_vertex omitted hzero hlast j
  | inr bottom =>
      simpa only [BoundarySharedFacet.internalRidgeMate,
        BoundarySharedFacet.vertex_eq_normalizedFacet,
        BoundarySharedFacet.normalizedFacet_inr,
        SharedFacet.internalNormalizedRidgeMate] using
        bottom.1.1.internalRidgeMate_vertex omitted hzero hlast j

/-- Helper for Theorem 57.6: ambient boundary-ridge occurrences with an
internal omitted position. -/
abbrev InternalBoundaryFaceOccurrence (d m : ℕ) :=
  {occurrence : BoundaryFaceOccurrence d m //
    occurrence.omitted ≠ 0 ∧ occurrence.omitted ≠ Fin.last d}

/-- Helper for Theorem 57.6: pair an internal ambient occurrence by swapping
the two active directions adjacent to its omitted position. -/
def internalBoundaryFaceOccurrenceMate {d m : ℕ}
    (occurrence : InternalBoundaryFaceOccurrence d m) :
    InternalBoundaryFaceOccurrence d m :=
  ⟨⟨occurrence.1.facet.internalRidgeMate occurrence.1.omitted
      occurrence.2.1 occurrence.2.2, occurrence.1.omitted⟩, occurrence.2⟩

/-- Helper for Theorem 57.6: the internal ambient occurrence mate is an
involution. -/
theorem internalBoundaryFaceOccurrenceMate_involutive {d m : ℕ} :
    Function.Involutive
      (internalBoundaryFaceOccurrenceMate :
        InternalBoundaryFaceOccurrence d m →
          InternalBoundaryFaceOccurrence d m) := by
  intro occurrence
  -- The omitted position is unchanged, while the boundary facet mate squares to one.
  apply Subtype.ext
  exact congrArg₂ BoundaryFaceOccurrence.mk
    (occurrence.1.facet.internalRidgeMate_involutive
      occurrence.1.omitted occurrence.2.1 occurrence.2.2) rfl

/-- Helper for Theorem 57.6: the internal ambient occurrence mate has no
fixed points. -/
theorem internalBoundaryFaceOccurrenceMate_ne {d m : ℕ}
    (occurrence : InternalBoundaryFaceOccurrence d m) :
    internalBoundaryFaceOccurrenceMate occurrence ≠ occurrence := by
  -- A fixed occurrence would force its internally paired boundary facets equal.
  intro hfixed
  have hvalue := congrArg Subtype.val hfixed
  exact occurrence.1.facet.internalRidgeMate_ne occurrence.1.omitted
    occurrence.2.1 occurrence.2.2
    (congrArg BoundaryFaceOccurrence.facet hvalue)

/-- Helper for Theorem 57.6: the internal occurrence mate presents the same
unordered boundary ridge. -/
theorem internalBoundaryFaceOccurrenceMate_ridgeVertexSet {d m : ℕ}
    (occurrence : InternalBoundaryFaceOccurrence d m) :
    (internalBoundaryFaceOccurrenceMate occurrence).1.ridgeVertexSet =
      occurrence.1.ridgeVertexSet := by
  -- Lift pointwise preservation of retained vertices to their finite images.
  unfold BoundaryFaceOccurrence.ridgeVertexSet
  apply Finset.image_congr
  intro j _
  simpa only [internalBoundaryFaceOccurrenceMate,
    BoundaryFaceOccurrence.vertex] using
    occurrence.1.facet.internalRidgeMate_vertex occurrence.1.omitted
      occurrence.2.1 occurrence.2.2 j

end StandardSphere.CubicalTucker
