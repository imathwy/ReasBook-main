module

public import Topology_Munkres_2000.Book.Theorem_57_5.JordanMeasurable
public import Topology_Munkres_2000.Book.Exercise_57_4

import Topology_Munkres_2000.Book.Remark_50_3.CubicalIncidence
import Topology_Munkres_2000.Book.Theorem_57_6.CubicalTucker
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Data.Prod.Lex
import Mathlib.Topology.ContinuousMap.Compact

public section

open MeasureTheory

/-- Helper for Theorem 57.6: intersecting a set with a fixed set preserves its
measure when the first set is replaced by its interior and has null frontier. -/
private lemma measure_interior_inter_of_null_frontier
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} {s t : Set α} (h : μ (frontier s) = 0) :
    μ (interior s ∩ t) = μ (s ∩ t) := by
  -- Intersect the canonical a.e. equality with `t`, then pass to measures.
  exact measure_congr
    (ae_eq_set_inter (interior_ae_eq_of_null_frontier h) (ae_eq_refl t))

namespace StandardSphere

universe u

namespace CubicalTucker

/-- Helper for Theorem 57.6: the endpoint equivalence recognizes a normal
form when the underlying occurrence equals that of its canonical inverse. -/
private theorem endpointStaircaseFaceEquiv_eq_of_val_eq_symm_val {d m : ℕ}
    (endpoint : EndpointStaircaseFaceOccurrence d m)
    (normal : PositiveNormalizedSharedFacet d m ⊕
      BelowTopNormalizedSharedFacet d m)
    (hval : endpoint.1 = ((endpointStaircaseFaceEquiv d m).symm normal).1) :
    endpointStaircaseFaceEquiv d m endpoint = normal := by
  -- Proof irrelevance upgrades equality of occurrences to equality of the
  -- endpoint subtypes, after which the equivalence cancels its inverse.
  have hendpoint : endpoint = (endpointStaircaseFaceEquiv d m).symm normal :=
    Subtype.ext hval
  rw [hendpoint]
  exact Equiv.apply_symm_apply (endpointStaircaseFaceEquiv d m) normal

/-- Helper for Theorem 57.6: normalizing an exchanged endpoint occurrence
maps the old outer boundary tag once its two canonical inverse projections
are available. -/
private theorem
    EndpointBoundaryFaceOccurrence.exchangedEndpointNormalForm_of_inverse_branches
    {d m : ℕ} (occurrence : EndpointBoundaryFaceOccurrence (d + 1) m)
    (inner : NormalizedSharedFacet d m)
    (hlower : ∀ top : TopBoundaryNormalizedSharedFacet (d + 1) m,
      occurrence.1.facet = Sum.inl top →
        (occurrence.exchangedActiveEndpointOccurrence inner).1 =
          ((endpointStaircaseFaceEquiv d m).symm
            (Sum.inl
              ⟨SharedFacet.exchangedActiveFacet top.1 inner,
                SharedFacet.exchangedActiveFacet_level_pos_of_top top inner⟩)).1)
    (hupper : ∀ bottom : BottomBoundaryNormalizedSharedFacet (d + 1) m,
      occurrence.1.facet = Sum.inr bottom →
        (occurrence.exchangedActiveEndpointOccurrence inner).1 =
          ((endpointStaircaseFaceEquiv d m).symm
            (Sum.inr
              ⟨SharedFacet.exchangedActiveFacet bottom.1 inner,
                SharedFacet.exchangedActiveFacet_level_lt_of_bottom bottom inner⟩)).1) :
    endpointStaircaseFaceEquiv d m
        (occurrence.exchangedActiveEndpointOccurrence inner) =
      Sum.map
        (fun top ↦
          ⟨SharedFacet.exchangedActiveFacet top.1 inner,
            SharedFacet.exchangedActiveFacet_level_pos_of_top top inner⟩)
        (fun bottom ↦
          ⟨SharedFacet.exchangedActiveFacet bottom.1 inner,
            SharedFacet.exchangedActiveFacet_level_lt_of_bottom bottom inner⟩)
        occurrence.1.facet := by
  -- Route correction: imported constructors stay opaque here. Split only on
  -- the outer tag and recognize each branch through its canonical inverse.
  cases hfacet : occurrence.1.facet with
  | inl top =>
      have hnormal := endpointStaircaseFaceEquiv_eq_of_val_eq_symm_val
        (occurrence.exchangedActiveEndpointOccurrence inner)
        (Sum.inl
          ⟨SharedFacet.exchangedActiveFacet top.1 inner,
            SharedFacet.exchangedActiveFacet_level_pos_of_top top inner⟩)
        (hlower top hfacet)
      simpa only [Sum.map_inl] using hnormal
  | inr bottom =>
      have hnormal := endpointStaircaseFaceEquiv_eq_of_val_eq_symm_val
        (occurrence.exchangedActiveEndpointOccurrence inner)
        (Sum.inr
          ⟨SharedFacet.exchangedActiveFacet bottom.1 inner,
            SharedFacet.exchangedActiveFacet_level_lt_of_bottom bottom inner⟩)
        (hupper bottom hfacet)
      simpa only [Sum.map_inr] using hnormal

/-- Helper for Theorem 57.6: excluding every complementary grid edge forces
equal signs on neighboring vertices with equal unsigned labels. -/
private theorem sameSign_of_no_complementary_centeredGridNeighbors {d m : ℕ}
    (label : CenteredGrid d m → Fin d × Bool)
    (hno : ¬∃ a b, centeredGridNeighbor a b ∧
      label b = ((label a).1, !(label a).2))
    {a b : CenteredGrid d m} (hab : centeredGridNeighbor a b)
    (hlabel : (label b).1 = (label a).1) :
    (label b).2 = (label a).2 := by
  -- Convert the global negated existential into the pointwise hypothesis of
  -- the established same-sign lemma.
  apply sameSignOfNoComplementaryNeighbor label
  · intro x y hxy hcomplementary
    exact hno ⟨x, y, hxy, hcomplementary⟩
  · exact hab
  · exact hlabel

end CubicalTucker

/-- Helper for Theorem 57.6: the radial point represented by a sphere-cone
coordinate. -/
private def sphereConePoint (n : ℕ) (p : unitInterval × StandardSphere n) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin (n + 1)))

/-- Helper for Theorem 57.6: every radial sphere-cone point belongs to the
closed unit ball. -/
private theorem sphereConePoint_mem (n : ℕ) (p : unitInterval × StandardSphere n) :
    sphereConePoint n p ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- Bound the radial coefficient by one and use the unit norm of the sphere point.
  rw [Metric.mem_closedBall, dist_zero_right, sphereConePoint, norm_smul]
  have hnorm : ‖(p.2 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property
  rw [hnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg]
  · linarith [unitInterval.nonneg p.1]
  · linarith [unitInterval.le_one p.1]

/-- Helper for Theorem 57.6: the radial sphere-cone point varies continuously. -/
private theorem continuous_sphereConePoint (n : ℕ) : Continuous (sphereConePoint n) := by
  -- Continuity follows from the scalar-multiplication formula.
  unfold sphereConePoint
  fun_prop

/-- Helper for Theorem 57.6: the sphere cone projects radially onto the closed
unit ball. -/
private def sphereConeProjection (n : ℕ) :
    C(unitInterval × StandardSphere n, ClosedUnitBall n) :=
  ⟨fun p ↦ ⟨sphereConePoint n p, sphereConePoint_mem n p⟩,
    (continuous_sphereConePoint n).subtype_mk _⟩

/-- Helper for Theorem 57.6: the radial cone projection restricts at time zero
to the canonical sphere inclusion. -/
private theorem sphereConeProjection_zero (n : ℕ) (x : StandardSphere n) :
    sphereConeProjection n (0, x) = toBall n x := by
  -- At time zero the radial scalar is one.
  apply Subtype.ext
  change (1 - (0 : ℝ)) • (x : EuclideanSpace ℝ (Fin (n + 1))) = x
  simp

/-- Helper for Theorem 57.6: the radial cone projection is surjective. -/
private theorem sphereConeProjection_surjective (n : ℕ) :
    Function.Surjective (sphereConeProjection n) := by
  -- Normalize a nonzero ball point; represent the origin by the cone apex.
  rintro ⟨x, hx⟩
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  by_cases hxzero : x = 0
  · let v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
    have hvnorm : ‖v‖ = 1 := by
      simp [v]
    have hvsphere :
        v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hvnorm
    let q : StandardSphere n := ⟨v, hvsphere⟩
    refine ⟨(1, q), ?_⟩
    apply Subtype.ext
    simp [sphereConeProjection, sphereConePoint, hxzero]
  · have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
    have ht_le_one : 1 - ‖x‖ ≤ 1 := by
      linarith
    let t : unitInterval := ⟨1 - ‖x‖, sub_nonneg.mpr hxnorm, ht_le_one⟩
    have hnormalize : ‖NormedSpace.normalize x‖ = 1 :=
      NormedSpace.norm_normalize hxzero
    have hnormalize_sphere :
        NormedSpace.normalize x ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hnormalize
    let q : StandardSphere n := ⟨NormedSpace.normalize x, hnormalize_sphere⟩
    refine ⟨(t, q), ?_⟩
    apply Subtype.ext
    simp only [sphereConeProjection, sphereConePoint, ContinuousMap.coe_mk, t, q]
    rw [sub_sub_cancel, NormedSpace.norm_smul_normalize]

/-- Helper for Theorem 57.6: equal radial cone images either have the same
representative or both representatives are at the apex. -/
private theorem sphereConeProjection_fiber (n : ℕ)
    (p q : unitInterval × StandardSphere n)
    (hpq : sphereConeProjection n p = sphereConeProjection n q) :
    p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  -- Norms determine the radial coordinate away from the common apex.
  have hvector : sphereConePoint n p = sphereConePoint n q :=
    congrArg (fun z : ClosedUnitBall n ↦
      (z : EuclideanSpace ℝ (Fin (n + 1)))) hpq
  have hp_norm : ‖(p.2 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property
  have hq_norm : ‖(q.2 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using q.2.property
  have htime_val : (p.1 : ℝ) = q.1 := by
    have hnorm := congrArg norm hvector
    simp only [sphereConePoint, norm_smul, hp_norm, hq_norm, mul_one,
      Real.norm_eq_abs] at hnorm
    rw [abs_of_nonneg, abs_of_nonneg] at hnorm
    · linarith
    · linarith [unitInterval.le_one q.1]
    · linarith [unitInterval.le_one p.1]
  have htime : p.1 = q.1 := Subtype.ext htime_val
  by_cases hapex : p.1 = 1
  · exact Or.inr ⟨hapex, htime.symm.trans hapex⟩
  · left
    apply Prod.ext htime
    apply Subtype.ext
    have hscalar : (1 - (p.1 : ℝ)) ≠ 0 := by
      intro hzero
      apply hapex
      apply Subtype.ext
      exact (sub_eq_zero.mp hzero).symm
    apply smul_right_injective (EuclideanSpace ℝ (Fin (n + 1))) hscalar
    simpa only [sphereConePoint, htime] using hvector

/-- Helper for Theorem 57.6: the radial sphere-cone projection is a quotient
map. -/
private theorem sphereConeProjection_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (sphereConeProjection n) := by
  -- A continuous surjection from the compact cone is a quotient map.
  exact Topology.IsQuotientMap.of_surjective_continuous
    (sphereConeProjection_surjective n) (sphereConeProjection n).continuous

/-- Helper for Theorem 57.6: a nullhomotopy is constant on the fibers of the
radial cone projection. -/
private theorem nullhomotopy_factors_sphereConeProjection
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    {f : C(StandardSphere n, X)} {x : X}
    (H : f.Homotopy (ContinuousMap.const _ x)) :
    Function.FactorsThrough H.toContinuousMap (sphereConeProjection n) := by
  -- Non-apex representatives agree, while the homotopy is constant at the apex.
  intro p q hpq
  rcases sphereConeProjection_fiber n p q hpq with rfl | ⟨hp, hq⟩
  · rfl
  · have hp_pair : p = (1, p.2) := Prod.ext hp rfl
    have hq_pair : q = (1, q.2) := Prod.ext hq rfl
    rw [hp_pair, hq_pair]
    change H (1, p.2) = H (1, q.2)
    rw [H.apply_one, H.apply_one]
    rfl

/-- Helper for Theorem 57.6: descend a nullhomotopy through the radial sphere
cone to the closed ball. -/
private noncomputable def sphereConeExtension
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    {f : C(StandardSphere n, X)} {x : X}
    (H : f.Homotopy (ContinuousMap.const _ x)) : C(ClosedUnitBall n, X) :=
  (sphereConeProjection_isQuotientMap n).lift H.toContinuousMap
    (nullhomotopy_factors_sphereConeProjection H)

/-- Helper for Theorem 57.6: the descended cone map restricts to the original
sphere map. -/
private theorem sphereConeExtension_comp_toBall
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    {f : C(StandardSphere n, X)} {x : X}
    (H : f.Homotopy (ContinuousMap.const _ x)) :
    (sphereConeExtension H).comp (toBall n) = f := by
  -- Evaluate the quotient lift on the time-zero cone representative.
  apply ContinuousMap.ext
  intro q
  rw [ContinuousMap.comp_apply, ← sphereConeProjection_zero n q]
  have hlift := congrArg
    (fun g : C(unitInterval × StandardSphere n, X) ↦ g (0, q))
    ((sphereConeProjection_isQuotientMap n).lift_comp H.toContinuousMap
      (nullhomotopy_factors_sphereConeProjection H))
  exact hlift.trans (H.apply_zero q)

/-- Helper for Theorem 57.6: a nullhomotopic map on a standard sphere extends
continuously over the closed unit ball. -/
private theorem ContinuousMap.exists_closedBallExtension_of_nullhomotopic
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    {f : C(StandardSphere n, X)} (hf : f.Nullhomotopic) :
    ∃ F : C(ClosedUnitBall n, X), ∀ x, F (toBall n x) = f x := by
  -- Choose the constant endpoint and expose only the boundary specification.
  obtain ⟨x, ⟨H⟩⟩ := hf
  refine ⟨sphereConeExtension H, ?_⟩
  intro q
  exact ContinuousMap.congr_fun (sphereConeExtension_comp_toBall H) q

/-- Helper for Theorem 57.6: the finite set of lexicographically ranked
absolute coordinates of a sphere point is nonempty. -/
private theorem coordinateRanks_nonempty {n : ℕ} (x : StandardSphere n) :
    (Finset.univ.image
      (fun i : Fin (n + 1) ↦ (toLex (|x.1 i|, i) : ℝ ×ₗ Fin (n + 1)))).Nonempty := by
  -- The coordinate type `Fin (n + 1)` contains its zeroth coordinate.
  exact Finset.univ_nonempty.image _

/-- Helper for Theorem 57.6: the lexicographically greatest absolute
coordinate, with the coordinate index breaking ties. -/
private noncomputable def maximalCoordinateRank {n : ℕ} (x : StandardSphere n) :
    ℝ ×ₗ Fin (n + 1) :=
  (Finset.univ.image
    (fun i : Fin (n + 1) ↦ (toLex (|x.1 i|, i) : ℝ ×ₗ Fin (n + 1)))).max'
      (coordinateRanks_nonempty x)

/-- Helper for Theorem 57.6: the selected maximal-coordinate index of a sphere
point. -/
private noncomputable def maximalCoordinateIndex {n : ℕ} (x : StandardSphere n) :
    Fin (n + 1) :=
  (ofLex (maximalCoordinateRank x)).2

/-- Helper for Theorem 57.6: the first component of the maximal coordinate rank
is the absolute value at its selected index. -/
private theorem maximalCoordinateRank_fst {n : ℕ} (x : StandardSphere n) :
    (ofLex (maximalCoordinateRank x)).1 = |x.1 (maximalCoordinateIndex x)| := by
  -- Membership of the finite maximum identifies both components with one coordinate.
  have hmem := Finset.max'_mem
    (Finset.univ.image
      (fun i : Fin (n + 1) ↦ (toLex (|x.1 i|, i) : ℝ ×ₗ Fin (n + 1))))
    (coordinateRanks_nonempty x)
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  have hpair := congrArg ofLex hi
  have hfst := congrArg Prod.fst hpair
  have hsnd := congrArg Prod.snd hpair
  unfold maximalCoordinateIndex
  exact hfst.symm.trans (congrArg (fun j ↦ |x.1 j|) hsnd)

/-- Helper for Theorem 57.6: every coordinate is bounded in absolute value by
the selected maximal coordinate. -/
private theorem abs_coordinate_le_maximal {n : ℕ} (x : StandardSphere n)
    (j : Fin (n + 1)) :
    |x.1 j| ≤ |x.1 (maximalCoordinateIndex x)| := by
  -- Compare the rank of `j` with the greatest rank and project to first components.
  have hle := Finset.le_max'
    (Finset.univ.image
      (fun i : Fin (n + 1) ↦ (toLex (|x.1 i|, i) : ℝ ×ₗ Fin (n + 1))))
    (toLex (|x.1 j|, j)) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hfst := Prod.Lex.monotone_fst _ _ hle
  -- The projected lexicographic inequality is the required absolute-value bound.
  exact hfst.trans (maximalCoordinateRank_fst x).le

/-- Helper for Theorem 57.6: the selected maximal coordinate has magnitude at
least the reciprocal of the number of coordinates. -/
private theorem reciprocal_card_le_abs_maximalCoordinate {n : ℕ}
    (x : StandardSphere n) :
    1 / (n + 1 : ℝ) ≤ |x.1 (maximalCoordinateIndex x)| := by
  -- Sum the squared coordinate bounds and use the unit-norm sphere equation.
  let c : ℝ := |x.1 (maximalCoordinateIndex x)|
  have hc_nonneg : 0 ≤ c := abs_nonneg _
  have hxnorm : ‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hcoordinate (j : Fin (n + 1)) : (x.1 j) ^ 2 ≤ c ^ 2 := by
    have habs := abs_coordinate_le_maximal x j
    change |x.1 j| ≤ c at habs
    rw [sq_le_sq, abs_of_nonneg hc_nonneg]
    exact habs
  have hsum :
      ∑ j : Fin (n + 1), (x.1 j) ^ 2 ≤ (n + 1 : ℝ) * c ^ 2 := by
    calc
      ∑ j : Fin (n + 1), (x.1 j) ^ 2 ≤
          ∑ _j : Fin (n + 1), c ^ 2 :=
        Finset.sum_le_sum (fun j _ ↦ hcoordinate j)
      _ = (n + 1 : ℝ) * c ^ 2 := by
        simp [Nat.cast_add, Nat.cast_one]
  have hone : 1 ≤ (n + 1 : ℝ) * c ^ 2 := by
    calc
      1 = ‖(x.1 : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := by rw [hxnorm]; norm_num
      _ = ∑ j : Fin (n + 1), (x.1 j) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq x.1
      _ ≤ (n + 1 : ℝ) * c ^ 2 := hsum
  have hc_le_one : c ≤ 1 := by
    have happly := PiLp.norm_apply_le
      (x.1 : EuclideanSpace ℝ (Fin (n + 1))) (maximalCoordinateIndex x)
    rw [Real.norm_eq_abs, hxnorm] at happly
    exact happly
  have hsquare_le : c ^ 2 ≤ c := by
    nlinarith
  have hlinear : 1 ≤ (n + 1 : ℝ) * c := by
    exact hone.trans (mul_le_mul_of_nonneg_left hsquare_le (by positivity))
  change 1 / (n + 1 : ℝ) ≤ c
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    (by simpa [mul_comm] using hlinear)

/-- Helper for Theorem 57.6: equal finite sets have equal greatest elements,
independently of the proofs that they are nonempty. -/
private theorem Finset.max'_congr_of_eq {α : Type*} [LinearOrder α]
    {s t : Finset α} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by
  -- Substitute the set equality; proof irrelevance identifies the witnesses.
  subst t
  rfl

/-- Helper for Theorem 57.6: negation preserves the deterministically selected
maximal-coordinate index. -/
private theorem maximalCoordinateIndex_neg {n : ℕ} (x : StandardSphere n) :
    maximalCoordinateIndex (-x) = maximalCoordinateIndex x := by
  -- Negation leaves every absolute-coordinate rank unchanged, including tie breaks.
  have hranks :
      Finset.univ.image
          (fun i : Fin (n + 1) ↦ (toLex (|(-x).1 i|, i) : ℝ ×ₗ Fin (n + 1))) =
        Finset.univ.image
          (fun i : Fin (n + 1) ↦ (toLex (|x.1 i|, i) : ℝ ×ₗ Fin (n + 1))) := by
    apply Finset.image_congr
    intro i hi
    simp
  unfold maximalCoordinateIndex maximalCoordinateRank
  exact congrArg (fun r : ℝ ×ₗ Fin (n + 1) ↦ (ofLex r).2)
    (Finset.max'_congr_of_eq hranks (coordinateRanks_nonempty (-x))
      (coordinateRanks_nonempty x))

/-- Helper for Theorem 57.6: the signed maximal-coordinate label of a sphere
point. -/
private noncomputable def maximalCoordinateLabel {n : ℕ} (x : StandardSphere n) :
    Fin (n + 1) × Bool :=
  (maximalCoordinateIndex x, decide (0 ≤ x.1 (maximalCoordinateIndex x)))

/-- Helper for Theorem 57.6: the coordinate selected by the maximal-coordinate
label is nonzero. -/
private theorem maximalCoordinate_ne_zero {n : ℕ} (x : StandardSphere n) :
    x.1 (maximalCoordinateIndex x) ≠ 0 := by
  -- Its absolute value is bounded below by a strictly positive reciprocal.
  have hpositive : 0 < 1 / (n + 1 : ℝ) := by
    positivity
  have habs : 0 < |x.1 (maximalCoordinateIndex x)| :=
    hpositive.trans_le (reciprocal_card_le_abs_maximalCoordinate x)
  exact (abs_pos.mp habs)

/-- Helper for Theorem 57.6: antipodal sphere points receive the same coordinate
index and opposite Boolean signs. -/
private theorem maximalCoordinateLabel_neg {n : ℕ} (x : StandardSphere n) :
    maximalCoordinateLabel (-x) =
      ((maximalCoordinateLabel x).1, !(maximalCoordinateLabel x).2) := by
  -- The index is invariant under negation, while its nonzero coordinate changes sign.
  apply Prod.ext
  · exact maximalCoordinateIndex_neg x
  · simp only [maximalCoordinateLabel, maximalCoordinateIndex_neg]
    by_cases hnonneg : 0 ≤ x.1 (maximalCoordinateIndex x)
    · have hpos : 0 < x.1 (maximalCoordinateIndex x) :=
        lt_of_le_of_ne hnonneg (Ne.symm (maximalCoordinate_ne_zero x))
      have hneg : ¬ 0 ≤ -x.1 (maximalCoordinateIndex x) := by
        linarith
      simp [hnonneg, hneg]
    · have hneg : x.1 (maximalCoordinateIndex x) < 0 := lt_of_not_ge hnonneg
      have hneg_nonneg : 0 ≤ -x.1 (maximalCoordinateIndex x) := by
        linarith
      simp [hnonneg, hneg_nonneg]

/-- Helper for Theorem 57.6: opposite signed maximal-coordinate labels force a
uniform metric separation on the sphere. -/
private theorem maximalCoordinateLabel_separated {n : ℕ} (x y : StandardSphere n)
    (hlabel : maximalCoordinateLabel y =
      ((maximalCoordinateLabel x).1, !(maximalCoordinateLabel x).2)) :
    2 / (n + 1 : ℝ) ≤ dist x y := by
  -- Extract the common selected index and the opposite sign information.
  have hindex : maximalCoordinateIndex y = maximalCoordinateIndex x := by
    exact congrArg Prod.fst hlabel
  have hsign :
      decide (0 ≤ y.1 (maximalCoordinateIndex x)) =
        !(decide (0 ≤ x.1 (maximalCoordinateIndex x))) := by
    have hsign' := congrArg Prod.snd hlabel
    simpa only [maximalCoordinateLabel, Prod.snd, hindex] using hsign'
  have hxlarge := reciprocal_card_le_abs_maximalCoordinate x
  have hylarge := reciprocal_card_le_abs_maximalCoordinate y
  rw [hindex] at hylarge
  -- A coordinate projection is one-Lipschitz for the Euclidean norm.
  have hcoordinateDist :
      |x.1 (maximalCoordinateIndex x) - y.1 (maximalCoordinateIndex x)| ≤ dist x y := by
    have happly := PiLp.norm_apply_le
      (x.1 - y.1 : EuclideanSpace ℝ (Fin (n + 1))) (maximalCoordinateIndex x)
    simpa only [PiLp.sub_apply, Real.norm_eq_abs, Subtype.dist_eq, dist_eq_norm]
      using happly
  by_cases hxnonneg : 0 ≤ x.1 (maximalCoordinateIndex x)
  · have hynonneg : ¬ 0 ≤ y.1 (maximalCoordinateIndex x) := by
      intro hy
      simp [hxnonneg, hy] at hsign
    have hyneg : y.1 (maximalCoordinateIndex x) < 0 := lt_of_not_ge hynonneg
    rw [abs_of_nonneg hxnonneg] at hxlarge
    rw [abs_of_neg hyneg] at hylarge
    have hdiff_nonneg :
        0 ≤ x.1 (maximalCoordinateIndex x) - y.1 (maximalCoordinateIndex x) := by
      linarith
    rw [abs_of_nonneg hdiff_nonneg] at hcoordinateDist
    calc
      2 / (n + 1 : ℝ) =
          1 / (n + 1 : ℝ) + 1 / (n + 1 : ℝ) := by ring
      _ ≤ x.1 (maximalCoordinateIndex x) - y.1 (maximalCoordinateIndex x) := by
        linarith
      _ ≤ dist x y := hcoordinateDist
  · have hxneg : x.1 (maximalCoordinateIndex x) < 0 := lt_of_not_ge hxnonneg
    have hynonneg : 0 ≤ y.1 (maximalCoordinateIndex x) := by
      by_contra hy
      simp [hxnonneg, hy] at hsign
    rw [abs_of_neg hxneg] at hxlarge
    rw [abs_of_nonneg hynonneg] at hylarge
    have hdiff_nonpos :
        x.1 (maximalCoordinateIndex x) - y.1 (maximalCoordinateIndex x) ≤ 0 := by
      linarith
    rw [abs_of_nonpos hdiff_nonpos] at hcoordinateDist
    calc
      2 / (n + 1 : ℝ) =
          1 / (n + 1 : ℝ) + 1 / (n + 1 : ℝ) := by ring
      _ ≤ -(x.1 (maximalCoordinateIndex x) - y.1 (maximalCoordinateIndex x)) := by
        linarith
      _ ≤ dist x y := hcoordinateDist

/-- Helper for Theorem 57.6: the real vector represented by a positive-radius
centered grid vertex. -/
private noncomputable def centeredGridVector {d m : ℕ} (_hm : 0 < m)
    (v : CenteredGrid d m) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ ((v i : ℕ) - (m : ℝ)) / (m : ℝ))

/-- Helper for Theorem 57.6: reflection of a grid vertex negates its realized
Euclidean vector. -/
private theorem centeredGridVector_neg {d m : ℕ} (hm : 0 < m)
    (v : CenteredGrid d m) :
    centeredGridVector hm (centeredGridNeg v) = -centeredGridVector hm v := by
  -- Compare coordinates and use the exact arithmetic formula for `Fin.rev`.
  apply WithLp.ofLp_injective
  funext i
  simp only [centeredGridVector, PiLp.toLp_apply, WithLp.ofLp_neg, Pi.neg_apply]
  have hsum : ((centeredGridNeg v i).1 : ℝ) + (v i).1 = 2 * (m : ℝ) := by
    exact_mod_cast centeredGridNeg_value v i
  have hmreal : (m : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

/-- Helper for Theorem 57.6: every coordinate of a realized grid vertex has
absolute value at most one. -/
private theorem abs_centeredGridVector_apply_le_one {d m : ℕ} (hm : 0 < m)
    (v : CenteredGrid d m) (i : Fin d) :
    |centeredGridVector hm v i| ≤ 1 := by
  -- Grid coordinates lie between `0` and `2m`, so centering and scaling lands in `[-1,1]`.
  simp only [centeredGridVector, PiLp.toLp_apply]
  have hv : (v i : ℕ) ≤ 2 * m := Nat.le_of_lt_succ (v i).isLt
  have hvreal : ((v i : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast hv
  have hmreal : (0 : ℝ) < m := by positivity
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hmreal]
    linarith
  · rw [div_le_iff₀ hmreal]
    linarith

/-- Helper for Theorem 57.6: a boundary grid vertex has a realized coordinate
of absolute value exactly one. -/
private theorem exists_abs_centeredGridVector_apply_eq_one {d m : ℕ} (hm : 0 < m)
    (v : CenteredGrid d m) (hv : centeredGridBoundary v) :
    ∃ i, |centeredGridVector hm v i| = 1 := by
  -- An extremal discrete coordinate realizes as `-1` or `1`.
  obtain ⟨i, hi | hi⟩ := hv
  · refine ⟨i, ?_⟩
    simp only [centeredGridVector, PiLp.toLp_apply, hi,
      Nat.cast_zero, zero_sub]
    have hmreal : (m : ℝ) ≠ 0 := by positivity
    rw [neg_div, div_self hmreal, abs_neg, abs_one]
  · refine ⟨i, ?_⟩
    simp only [centeredGridVector, PiLp.toLp_apply, hi]
    have hmreal : (m : ℝ) ≠ 0 := by positivity
    push_cast
    rw [show (2 : ℝ) * m - m = m by ring, div_self hmreal, abs_one]

/-- Helper for Theorem 57.6: radial clamping sends an ambient vector into the
closed unit ball. -/
private theorem radialClamp_mem_closedBall {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    (max 1 ‖x‖)⁻¹ • x ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  -- Its norm is `‖x‖ / max 1 ‖x‖`, which is at most one.
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv]
  have hmax_nonneg : 0 ≤ max 1 ‖x‖ := zero_le_one.trans (le_max_left 1 ‖x‖)
  have hmax : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [abs_of_nonneg hmax_nonneg, inv_mul_eq_div, div_le_one hmax]
  exact le_max_right 1 ‖x‖

/-- Helper for Theorem 57.6: radial clamping as a point of the closed unit ball. -/
private noncomputable def radialClampToBall {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  ⟨(max 1 ‖x‖)⁻¹ • x, radialClamp_mem_closedBall x⟩

/-- Helper for Theorem 57.6: radial clamping commutes with negation. -/
private theorem radialClampToBall_neg {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    radialClampToBall (-x) = -radialClampToBall x := by
  -- Negation preserves the norm and commutes with scalar multiplication.
  apply Subtype.ext
  change (max 1 ‖-x‖)⁻¹ • (-x) = -((max 1 ‖x‖)⁻¹ • x)
  rw [norm_neg, smul_neg]

/-- Helper for Theorem 57.6: a realized cube-boundary vertex clamps to the
unit sphere. -/
private theorem radialClamp_centeredGridVector_mem_sphere {d m : ℕ} (hm : 0 < m)
    (v : CenteredGrid d m) (hv : centeredGridBoundary v) :
    ((radialClampToBall (centeredGridVector hm v) :
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
      EuclideanSpace ℝ (Fin d)) ∈ Metric.sphere 0 1 := by
  -- A boundary coordinate has magnitude one, so the ambient norm is at least one;
  -- radial clamping consequently normalizes the vector to norm one.
  obtain ⟨i, hi⟩ := exists_abs_centeredGridVector_apply_eq_one hm v hv
  have hone_le : 1 ≤ ‖centeredGridVector hm v‖ := by
    have happly := PiLp.norm_apply_le (centeredGridVector hm v) i
    rw [Real.norm_eq_abs, hi] at happly
    exact happly
  rw [Metric.mem_sphere, dist_zero_right]
  simp only [radialClampToBall, norm_smul, Real.norm_eq_abs]
  rw [max_eq_right hone_le, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact ne_of_gt (zero_lt_one.trans_le hone_le)

/-- Helper for Theorem 57.6: radial clamping into the closed unit ball is
continuous. -/
private theorem continuous_radialClampToBall (d : ℕ) :
    Continuous (radialClampToBall :
      EuclideanSpace ℝ (Fin d) → Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  -- The denominator is bounded below by one, so inversion and scalar multiplication are continuous.
  apply Continuous.subtype_mk
  have hdenominator : Continuous (fun x : EuclideanSpace ℝ (Fin d) ↦ max 1 ‖x‖) :=
    continuous_const.max continuous_norm
  have hdenominator_ne :
      ∀ x : EuclideanSpace ℝ (Fin d), max 1 ‖x‖ ≠ 0 :=
    fun x ↦ ne_of_gt (zero_lt_one.trans_le (le_max_left 1 ‖x‖))
  exact (hdenominator.inv₀ hdenominator_ne).smul continuous_id

/-- Helper for Theorem 57.6: every realized positive-radius grid vertex lies
in the closed ball whose radius is the number of coordinates. -/
private theorem centeredGridVector_norm_le_dim {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (v : CenteredGrid d m) :
    ‖centeredGridVector hm v‖ ≤ d := by
  -- Bound the squared norm by summing the coordinatewise bounds by one.
  have hcoordinate (i : Fin d) : (centeredGridVector hm v i) ^ 2 ≤ 1 := by
    have hi := abs_centeredGridVector_apply_le_one hm v i
    have hisquare :=
      (sq_le_sq₀ (abs_nonneg (centeredGridVector hm v i)) zero_le_one).mpr hi
    simpa only [sq_abs, one_pow] using hisquare
  have hsquare : ‖centeredGridVector hm v‖ ^ 2 ≤ (d : ℝ) := by
    calc
      ‖centeredGridVector hm v‖ ^ 2 =
          ∑ i : Fin d, (centeredGridVector hm v i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq _
      _ ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ ↦ hcoordinate i)
      _ = d := by simp
  have hdone : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  nlinarith [norm_nonneg (centeredGridVector hm v)]

/-- Helper for Theorem 57.6: every realized grid vertex belongs to the fixed
dimension-radius compact ball. -/
private theorem centeredGridVector_mem_closedBall_dim {d m : ℕ} (hd : 0 < d)
    (hm : 0 < m) (v : CenteredGrid d m) :
    centeredGridVector hm v ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) d := by
  -- This is the metric-set form of the preceding norm estimate.
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    centeredGridVector_norm_le_dim hd hm v

/-- Helper for Theorem 57.6: neighboring centered-grid vectors are at distance
at most `d / m`. -/
private theorem dist_centeredGridVector_le {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {v w : CenteredGrid d m} (hvw : centeredGridNeighbor v w) :
    dist (centeredGridVector hm v) (centeredGridVector hm w) ≤ (d : ℝ) / m := by
  -- Each coordinate changes by at most `1/m`; summing squares gives the Euclidean bound.
  have hmreal : (0 : ℝ) < m := by positivity
  have hcoordinate (i : Fin d) :
      |centeredGridVector hm v i - centeredGridVector hm w i| ≤ 1 / (m : ℝ) := by
    obtain ⟨hvw_le, hwv_le⟩ := hvw i
    have hvw_real : ((v i).1 : ℝ) ≤ (w i).1 + 1 := by exact_mod_cast hvw_le
    have hwv_real : ((w i).1 : ℝ) ≤ (v i).1 + 1 := by exact_mod_cast hwv_le
    simp only [centeredGridVector, PiLp.toLp_apply]
    rw [← sub_div, abs_div, abs_of_nonneg hmreal.le]
    apply (div_le_iff₀ hmreal).mpr
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hmreal)]
    rw [abs_le]
    constructor <;> linarith
  have hcoordinate_sq (i : Fin d) :
      (centeredGridVector hm v i - centeredGridVector hm w i) ^ 2 ≤
        (1 / (m : ℝ)) ^ 2 := by
    have hnonneg : 0 ≤ 1 / (m : ℝ) := by positivity
    have hisquare := (sq_le_sq₀
      (abs_nonneg (centeredGridVector hm v i - centeredGridVector hm w i))
      hnonneg).mpr (hcoordinate i)
    simpa only [sq_abs] using hisquare
  have hsquare :
      dist (centeredGridVector hm v) (centeredGridVector hm w) ^ 2 ≤
        (d : ℝ) * (1 / (m : ℝ)) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i : Fin d,
          ((centeredGridVector hm v - centeredGridVector hm w) i) ^ 2 ≤
          ∑ _i : Fin d, (1 / (m : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [PiLp.sub_apply] using hcoordinate_sq i
      _ = (d : ℝ) * (1 / (m : ℝ)) ^ 2 := by simp
  have hdim : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have htarget_sq :
      (d : ℝ) * (1 / (m : ℝ)) ^ 2 ≤ ((d : ℝ) / m) ^ 2 := by
    field_simp
    nlinarith
  have htarget_nonneg : 0 ≤ (d : ℝ) / m := by positivity
  have hdist_nonneg :
      0 ≤ dist (centeredGridVector hm v) (centeredGridVector hm w) := dist_nonneg
  nlinarith

/-- Helper for Theorem 57.6: the one-dimensional centered-grid Tucker lemma,
which is the base case of the cubical parity induction. -/
private theorem exists_complementary_centeredGridNeighbors_one
    (m : ℕ) (label : CenteredGrid 1 m → Fin 1 × Bool)
    (hboundary : ∀ v, centeredGridBoundary v →
      label (centeredGridNeg v) = ((label v).1, !(label v).2)) :
    ∃ a b, centeredGridNeighbor a b ∧
      label b = ((label a).1, !(label a).2) := by
  -- Follow the linear grid from one endpoint to the other; without a complementary
  -- edge its Boolean label would be constant, contradicting the endpoint condition.
  let vertex : Fin (2 * m + 1) → CenteredGrid 1 m := fun j _ ↦ j
  by_contra hcomplement
  push Not at hcomplement
  have hstep (j : Fin (2 * m)) :
      label (vertex j.castSucc) = label (vertex j.succ) := by
    have hneighbor : centeredGridNeighbor (vertex j.castSucc) (vertex j.succ) := by
      intro i
      change j.1 ≤ j.1 + 1 + 1 ∧ j.1 + 1 ≤ j.1 + 1
      omega
    have hne := hcomplement (vertex j.castSucc) (vertex j.succ) hneighbor
    rcases hleft : label (vertex j.castSucc) with ⟨ia, ba⟩
    rcases hright : label (vertex j.succ) with ⟨ib, bb⟩
    have hib : ib = ia := Subsingleton.elim _ _
    subst ib
    simp only [hleft, hright] at hne ⊢
    cases ba <;> cases bb <;> simp_all
  have hconstant (j : Fin (2 * m + 1)) :
      label (vertex j) = label (vertex 0) := by
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih => exact (hstep j).symm.trans ih
  have hzero_boundary : centeredGridBoundary (vertex 0) := by
    refine ⟨0, Or.inl ?_⟩
    rfl
  have hneg_zero :
      centeredGridNeg (vertex 0) = vertex (Fin.last (2 * m)) := by
    funext i
    simp [centeredGridNeg, vertex]
  have hend := hboundary (vertex 0) hzero_boundary
  rw [hneg_zero] at hend
  have hself :
      label (vertex 0) = ((label (vertex 0)).1, !(label (vertex 0)).2) :=
    (hconstant (Fin.last (2 * m))).symm.trans hend
  have hbool := congrArg Prod.snd hself
  exact Bool.self_ne_not _ hbool

/-- Helper for Theorem 57.6: cubical Tucker's lemma for the explicit centered
grid. An antipodal boundary labeling has a complementary pair in one elementary cube. -/
private theorem exists_complementary_centeredGridNeighbors
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (label : CenteredGrid d m → Fin d × Bool)
    (hboundary : ∀ v, centeredGridBoundary v →
      label (centeredGridNeg v) = ((label v).1, !(label v).2)) :
    ∃ a b, centeredGridNeighbor a b ∧
      label b = ((label a).1, !(label a).2) := by
  -- Route correction: use the verified line argument in dimension one and the
  -- isolated mod-two cubical Tucker theorem in every higher dimension.
  by_cases hd_one : d = 1
  · subst d
    exact exists_complementary_centeredGridNeighbors_one m label hboundary
  · have hd_two : 2 ≤ d := by omega
    -- Route correction: reuse the canonical item support theorem instead of
    -- maintaining a duplicate target-local declaration.
    exact exists_complementary_centeredGridNeighbors_of_two_le
      d m hd_two hm label hboundary

/-- Helper for Theorem 57.6: a finite antipodal Tucker certificate in the
closed ball, exposing only boundary pairs, short edges, and complementary labels. -/
private structure TuckerBallMesh (n : ℕ) (δ : ℝ) where
  Vertex : Type
  vertexFinite : Finite Vertex
  point : Vertex → ClosedUnitBall n
  Adjacent : Vertex → Vertex → Prop
  short : ∀ {a b}, Adjacent a b → dist (point a) (point b) < δ
  BoundaryPair : Type
  boundaryPairFinite : Finite BoundaryPair
  positive : BoundaryPair → Vertex
  negative : BoundaryPair → Vertex
  spherePoint : BoundaryPair → StandardSphere n
  positive_point : ∀ p, point (positive p) = toBall n (spherePoint p)
  negative_point : ∀ p, point (negative p) = toBall n (-spherePoint p)
  complementaryEdge :
    ∀ label : Vertex → Fin (n + 1) × Bool,
      (∀ p, label (negative p) = ((label (positive p)).1, !(label (positive p)).2)) →
      ∃ a b, Adjacent a b ∧ label b = ((label a).1, !(label a).2)

/-- Helper for Theorem 57.6: arbitrarily fine antipodal Tucker certificates
exist in every finite-dimensional closed unit ball. -/
private theorem TuckerBallMesh.exists_fine (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (TuckerBallMesh n δ) := by
  -- Restrict the radial clamp to one compact ball containing every realized grid.
  let compactClamp :
      C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) ((n + 1 : ℕ) : ℝ),
        ClosedUnitBall n) :=
    ⟨fun x ↦ radialClampToBall (x : EuclideanSpace ℝ (Fin (n + 1))),
      (continuous_radialClampToBall (n + 1)).comp continuous_subtype_val⟩
  obtain ⟨η, hη, hclamp⟩ := compactClamp.uniform_continuity δ hδ
  -- Choose the grid radius so that a whole elementary cube is inside the uniformity scale.
  have hdim : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hη hdim)
  have hm : 0 < k + 1 := Nat.succ_pos k
  have hk' : 1 / ((k + 1 : ℕ) : ℝ) < η / ((n + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hk
  have hscale : ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) < η := by
    calc
      ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) * (1 / ((k + 1 : ℕ) : ℝ)) := by ring
      _ < ((n + 1 : ℕ) : ℝ) * (η / ((n + 1 : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_left hk' hdim
      _ = η := by field_simp
  -- Package the geometric realization; only the finite cubical Tucker lemma enters
  -- the final complementary-edge field.
  refine ⟨{
    Vertex := CenteredGrid (n + 1) (k + 1)
    vertexFinite := inferInstance
    point := fun v ↦ radialClampToBall (centeredGridVector hm v)
    Adjacent := centeredGridNeighbor
    short := ?_
    BoundaryPair := {v : CenteredGrid (n + 1) (k + 1) // centeredGridBoundary v}
    boundaryPairFinite := inferInstance
    positive := fun p ↦ p.1
    negative := fun p ↦ centeredGridNeg p.1
    spherePoint := fun p ↦
      ⟨(radialClampToBall (centeredGridVector hm p.1) :
          EuclideanSpace ℝ (Fin (n + 1))),
        radialClamp_centeredGridVector_mem_sphere hm p.1 p.2⟩
    positive_point := ?_
    negative_point := ?_
    complementaryEdge := ?_
  }⟩
  · intro a b hab
    let a' : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1)))
        ((n + 1 : ℕ) : ℝ) :=
      ⟨centeredGridVector hm a,
        centeredGridVector_mem_closedBall_dim (Nat.succ_pos n) hm a⟩
    let b' : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1)))
        ((n + 1 : ℕ) : ℝ) :=
      ⟨centeredGridVector hm b,
        centeredGridVector_mem_closedBall_dim (Nat.succ_pos n) hm b⟩
    have hab' : dist a' b' < η := by
      simpa only [a', b', Subtype.dist_eq] using
        (dist_centeredGridVector_le (Nat.succ_pos n) hm hab).trans_lt hscale
    simpa only [compactClamp, ContinuousMap.coe_mk] using hclamp hab'
  · intro p
    apply Subtype.ext
    rw [toBall_apply]
  · intro p
    apply Subtype.ext
    rw [toBall_apply]
    change
      (radialClampToBall (centeredGridVector hm (centeredGridNeg p.1)) :
          EuclideanSpace ℝ (Fin (n + 1))) =
        -((radialClampToBall (centeredGridVector hm p.1) :
          EuclideanSpace ℝ (Fin (n + 1))))
    rw [centeredGridVector_neg, radialClampToBall_neg]
    rfl
  · intro label hboundary
    apply exists_complementary_centeredGridNeighbors (n + 1) (k + 1)
      (Nat.succ_pos n) hm label
    intro v hv
    exact hboundary ⟨v, hv⟩

/-- Helper for Theorem 57.6: every continuous odd self-map of a standard sphere
is not nullhomotopic. -/
theorem oddSelfMap_not_nullhomotopic (n : ℕ)
    (h : C(StandardSphere n, StandardSphere n)) (hodd : Function.Odd h) :
    ¬ h.Nullhomotopic := by
  -- Route correction: degree infrastructure is unavailable here, so the remaining
  -- proof is isolated as the finite Tucker obstruction to a ball extension.
  intro hnull
  obtain ⟨F, hF⟩ :=
    ContinuousMap.exists_closedBallExtension_of_nullhomotopic hnull
  -- Choose a mesh scale on which the ball extension moves less than the label separation.
  have hseparation : 0 < 2 / (n + 1 : ℝ) := by
    positivity
  obtain ⟨δ, hδ, huniform⟩ := F.uniform_continuity (2 / (n + 1 : ℝ)) hseparation
  obtain ⟨mesh⟩ := TuckerBallMesh.exists_fine n hδ
  let label : mesh.Vertex → Fin (n + 1) × Bool :=
    fun v ↦ maximalCoordinateLabel (F (mesh.point v))
  -- On paired boundary vertices, the extension equation and oddness reverse the sign label.
  have hboundary (p : mesh.BoundaryPair) :
      label (mesh.negative p) =
        ((label (mesh.positive p)).1, !(label (mesh.positive p)).2) := by
    dsimp only [label]
    rw [mesh.negative_point, hF, hodd]
    rw [maximalCoordinateLabel_neg]
    rw [mesh.positive_point, hF]
  -- Tucker supplies a short edge whose image labels force the fixed separation, a contradiction.
  obtain ⟨a, b, hab, hlabels⟩ := mesh.complementaryEdge label hboundary
  have hfar : 2 / (n + 1 : ℝ) ≤ dist (F (mesh.point a)) (F (mesh.point b)) :=
    maximalCoordinateLabel_separated (F (mesh.point a)) (F (mesh.point b)) hlabels
  have hclose : dist (F (mesh.point a)) (F (mesh.point b)) < 2 / (n + 1 : ℝ) :=
    huniform (mesh.short hab)
  exact (not_lt_of_ge hfar) hclose

end StandardSphere

/-- Helper for Theorem 57.6: the generalized measurable ham-sandwich theorem
bisects Jordan-measurable sets once the odd-sphere obstruction is available. -/
private lemma existsHyperplaneBisectsJordanMeasurable_of_oddSelfMapsNotNullhomotopic
    (k : ℕ) (hodd : StandardSphere.OddSelfMapsNotNullhomotopic k)
    (A : Fin (k + 1) → Set (EuclideanSpace ℝ (Fin (k + 1))))
    (hA : ∀ i, (A i).IsJordanMeasurable) :
    ∃ (v : EuclideanSpace ℝ (Fin (k + 1))) (c : ℝ),
      ‖v‖ = 1 ∧
        ∀ i, volume (A i ∩ {x | inner ℝ v x ≤ c}) = volume (A i) / 2 := by
  -- Use interiors as bounded measurable representatives of all Jordan sets.
  have hmeasurable : ∀ i, MeasurableSet (interior (A i)) :=
    fun _ ↦ isOpen_interior.measurableSet
  have hbounded : ∀ i, Bornology.IsBounded (interior (A i)) :=
    fun i ↦ (hA i).isBounded.subset interior_subset
  -- Invoke the established higher-dimensional halfspace theorem as an opaque interface.
  obtain ⟨v, c, hv, hbisects⟩ :=
    existsHyperplaneBisects k hodd (fun i ↦ interior (A i)) hmeasurable hbounded
  use v, c
  constructor
  · exact hv
  · intro i
    -- Null frontiers transfer both the cut volume and the total volume back to `A i`.
    calc
      volume (A i ∩ {x | inner ℝ v x ≤ c}) =
          volume (interior (A i) ∩ {x | inner ℝ v x ≤ c}) :=
        (measure_interior_inter_of_null_frontier (hA i).null_frontier).symm
      _ = volume (interior (A i)) / 2 := hbisects i
      _ = volume (A i) / 2 :=
        congrArg (fun m : ENNReal ↦ m / 2)
          (measure_interior_of_null_frontier (hA i).null_frontier)

/-- Theorem 57.6. For positive `n`, any `n` Jordan-measurable subsets of
`EuclideanSpace ℝ (Fin n)` admit a common bisecting affine hyperplane. The witnesses
`v` and `c` describe the hyperplane `{x | inner ℝ v x = c}`; for `n = 3`, this is the
ham sandwich theorem. -/
theorem existsHyperplaneBisectsJordanMeasurable (n : ℕ) (hn : 0 < n)
    (A : Fin n → Set (EuclideanSpace ℝ (Fin n)))
    (hA : ∀ i, (A i).IsJordanMeasurable) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
      ‖v‖ = 1 ∧
        ∀ i, volume (A i ∩ {x | inner ℝ v x ≤ c}) = volume (A i) / 2 := by
  -- Express the positive dimension in the successor form used by the measurable theorem.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hodd : StandardSphere.OddSelfMapsNotNullhomotopic k :=
    StandardSphere.OddSelfMapsNotNullhomotopic.of_forall k
      (StandardSphere.oddSelfMap_not_nullhomotopic k)
  -- The conditional Jordan adapter now supplies the common bisecting hyperplane.
  exact existsHyperplaneBisectsJordanMeasurable_of_oddSelfMapsNotNullhomotopic k hodd A hA
