module

public import Topology_Munkres_2000.Book.Exercise_8_99_6.Charts
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Topology.Separation.NotNormal
public import Mathlib.Topology.Separation.Basic

public section

open Set
open scoped Cardinal

/- Exercise 8.99.6 (1). These are the wedge and sheet-strip sets requested in part (a). -/
#check PruferManifold.upperWedge
#check PruferManifold.mem_upperWedge_iff
#check PruferManifold.sheetStrip
#check PruferManifold.mem_sheetStrip_iff

/- Exercise 8.99.6 (2). The three prescribed families form a basis for the topology. -/
#check PruferManifold.basis_isTopologicalBasis

namespace PruferManifold

/- Exercise 8.99.6 (3). The map `f_c` is a homeomorphism from `ℝ²` onto `A ∪ B_c`. -/
#check chart
#check chart_apply

/- Exercise 8.99.6 (4). Each subspace `A ∪ B_c` is open. -/
#check chartRange_isOpen

/- Exercise 8.99.6 (5). The Prüfer manifold is locally two-Euclidean. -/
#check (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) PruferManifold)

/-- Helper for Exercise 8.99.6: upper coordinate opens are open in the Prüfer topology. -/
private lemma upperOpen_isOpen {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    IsOpen (upperOpen U) := by
  -- Recognize the coordinate open as a member of the defining basis.
  exact basis_isTopologicalBasis.isOpen
    (mem_basis_iff.mpr (Or.inl ⟨U, hU, rfl⟩))

/-- Helper for Exercise 8.99.6: negative sheet-interior coordinate opens are open. -/
private lemma sheetInteriorOpen_isOpen (c : ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    IsOpen (sheetInteriorOpen c U) := by
  -- Recognize the sheet open as a member of the defining basis.
  exact basis_isTopologicalBasis.isOpen
    (mem_basis_iff.mpr (Or.inr (Or.inl ⟨c, U, hU, rfl⟩)))

/-- Helper for Exercise 8.99.6: every prescribed gluing neighborhood is open. -/
private lemma gluingNeighborhood_isOpen {c a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    IsOpen (gluingNeighborhood c a b ε) := by
  -- Recognize the gluing neighborhood as a member of the defining basis.
  exact basis_isTopologicalBasis.isOpen
    (mem_basis_iff.mpr (Or.inr (Or.inr ⟨c, a, b, ε, hab, hε, rfl⟩)))

/-- Helper for Exercise 8.99.6: separation inside one chart lifts to the manifold. -/
private lemma existsOpenSeparation_of_mem_chartRange (c : ℝ) {p q : PruferManifold}
    (hp : p ∈ chartRange c) (hq : q ∈ chartRange c) (hpq : p ≠ q) :
    ∃ u v : Set PruferManifold,
      IsOpen u ∧ IsOpen v ∧ p ∈ u ∧ q ∈ v ∧ Disjoint u v := by
  -- Separate the corresponding subtype points in the Euclidean chart.
  letI : T2Space (chartRange c) := (chart c).t2Space
  have hpq' : (⟨p, hp⟩ : chartRange c) ≠ ⟨q, hq⟩ := by
    intro h
    exact hpq (congrArg Subtype.val h)
  obtain ⟨u, v, hu, hv, hpu, hqv, huv⟩ := t2_separation hpq'
  -- The chart range is ambiently open, so subtype-open images are open.
  refine ⟨Subtype.val '' u, Subtype.val '' v,
    (chartRange_isOpen c).isOpenMap_subtype_val u hu,
    (chartRange_isOpen c).isOpenMap_subtype_val v hv, ?_, ?_, ?_⟩
  · exact ⟨⟨p, hp⟩, hpu, rfl⟩
  · exact ⟨⟨q, hq⟩, hqv, rfl⟩
  · exact Set.disjoint_image_of_injective Subtype.val_injective huv

/-- Helper for Exercise 8.99.6: distinct sheets have disjoint negative interiors. -/
private lemma sheetInteriorOpen_disjoint_of_ne {c d : ℝ} (hcd : c ≠ d) :
    Disjoint (sheetInteriorOpen c Set.univ) (sheetInteriorOpen d Set.univ) := by
  -- A point in both interiors would have two different sheet coordinates.
  refine Set.disjoint_left.mpr ?_
  intro p hpc hpd
  exact hcd ((mem_sheetInteriorOpen_iff.mp hpc).1.symm.trans
    (mem_sheetInteriorOpen_iff.mp hpd).1)

/-- Helper for Exercise 8.99.6: a sheet interior misses every gluing neighborhood
on a distinct sheet. -/
private lemma sheetInteriorOpen_disjoint_gluingNeighborhood_of_ne {c d a b ε : ℝ}
    (hcd : c ≠ d) :
    Disjoint (sheetInteriorOpen c Set.univ) (gluingNeighborhood d a b ε) := by
  -- The wedge has positive first coordinate, while the strip has the wrong sheet coordinate.
  refine Set.disjoint_left.mpr ?_
  intro p hpc hpd
  rcases mem_gluingNeighborhood_iff.mp hpd with hpd | hpd
  · exact (not_lt_of_ge (le_of_lt (mem_upperWedge_iff.mp hpd).1))
      (mem_sheetInteriorOpen_iff.mp hpc).2.1
  · exact hcd ((mem_sheetInteriorOpen_iff.mp hpc).1.symm.trans
      (mem_sheetStrip_iff.mp hpd).1)

/-- Helper for Exercise 8.99.6: a positive radius small enough to separate two boundary wedges. -/
private noncomputable def boundarySeparationRadius (c d m n : ℝ) : ℝ :=
  |c - d| / (|m| + |n| + 2)

/-- Helper for Exercise 8.99.6: the boundary separation radius is positive for distinct sheets. -/
private lemma boundarySeparationRadius_pos {c d m n : ℝ} (hcd : c ≠ d) :
    0 < boundarySeparationRadius c d m n := by
  -- Both the sheet gap and the slope-control denominator are positive.
  unfold boundarySeparationRadius
  have hdenom : 0 < |m| + |n| + 2 := by positivity
  exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hcd)) hdenom

/-- Helper for Exercise 8.99.6: ordered boundary sheets have disjoint sufficiently small
gluing neighborhoods. -/
private lemma gluingNeighborhood_disjoint_of_lt {c d m n : ℝ} (hcd : c < d) :
    Disjoint
      (gluingNeighborhood c (m - 1) (m + 1) (boundarySeparationRadius c d m n))
      (gluingNeighborhood d (n - 1) (n + 1) (boundarySeparationRadius c d m n)) := by
  -- The radius makes the vertical displacement of both wedges smaller than the sheet gap.
  have hdenom : 0 < |m| + |n| + 2 := by positivity
  have hradius :
      (|m| + |n| + 2) * boundarySeparationRadius c d m n = d - c := by
    unfold boundarySeparationRadius
    rw [abs_of_neg (sub_neg.mpr hcd), neg_sub]
    exact mul_div_cancel₀ (d - c) hdenom.ne'
  refine Set.disjoint_left.mpr ?_
  intro p hp hq
  rcases mem_gluingNeighborhood_iff.mp hp with hp | hp
  · rcases mem_gluingNeighborhood_iff.mp hq with hq | hq
    · have hpData := mem_upperWedge_iff.mp hp
      have hqData := mem_upperWedge_iff.mp hq
      have hcontrolled :
          (|m| + |n| + 2) * p.x < d - c := by
        calc
          (|m| + |n| + 2) * p.x <
              (|m| + |n| + 2) * boundarySeparationRadius c d m n :=
            mul_lt_mul_of_pos_left hpData.2.1 hdenom
          _ = d - c := hradius
      have hseparate : c + (m + 1) * p.x < d + (n - 1) * p.x := by
        nlinarith [le_abs_self m, neg_abs_le n]
      linarith [hpData.2.2.2, hqData.2.2.1]
    · exact (not_lt_of_ge (mem_sheetStrip_iff.mp hq).2.2.1)
        (mem_upperWedge_iff.mp hp).1
  · rcases mem_gluingNeighborhood_iff.mp hq with hq | hq
    · exact (not_lt_of_ge (mem_sheetStrip_iff.mp hp).2.2.1)
        (mem_upperWedge_iff.mp hq).1
    · exact hcd.ne ((mem_sheetStrip_iff.mp hp).1.symm.trans
        (mem_sheetStrip_iff.mp hq).1)

/-- Helper for Exercise 8.99.6: nonpositive points on distinct sheets admit disjoint
open neighborhoods. -/
private lemma existsOpenSeparation_of_nonpositive_of_z_ne {p q : PruferManifold}
    (hp : p.x ≤ 0) (hq : q.x ≤ 0) (hpqz : p.z ≠ q.z) :
    ∃ u v : Set PruferManifold,
      IsOpen u ∧ IsOpen v ∧ p ∈ u ∧ q ∈ v ∧ Disjoint u v := by
  -- Split off negative interior points; only two boundary points require a radius estimate.
  rcases hp.lt_or_eq with hpx | hpx
  · rcases hq.lt_or_eq with hqx | hqx
    · refine ⟨sheetInteriorOpen p.z Set.univ, sheetInteriorOpen q.z Set.univ,
        sheetInteriorOpen_isOpen p.z isOpen_univ,
        sheetInteriorOpen_isOpen q.z isOpen_univ, ?_, ?_,
        sheetInteriorOpen_disjoint_of_ne hpqz⟩
      · exact mem_sheetInteriorOpen_iff.mpr ⟨rfl, hpx, Set.mem_univ _⟩
      · exact mem_sheetInteriorOpen_iff.mpr ⟨rfl, hqx, Set.mem_univ _⟩
    · refine ⟨sheetInteriorOpen p.z Set.univ,
        gluingNeighborhood q.z (q.y - 1) (q.y + 1) 1,
        sheetInteriorOpen_isOpen p.z isOpen_univ,
        gluingNeighborhood_isOpen ?_ ?_, ?_, ?_,
        sheetInteriorOpen_disjoint_gluingNeighborhood_of_ne hpqz⟩
      · linarith
      · norm_num
      · exact mem_sheetInteriorOpen_iff.mpr ⟨rfl, hpx, Set.mem_univ _⟩
      · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
        apply Or.inr
        refine ⟨rfl, ?_, hq, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
  · rcases hq.lt_or_eq with hqx | hqx
    · refine ⟨gluingNeighborhood p.z (p.y - 1) (p.y + 1) 1,
        sheetInteriorOpen q.z Set.univ,
        gluingNeighborhood_isOpen ?_ ?_,
        sheetInteriorOpen_isOpen q.z isOpen_univ, ?_, ?_,
        (sheetInteriorOpen_disjoint_gluingNeighborhood_of_ne hpqz.symm).symm⟩
      · linarith
      · norm_num
      · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
        apply Or.inr
        refine ⟨rfl, ?_, hp, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
      · exact mem_sheetInteriorOpen_iff.mpr ⟨rfl, hqx, Set.mem_univ _⟩
    · rcases lt_or_gt_of_ne hpqz with hpzqz | hqzpz
      · let ε := boundarySeparationRadius p.z q.z p.y q.y
        have hεpos : 0 < ε := boundarySeparationRadius_pos hpqz
        refine ⟨gluingNeighborhood p.z (p.y - 1) (p.y + 1) ε,
          gluingNeighborhood q.z (q.y - 1) (q.y + 1) ε,
          gluingNeighborhood_isOpen ?_ hεpos,
          gluingNeighborhood_isOpen ?_ hεpos, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
          apply Or.inr
          refine ⟨rfl, ?_, hp, ?_, ?_⟩
          · linarith
          · linarith
          · linarith
        · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
          apply Or.inr
          refine ⟨rfl, ?_, hq, ?_, ?_⟩
          · linarith
          · linarith
          · linarith
        · exact gluingNeighborhood_disjoint_of_lt hpzqz
      · let ε := boundarySeparationRadius q.z p.z q.y p.y
        have hεpos : 0 < ε := boundarySeparationRadius_pos hpqz.symm
        refine ⟨gluingNeighborhood p.z (p.y - 1) (p.y + 1) ε,
          gluingNeighborhood q.z (q.y - 1) (q.y + 1) ε,
          gluingNeighborhood_isOpen ?_ hεpos,
          gluingNeighborhood_isOpen ?_ hεpos, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
          apply Or.inr
          refine ⟨rfl, ?_, hp, ?_, ?_⟩
          · linarith
          · linarith
          · linarith
        · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
          apply Or.inr
          refine ⟨rfl, ?_, hq, ?_, ?_⟩
          · linarith
          · linarith
          · linarith
        · exact (gluingNeighborhood_disjoint_of_lt hqzpz).symm

/-- Helper for Exercise 8.99.6: the Prüfer manifold is Hausdorff. -/
instance instT2Space : T2Space PruferManifold := by
  -- Put the points in a common chart whenever one is positive or their sheets agree.
  constructor
  intro p q hpq
  by_cases hpx : 0 < p.x
  · have hpChart : p ∈ chartRange q.z := mem_chartRange_iff.mpr (Or.inl hpx)
    have hqChart : q ∈ chartRange q.z := by
      rw [mem_chartRange_iff]
      exact (lt_or_ge 0 q.x).imp_right fun hq ↦ ⟨hq, rfl⟩
    exact existsOpenSeparation_of_mem_chartRange q.z hpChart hqChart hpq
  · by_cases hqx : 0 < q.x
    · have hpChart : p ∈ chartRange p.z :=
        mem_chartRange_iff.mpr (Or.inr ⟨le_of_not_gt hpx, rfl⟩)
      have hqChart : q ∈ chartRange p.z := mem_chartRange_iff.mpr (Or.inl hqx)
      exact existsOpenSeparation_of_mem_chartRange p.z hpChart hqChart hpq
    · have hpNonpositive : p.x ≤ 0 := le_of_not_gt hpx
      have hqNonpositive : q.x ≤ 0 := le_of_not_gt hqx
      by_cases hpqz : p.z = q.z
      · have hpChart : p ∈ chartRange p.z :=
          mem_chartRange_iff.mpr (Or.inr ⟨hpNonpositive, rfl⟩)
        have hqChart : q ∈ chartRange p.z :=
          mem_chartRange_iff.mpr (Or.inr ⟨hqNonpositive, hpqz.symm⟩)
        exact existsOpenSeparation_of_mem_chartRange p.z hpChart hqChart hpq
      · exact existsOpenSeparation_of_nonpositive_of_z_ne
          hpNonpositive hqNonpositive hpqz

/-- The boundary line `L = {(0, 0, c) | c ∈ ℝ}` used to prove nonnormality. -/
def boundaryLine : Set PruferManifold :=
  {p | p.x = 0 ∧ p.y = 0}

/-- Membership in the boundary line is characterized by the two vanishing coordinates. -/
theorem mem_boundaryLine_iff {p : PruferManifold} :
    p ∈ boundaryLine ↔ p.x = 0 ∧ p.y = 0 := by
  -- Membership is the defining coordinate predicate.
  rfl

/-- The boundary line is exactly the range of `c ↦ sheet c 0 0`. -/
theorem boundaryLine_eq_range_sheet :
    boundaryLine = Set.range (fun c : ℝ ↦ sheet c 0 0 (le_refl 0)) := by
  -- Recover the sheet parameter from the third coordinate, and check the converse directly.
  ext p
  constructor
  · intro hp
    have hpCoordinates := mem_boundaryLine_iff.mp hp
    refine ⟨p.z, ?_⟩
    have hx : (sheet p.z 0 0 (le_refl 0)).x = p.x := by
      simpa using hpCoordinates.1.symm
    have hy : (sheet p.z 0 0 (le_refl 0)).y = p.y := by
      simpa using hpCoordinates.2.symm
    have hz : (sheet p.z 0 0 (le_refl 0)).z = p.z := by simp
    exact PruferManifold.ext hx hy hz
  · rintro ⟨c, rfl⟩
    apply mem_boundaryLine_iff.mpr
    constructor
    · simp
    · simp

/-- Helper for Exercise 8.99.6: the boundary line is closed in the Prüfer manifold. -/
theorem boundaryLine_isClosed : IsClosed boundaryLine := by
  -- Cover every point off the line by a basis set that still misses the line.
  rw [← isOpen_compl_iff]
  refine basis_isTopologicalBasis.isOpen_iff.mpr ?_
  intro p hp
  have hpNotBoundary : p ∉ boundaryLine := by
    simpa only [Set.mem_compl_iff] using hp
  rcases lt_trichotomy p.x 0 with hpx | hpx | hpx
  · refine ⟨sheetInteriorOpen p.z Set.univ,
      mem_basis_iff.mpr (Or.inr (Or.inl ⟨p.z, Set.univ, isOpen_univ, rfl⟩)),
      mem_sheetInteriorOpen_iff.mpr ⟨rfl, hpx, Set.mem_univ _⟩, ?_⟩
    intro q hq
    rw [Set.mem_compl_iff]
    intro hqBoundary
    linarith [(mem_sheetInteriorOpen_iff.mp hq).2.1,
      (mem_boundaryLine_iff.mp hqBoundary).1]
  · have hpy : p.y ≠ 0 := by
      intro hpy
      exact hpNotBoundary (mem_boundaryLine_iff.mpr ⟨hpx, hpy⟩)
    rcases lt_or_gt_of_ne hpy with hpy | hpy
    · refine ⟨gluingNeighborhood p.z (3 * p.y / 2) (p.y / 2) 1,
        ?_, ?_, ?_⟩
      · apply mem_basis_iff.mpr
        apply Or.inr
        apply Or.inr
        refine ⟨p.z, 3 * p.y / 2, p.y / 2, 1, ?_, ?_, rfl⟩
        · linarith
        · norm_num
      · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
        apply Or.inr
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
        · linarith
      · intro q hq
        rw [Set.mem_compl_iff]
        intro hqBoundary
        rcases mem_gluingNeighborhood_iff.mp hq with hq | hq
        · linarith [(mem_upperWedge_iff.mp hq).1,
            (mem_boundaryLine_iff.mp hqBoundary).1]
        · linarith [(mem_sheetStrip_iff.mp hq).2.2.2.2,
            (mem_boundaryLine_iff.mp hqBoundary).2]
    · refine ⟨gluingNeighborhood p.z (p.y / 2) (3 * p.y / 2) 1,
        ?_, ?_, ?_⟩
      · apply mem_basis_iff.mpr
        apply Or.inr
        apply Or.inr
        refine ⟨p.z, p.y / 2, 3 * p.y / 2, 1, ?_, ?_, rfl⟩
        · linarith
        · norm_num
      · rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
        apply Or.inr
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
        · linarith
      · intro q hq
        rw [Set.mem_compl_iff]
        intro hqBoundary
        rcases mem_gluingNeighborhood_iff.mp hq with hq | hq
        · linarith [(mem_upperWedge_iff.mp hq).1,
            (mem_boundaryLine_iff.mp hqBoundary).1]
        · linarith [(mem_sheetStrip_iff.mp hq).2.2.2.1,
            (mem_boundaryLine_iff.mp hqBoundary).2]
  · refine ⟨upperOpen Set.univ,
      mem_basis_iff.mpr (Or.inl ⟨Set.univ, isOpen_univ, rfl⟩),
      mem_upperOpen_iff.mpr ⟨hpx, Set.mem_univ _⟩, ?_⟩
    intro q hq
    rw [Set.mem_compl_iff]
    intro hqBoundary
    linarith [(mem_upperOpen_iff.mp hq).1,
      (mem_boundaryLine_iff.mp hqBoundary).1]

/-- Helper for Exercise 8.99.6: a standard gluing neighborhood isolates each point of
the boundary line. -/
private lemma boundaryLineIsolation (p : PruferManifold) (hp : p ∈ boundaryLine) :
    gluingNeighborhood p.z (-1) 1 1 ∩ boundaryLine = {p} := by
  -- Boundary membership eliminates the wedge and fixes all coordinates in the strip.
  ext q
  constructor
  · intro hq
    have hpCoordinates := mem_boundaryLine_iff.mp hp
    have hqCoordinates := mem_boundaryLine_iff.mp hq.2
    rcases mem_gluingNeighborhood_iff.mp hq.1 with hqWedge | hqStrip
    · exfalso
      linarith [(mem_upperWedge_iff.mp hqWedge).1, hqCoordinates.1]
    · rw [Set.mem_singleton_iff]
      exact PruferManifold.ext (hqCoordinates.1.trans hpCoordinates.1.symm)
        (hqCoordinates.2.trans hpCoordinates.2.symm) (mem_sheetStrip_iff.mp hqStrip).1
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    have hpCoordinates := mem_boundaryLine_iff.mp hp
    refine ⟨?_, hp⟩
    rw [mem_gluingNeighborhood_iff, mem_sheetStrip_iff]
    apply Or.inr
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith

/-- Helper for Exercise 8.99.6: the boundary line has the discrete subspace topology. -/
instance instDiscreteTopologyBoundaryLine : DiscreteTopology boundaryLine := by
  -- Use the explicit isolating gluing neighborhood at every boundary point.
  rw [discreteTopology_subtype_iff']
  intro p hp
  refine ⟨gluingNeighborhood p.z (-1) 1 1,
    gluingNeighborhood_isOpen ?_ ?_, boundaryLineIsolation p hp⟩
  · norm_num
  · norm_num

/-- Helper for Exercise 8.99.6: the closed nonnegative part used for the cardinality
obstruction. -/
private def nonnegativePart : Set PruferManifold :=
  {p | 0 ≤ p.x}

/-- Helper for Exercise 8.99.6: membership in the nonnegative part is the coordinate
inequality `0 ≤ p.x`. -/
private lemma mem_nonnegativePart_iff {p : PruferManifold} :
    p ∈ nonnegativePart ↔ 0 ≤ p.x := by
  -- Unfold the defining coordinate condition.
  rfl

/-- Helper for Exercise 8.99.6: the nonnegative part of the Prüfer manifold is closed. -/
private lemma nonnegativePart_isClosed : IsClosed nonnegativePart := by
  -- Its complement is covered by negative sheet-interior basis opens.
  rw [← isOpen_compl_iff]
  refine basis_isTopologicalBasis.isOpen_iff.mpr ?_
  intro p hp
  have hpx : p.x < 0 := by
    have hpNot : ¬0 ≤ p.x := by
      simpa only [Set.mem_compl_iff, mem_nonnegativePart_iff] using hp
    exact lt_of_not_ge hpNot
  refine ⟨sheetInteriorOpen p.z Set.univ,
    mem_basis_iff.mpr (Or.inr (Or.inl ⟨p.z, Set.univ, isOpen_univ, rfl⟩)),
    mem_sheetInteriorOpen_iff.mpr ⟨rfl, hpx, Set.mem_univ _⟩, ?_⟩
  intro q hq
  rw [Set.mem_compl_iff, mem_nonnegativePart_iff]
  exact not_le_of_gt (mem_sheetInteriorOpen_iff.mp hq).2.1

/-- Helper for Exercise 8.99.6: the positive portion of the chart indexed by zero. -/
private def positiveChartPart : Set (chartRange 0) :=
  {p | 0 < p.1.x}

/-- Helper for Exercise 8.99.6: a point in the positive chart part lies in the
nonnegative part. -/
private lemma positiveChartPart_mem_nonnegative (p : positiveChartPart) :
    p.1.1 ∈ nonnegativePart := by
  -- Strict positivity implies the required weak inequality.
  exact mem_nonnegativePart_iff.mpr (le_of_lt p.2)

/-- Helper for Exercise 8.99.6: the positive chart part includes into the closed
nonnegative part. -/
private def positiveChartPartToNonnegative (p : positiveChartPart) : nonnegativePart :=
  ⟨p.1.1, positiveChartPart_mem_nonnegative p⟩

/-- Helper for Exercise 8.99.6: the positive-part inclusion has the expected ambient value. -/
private lemma positiveChartPartToNonnegative_coe (p : positiveChartPart) :
    (positiveChartPartToNonnegative p).1 = p.1.1 := by
  -- The inclusion changes only the recorded membership proof.
  rfl

/-- Helper for Exercise 8.99.6: the positive-part inclusion is continuous. -/
private lemma continuous_positiveChartPartToNonnegative :
    Continuous positiveChartPartToNonnegative := by
  -- Compose the two subtype inclusions and repackage the nonnegative membership proof.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    positiveChartPart_mem_nonnegative

/-- Helper for Exercise 8.99.6: halving a positive gluing radius remains positive. -/
private lemma halfGluingRadius_pos {ε : ℝ} (hε : 0 < ε) : 0 < ε / 2 := by
  -- Division by two preserves strict positivity.
  positivity

/-- Helper for Exercise 8.99.6: the upper point using the midpoint slope of a gluing
neighborhood. -/
private noncomputable def upperMidpoint (c a b ε : ℝ) (hε : 0 < ε) : PruferManifold :=
  upper (ε / 2) (c + ((a + b) / 2) * (ε / 2)) (halfGluingRadius_pos hε)

/-- Helper for Exercise 8.99.6: the upper midpoint has positive first coordinate. -/
private lemma upperMidpoint_x_pos {c a b ε : ℝ} (hε : 0 < ε) :
    0 < (upperMidpoint c a b ε hε).x := by
  -- Read the first coordinate from the explicit upper point.
  simpa only [upperMidpoint, upper_x] using halfGluingRadius_pos hε

/-- Helper for Exercise 8.99.6: the upper midpoint lies in its gluing neighborhood. -/
private lemma upperMidpoint_mem_gluingNeighborhood {c a b ε : ℝ}
    (hab : a < b) (hε : 0 < ε) :
    upperMidpoint c a b ε hε ∈ gluingNeighborhood c a b ε := by
  -- Its radius is halved and its slope is strictly between the two endpoint slopes.
  rw [mem_gluingNeighborhood_iff, mem_upperWedge_iff]
  apply Or.inl
  simp only [upperMidpoint, upper_x, upper_y]
  have hhalf : 0 < ε / 2 := halfGluingRadius_pos hε
  have hslopeLower : a < (a + b) / 2 := by linarith
  have hslopeUpper : (a + b) / 2 < b := by linarith
  constructor
  · exact hhalf
  constructor
  · linarith
  constructor
  · nlinarith
  · nlinarith

/-- Helper for Exercise 8.99.6: the positive chart part has dense image in the
nonnegative part. -/
private lemma denseRange_positiveChartPartToNonnegative :
    DenseRange positiveChartPartToNonnegative := by
  -- Meet an arbitrary nonempty subtype-open set, using a gluing midpoint at its boundary points.
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUNonempty
  obtain ⟨p, hpU⟩ := hUNonempty
  obtain ⟨C, hCOpen, hUImage⟩ := hU.image_val
  have hpImage : p.1 ∈ Subtype.val '' U := ⟨p, hpU, rfl⟩
  have hpC : p.1 ∈ C := by
    rw [hUImage] at hpImage
    exact hpImage.1
  by_cases hpx : 0 < p.1.x
  · have hpChart : p.1 ∈ chartRange 0 := mem_chartRange_iff.mpr (Or.inl hpx)
    let pChart : chartRange 0 := ⟨p.1, hpChart⟩
    have hpPositive : pChart ∈ positiveChartPart := hpx
    let r : positiveChartPart := ⟨pChart, hpPositive⟩
    have hrValue : positiveChartPartToNonnegative r = p := by
      apply Subtype.ext
      exact positiveChartPartToNonnegative_coe r
    refine ⟨p, hpU, ?_⟩
    exact ⟨r, hrValue⟩
  · have hpxZero : p.1.x = 0 :=
      le_antisymm (le_of_not_gt hpx) (mem_nonnegativePart_iff.mp p.2)
    obtain ⟨s, hsBasis, hps, hsC⟩ :=
      basis_isTopologicalBasis.isOpen_iff.mp hCOpen p.1 hpC
    obtain ⟨a, b, ε, hab, hε, hs, ha, hb⟩ :=
      exists_gluingParameters_of_mem_basis_of_x_eq_zero hsBasis hps hpxZero
    let rPoint := upperMidpoint p.1.z a b ε hε
    have hrS : rPoint ∈ s := by
      rw [hs]
      exact upperMidpoint_mem_gluingNeighborhood hab hε
    have hrPositive : 0 < rPoint.x := upperMidpoint_x_pos hε
    have hrChart : rPoint ∈ chartRange 0 := mem_chartRange_iff.mpr (Or.inl hrPositive)
    let rChart : chartRange 0 := ⟨rPoint, hrChart⟩
    have hrPositiveChart : rChart ∈ positiveChartPart := hrPositive
    let r : positiveChartPart := ⟨rChart, hrPositiveChart⟩
    have hrImage : (positiveChartPartToNonnegative r).1 ∈ Subtype.val '' U := by
      rw [hUImage, positiveChartPartToNonnegative_coe]
      exact ⟨hsC hrS, positiveChartPart_mem_nonnegative r⟩
    obtain ⟨q, hqU, hqValue⟩ := hrImage
    have hq : q = positiveChartPartToNonnegative r := by
      apply Subtype.ext
      exact hqValue
    refine ⟨positiveChartPartToNonnegative r, ?_, Set.mem_range_self r⟩
    rwa [← hq]

/-- Helper for Exercise 8.99.6: the boundary line viewed inside the nonnegative part. -/
private def boundaryLineWithinNonnegative : Set nonnegativePart :=
  {p | p.1 ∈ boundaryLine}

/-- Helper for Exercise 8.99.6: the internal boundary line is closed in the
nonnegative part. -/
private lemma boundaryLineWithinNonnegative_isClosed :
    IsClosed boundaryLineWithinNonnegative := by
  -- It is the preimage of the ambient closed boundary line under subtype inclusion.
  exact boundaryLine_isClosed.preimage continuous_subtype_val

/-- Helper for Exercise 8.99.6: the internal boundary line has the discrete topology. -/
private lemma boundaryLineWithinNonnegative_discreteTopology :
    DiscreteTopology boundaryLineWithinNonnegative := by
  -- Pull the ambient isolating gluing neighborhoods back to the nonnegative subtype.
  rw [discreteTopology_subtype_iff']
  intro p hp
  let G : Set nonnegativePart :=
    Subtype.val ⁻¹' gluingNeighborhood p.1.z (-1) 1 1
  have hGOpen : IsOpen G := by
    have hLowerUpper : (-1 : ℝ) < 1 := by norm_num
    have hRadius : (0 : ℝ) < 1 := by norm_num
    exact (gluingNeighborhood_isOpen hLowerUpper hRadius).preimage continuous_subtype_val
  refine ⟨G, hGOpen, ?_⟩
  ext q
  constructor
  · intro hq
    have hqAmbient : q.1 ∈ gluingNeighborhood p.1.z (-1) 1 1 ∩ boundaryLine :=
      ⟨hq.1, hq.2⟩
    rw [boundaryLineIsolation p.1 hp] at hqAmbient
    rw [Set.mem_singleton_iff]
    exact Subtype.ext (Set.mem_singleton_iff.mp hqAmbient)
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    have hpAmbient : p.1 ∈ gluingNeighborhood p.1.z (-1) 1 1 ∩ boundaryLine := by
      rw [boundaryLineIsolation p.1 hp]
      exact Set.mem_singleton p.1
    exact ⟨hpAmbient.1, hp⟩

/-- Helper for Exercise 8.99.6: a standard boundary point belongs to the
nonnegative part. -/
private lemma sheetZero_mem_nonnegativePart (c : ℝ) :
    sheet c 0 0 (le_refl 0) ∈ nonnegativePart := by
  -- Its first coordinate is zero.
  apply mem_nonnegativePart_iff.mpr
  simp

/-- Helper for Exercise 8.99.6: a standard boundary point belongs to the internal
boundary line. -/
private lemma sheetZero_mem_boundaryLineWithinNonnegative (c : ℝ) :
    (⟨sheet c 0 0 (le_refl 0), sheetZero_mem_nonnegativePart c⟩ : nonnegativePart) ∈
      boundaryLineWithinNonnegative := by
  -- Both boundary coordinates vanish.
  apply mem_boundaryLine_iff.mpr
  constructor
  · simp
  · simp

/-- Helper for Exercise 8.99.6: the real line parametrizes the internal boundary line. -/
private def boundaryLineWithinNonnegativeParam (c : ℝ) :
    boundaryLineWithinNonnegative :=
  ⟨⟨sheet c 0 0 (le_refl 0), sheetZero_mem_nonnegativePart c⟩,
    sheetZero_mem_boundaryLineWithinNonnegative c⟩

/-- Helper for Exercise 8.99.6: the real boundary parametrization is injective. -/
private lemma boundaryLineWithinNonnegativeParam_injective :
    Function.Injective boundaryLineWithinNonnegativeParam := by
  -- Equality of boundary points forces equality of their sheet coordinates.
  intro c d hcd
  have hz := congrArg
    (fun p : boundaryLineWithinNonnegative ↦ p.1.1.z) hcd
  simpa only [boundaryLineWithinNonnegativeParam, sheet_z] using hz

/-- Helper for Exercise 8.99.6: the closed nonnegative part is not normal. -/
private lemma nonnegativePart_not_normal : ¬ NormalSpace nonnegativePart := by
  -- The dense positive chart supplies separability of the closed nonnegative part.
  letI : SecondCountableTopology (chartRange 0) :=
    (chart 0).symm.secondCountableTopology
  letI : TopologicalSpace.SeparableSpace nonnegativePart :=
    denseRange_positiveChartPartToNonnegative.separableSpace
      continuous_positiveChartPartToNonnegative
  letI : DiscreteTopology boundaryLineWithinNonnegative :=
    boundaryLineWithinNonnegative_discreteTopology
  have hCardinality : 𝔠 ≤ Cardinal.mk boundaryLineWithinNonnegative := by
    simpa only [Cardinal.mk_real] using
      Cardinal.mk_le_of_injective boundaryLineWithinNonnegativeParam_injective
  -- Apply the closed-discrete cardinality obstruction in this separable subspace.
  exact boundaryLineWithinNonnegative_isClosed.not_normal_of_continuum_le_mk hCardinality

/-- Exercise 8.99.6 (9). The Prüfer manifold is not normal. -/
theorem not_normal : ¬ NormalSpace PruferManifold := by
  -- Ambient normality would pass to the closed nonnegative part, contradicting its obstruction.
  intro hNormal
  letI : NormalSpace PruferManifold := hNormal
  letI : NormalSpace nonnegativePart :=
    nonnegativePart_isClosed.isClosedEmbedding_subtypeVal.normalSpace
  exact nonnegativePart_not_normal inferInstance

end PruferManifold
