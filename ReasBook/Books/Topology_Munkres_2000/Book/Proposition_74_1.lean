module

public import Topology_Munkres_2000.Book.Proposition_74_1.Segments
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Separation.Hausdorff

public section

namespace CyclicPolygon

open Set

noncomputable section

variable {n : ℕ}

/-- Helper for Proposition 74.1: distinct indices determine distinct cyclic vertices. -/
lemma vertices_injective (P : CyclicPolygon n) : Function.Injective P.toPolygon.vertices := by
  -- Equality of vertices gives equality of their two circle-map coordinates.
  intro i j hij
  rw [P.toPolygon_vertices, P.toPolygon_vertices] at hij
  have hcos : P.radius * Real.cos (P.angles i.castSucc) =
      P.radius * Real.cos (P.angles j.castSucc) := by
    have hcoordinate := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hij
    simpa [vertex, PiLp.toLp_apply] using hcoordinate
  have hsin : P.radius * Real.sin (P.angles i.castSucc) =
      P.radius * Real.sin (P.angles j.castSucc) := by
    have hcoordinate := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hij
    simpa [vertex, PiLp.toLp_apply] using hcoordinate
  have hcircle : circleMap 0 P.radius (P.angles i.castSucc) =
      circleMap 0 P.radius (P.angles j.castSucc) := by
    apply Complex.ext
    · simpa [circleMap_zero_re] using hcos
    · simpa [circleMap_zero_im] using hsin
  -- The first `n` lifted angles lie in one half-open interval of length `2 * π`.
  have hi_upper := P.angles_strictMono (Fin.castSucc_lt_last i)
  have hj_upper := P.angles_strictMono (Fin.castSucc_lt_last j)
  have hi_lower : P.angles 0 ≤ P.angles i.castSucc :=
    P.angles_strictMono.monotone (Fin.zero_le _)
  have hj_lower : P.angles 0 ≤ P.angles j.castSucc :=
    P.angles_strictMono.monotone (Fin.zero_le _)
  have hdist : |P.angles i.castSucc - P.angles j.castSucc| < 2 * Real.pi := by
    rw [P.angles_last] at hi_upper hj_upper
    rw [abs_lt]
    constructor <;> linarith
  have hangles : P.angles i.castSucc = P.angles j.castSucc :=
    eq_of_circleMap_eq P.radius_pos.ne' hdist hcircle
  exact Fin.castSucc_inj.mp (P.angles_strictMono.injective hangles)

/-- Helper for Proposition 74.1: on at least three cyclic indices, applying the cyclic
successor twice never returns to the starting index. -/
lemma finRotate_sq_ne_self_of_three_le {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    finRotate m (finRotate m i) ≠ i := by
  -- Applying the inverse rotation would identify the successor with the predecessor.
  intro hcycle
  have hneighbors := congrArg (finRotate m).symm hcycle
  simp only [Equiv.symm_apply_apply] at hneighbors
  exact (finRotate_symm_ne_finRotate_of_three_le hm i) hneighbors.symm

/-- Helper for Proposition 74.1: the zero endpoint of `unitInterval` has real value zero. -/
lemma unitInterval_coe_zero : (((0 : unitInterval) : unitInterval) : ℝ) = 0 := rfl

/-- Helper for Proposition 74.1: the one endpoint of `unitInterval` has real value one. -/
lemma unitInterval_coe_one : (((1 : unitInterval) : unitInterval) : ℝ) = 1 := rfl

/-- Helper for Proposition 74.1: affine parameters on one cyclic edge are unique. -/
lemma edgePoint_injective (P : CyclicPolygon n) (i : Fin n) :
    Function.Injective (P.edgePoint i) := by
  -- Equality in the polygon boundary induces equality in the oriented edge carrier.
  intro s t hst
  apply (P.orientedEdge i).paramHomeomorph.injective
  apply Subtype.ext
  rw [← P.edgePoint_coe, ← P.edgePoint_coe]
  exact congrArg Subtype.val hst

/-- Helper for Proposition 74.1: signed area along a parameterized edge is the affine
combination of the signed areas at its endpoints. -/
lemma signedArea_edgePoint_eq (P : CyclicPolygon n) (i j : Fin n) (t : unitInterval) :
    signedArea
        (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
        ((P.edgePoint j t : EuclideanSpace ℝ (Fin 2)) - P.toPolygon.vertices i) =
      (1 - (t : ℝ)) * signedArea
          (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
          (P.toPolygon.vertices j - P.toPolygon.vertices i) +
        (t : ℝ) * signedArea
          (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
          (P.toPolygon.vertices (finRotate n j) - P.toPolygon.vertices i) := by
  -- Expand the affine line map; bilinearity of the determinant gives the formula.
  rw [P.edgePoint_coe_eq_lineMap, AffineMap.lineMap_apply_module]
  simp only [← signedAreaRightCLM_apply, map_sub, map_add, map_smul, smul_eq_mul]
  ring

/-- Helper for Proposition 74.1: a point parameterized on an edge lies on that edge's
supporting line. -/
lemma signedArea_edgePoint_self (P : CyclicPolygon n) (i : Fin n) (s : unitInterval) :
    signedArea
        (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
        ((P.edgePoint i s : EuclideanSpace ℝ (Fin 2)) - P.toPolygon.vertices i) = 0 := by
  -- Both endpoint determinants vanish, so the affine determinant vanishes as well.
  rw [P.signedArea_edgePoint_eq]
  rw [(P.signedArea_edge_vertex_nonneg_and_eq_zero i i).2.mpr (Or.inl rfl),
    (P.signedArea_edge_vertex_nonneg_and_eq_zero i (finRotate n i)).2.mpr (Or.inr rfl)]
  ring

/-- Helper for Proposition 74.1: two edge parameters represent the same boundary point
exactly when they agree on one edge or describe a common cyclic endpoint. -/
lemma edgePoint_eq_iff (P : CyclicPolygon n) (i j : Fin n) (s t : unitInterval) :
    P.edgePoint i s = P.edgePoint j t ↔
      (i = j ∧ s = t) ∨
        (s = 0 ∧ t = 1 ∧ i = finRotate n j) ∨
          (s = 1 ∧ t = 0 ∧ finRotate n i = j) := by
  constructor
  · intro hpoint
    have hval := congrArg Subtype.val hpoint
    have hzero : signedArea
        (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
        ((P.edgePoint j t : EuclideanSpace ℝ (Fin 2)) - P.toPolygon.vertices i) = 0 := by
      rw [← hval]
      exact P.signedArea_edgePoint_self i s
    have hj_nonneg := (P.signedArea_edge_vertex_nonneg_and_eq_zero i j).1
    have hjrot_nonneg :=
      (P.signedArea_edge_vertex_nonneg_and_eq_zero i (finRotate n j)).1
    rw [P.signedArea_edgePoint_eq] at hzero
    -- Endpoint parameters are classified directly by the zero-area endpoint theorem.
    by_cases ht_zero : (t : ℝ) = 0
    · have ht : t = 0 := Subtype.ext ht_zero
      subst t
      simp only [unitInterval_coe_zero, sub_zero, one_mul, zero_mul, add_zero] at hzero
      rcases (P.signedArea_edge_vertex_nonneg_and_eq_zero i j).2.mp hzero with hji | hji
      · subst j
        exact Or.inl ⟨rfl, P.edgePoint_injective i hpoint⟩
      · have hs : s = 1 := by
          apply P.edgePoint_injective i
          apply Subtype.ext
          rw [P.edgePoint_coe_eq_lineMap, P.edgePoint_coe_eq_lineMap,
            AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at hval
          rw [P.edgePoint_coe_eq_lineMap, P.edgePoint_coe_eq_lineMap,
            AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
          simpa only [unitInterval_coe_one, unitInterval_coe_zero, sub_zero, one_smul,
            zero_smul, add_zero, zero_add, sub_self, hji] using hval
        exact Or.inr (Or.inr ⟨hs, rfl, hji.symm⟩)
    by_cases ht_one : (t : ℝ) = 1
    · have ht : t = 1 := Subtype.ext ht_one
      subst t
      simp only [unitInterval_coe_one, sub_self, zero_mul, one_mul, zero_add] at hzero
      rcases (P.signedArea_edge_vertex_nonneg_and_eq_zero i (finRotate n j)).2.mp hzero with
        hjrot_i | hjrot_rot
      · have hs : s = 0 := by
          apply P.edgePoint_injective i
          apply Subtype.ext
          rw [P.edgePoint_coe_eq_lineMap, P.edgePoint_coe_eq_lineMap,
            AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at hval
          rw [P.edgePoint_coe_eq_lineMap, P.edgePoint_coe_eq_lineMap,
            AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
          simpa only [unitInterval_coe_zero, unitInterval_coe_one, sub_zero, one_smul,
            zero_smul, add_zero, zero_add, sub_self, hjrot_i] using hval
        exact Or.inr (Or.inl ⟨hs, rfl, hjrot_i.symm⟩)
      · have hji : j = i := (finRotate n).injective hjrot_rot
        subst j
        exact Or.inl ⟨rfl, P.edgePoint_injective i hpoint⟩
    -- At an interior parameter both nonnegative endpoint determinants must vanish.
    have ht_pos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht_zero)
    have ht_lt_one : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht_one
    have hleft_nonneg : 0 ≤ (1 - (t : ℝ)) * signedArea
        (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
        (P.toPolygon.vertices j - P.toPolygon.vertices i) :=
      mul_nonneg (sub_nonneg.mpr t.property.2) hj_nonneg
    have hright_nonneg : 0 ≤ (t : ℝ) * signedArea
        (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
        (P.toPolygon.vertices (finRotate n j) - P.toPolygon.vertices i) :=
      mul_nonneg t.property.1 hjrot_nonneg
    have hj_zero : signedArea
        (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
        (P.toPolygon.vertices j - P.toPolygon.vertices i) = 0 := by
      have hproduct : (1 - (t : ℝ)) * signedArea
          (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
          (P.toPolygon.vertices j - P.toPolygon.vertices i) = 0 := by
        linarith
      exact (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr (Ne.symm ht_one))
    have hjrot_zero : signedArea
        (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
        (P.toPolygon.vertices (finRotate n j) - P.toPolygon.vertices i) = 0 := by
      have hproduct : (t : ℝ) * signedArea
          (P.toPolygon.vertices (finRotate n i) - P.toPolygon.vertices i)
          (P.toPolygon.vertices (finRotate n j) - P.toPolygon.vertices i) = 0 := by
        linarith
      exact (mul_eq_zero.mp hproduct).resolve_left ht_zero
    rcases (P.signedArea_edge_vertex_nonneg_and_eq_zero i j).2.mp hj_zero with hji | hji
    · subst j
      exact Or.inl ⟨rfl, P.edgePoint_injective i hpoint⟩
    · rcases
        (P.signedArea_edge_vertex_nonneg_and_eq_zero i (finRotate n j)).2.mp hjrot_zero with
        hjrot_i | hjrot_rot
      · subst j
        exact False.elim (finRotate_sq_ne_self_of_three_le P.three_le i hjrot_i)
      · subst j
        exact False.elim
          (finRotate_ne_self_of_two_le (P.three_le.trans' (by omega)) (finRotate n i) hjrot_rot)
  · rintro (⟨rfl, rfl⟩ | ⟨hs, ht, hi⟩ | ⟨hs, ht, hi⟩)
    · rfl
    · subst s
      subst t
      apply Subtype.ext
      rw [P.edgePoint_coe_eq_lineMap, P.edgePoint_coe_eq_lineMap,
        AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      simp only [unitInterval_coe_zero, unitInterval_coe_one, sub_zero, one_smul, zero_smul,
        add_zero, zero_add, sub_self, hi]
    · subst s
      subst t
      apply Subtype.ext
      rw [P.edgePoint_coe_eq_lineMap, P.edgePoint_coe_eq_lineMap,
        AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      simp only [unitInterval_coe_zero, unitInterval_coe_one, sub_zero, one_smul, zero_smul,
        add_zero, zero_add, sub_self, hi]

/-- Helper for Proposition 74.1: affine parameters on one radial segment are unique. -/
lemma radialPoint_injective (P : CyclicPolygon n) (p : P.interior) (x : P.boundary) :
    Function.Injective (P.radialPoint p x) := by
  -- The center is not a boundary point, so the affine line map is injective in its scalar.
  intro s t hst
  apply Subtype.ext
  have hpx : (p : EuclideanSpace ℝ (Fin 2)) ≠ (x : EuclideanSpace ℝ (Fin 2)) := by
    have hpDiff : (p : EuclideanSpace ℝ (Fin 2)) ∈ P.region \ P.boundary :=
      Eq.mp (congrArg
        (fun S : Set (EuclideanSpace ℝ (Fin 2)) ↦ (p : EuclideanSpace ℝ (Fin 2)) ∈ S)
        P.interior_def) p.property
    intro h
    apply hpDiff.2
    rw [h]
    exact x.property
  apply AffineMap.lineMap_injective ℝ hpx
  rw [← P.radialPoint_coe_eq_lineMap, ← P.radialPoint_coe_eq_lineMap]
  exact congrArg Subtype.val hst

/-- Helper for Proposition 74.1: every parameterized radial point belongs to its geometric
segment from the chosen interior point to the boundary. -/
lemma radialPoint_mem_segment (P : CyclicPolygon n) (p : P.interior)
    (x : P.boundary) (s : unitInterval) :
    (P.radialPoint p x s : EuclideanSpace ℝ (Fin 2)) ∈
      segment ℝ (p : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2)) := by
  -- Use the standard image description of a closed segment.
  rw [P.radialPoint_coe_eq_lineMap, segment_eq_image_lineMap]
  exact ⟨s, s.property, rfl⟩

/-- Helper for Proposition 74.1: two radial parameters represent the same region point
exactly at the common center or on the same radial segment with the same parameter. -/
lemma radialPoint_eq_iff (P : CyclicPolygon n) (p : P.interior)
    (x y : P.boundary) (s t : unitInterval) :
    P.radialPoint p x s = P.radialPoint p y t ↔
      (s = 0 ∧ t = 0) ∨ (x = y ∧ s = t) := by
  constructor
  · intro hpoint
    by_cases hxy : x = y
    · subst y
      exact Or.inr ⟨rfl, P.radialPoint_injective p x hpoint⟩
    have hval := congrArg Subtype.val hpoint
    have hxy_val : (x : EuclideanSpace ℝ (Fin 2)) ≠
        (y : EuclideanSpace ℝ (Fin 2)) := by
      intro h
      exact hxy (Subtype.ext h)
    have hintersection : (P.radialPoint p x s : EuclideanSpace ℝ (Fin 2)) ∈
        segment ℝ (p : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2)) ∩
          segment ℝ (p : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 2)) := by
      constructor
      · exact P.radialPoint_mem_segment p x s
      · rw [hval]
        exact P.radialPoint_mem_segment p y t
    rw [P.segment_inter_segment p.property x.property y.property hxy_val,
      mem_singleton_iff] at hintersection
    have hs : s = 0 := by
      apply P.radialPoint_injective p x
      apply Subtype.ext
      rw [P.radialPoint_coe_eq_lineMap] at hintersection
      rw [P.radialPoint_coe_eq_lineMap, P.radialPoint_coe_eq_lineMap]
      simp only [unitInterval_coe_zero, AffineMap.lineMap_apply_zero]
      exact hintersection
    have htcenter : (P.radialPoint p y t : EuclideanSpace ℝ (Fin 2)) =
        (p : EuclideanSpace ℝ (Fin 2)) := hval.symm.trans hintersection
    have ht : t = 0 := by
      apply P.radialPoint_injective p y
      apply Subtype.ext
      rw [P.radialPoint_coe_eq_lineMap] at htcenter
      rw [P.radialPoint_coe_eq_lineMap, P.radialPoint_coe_eq_lineMap]
      simp only [unitInterval_coe_zero, AffineMap.lineMap_apply_zero]
      exact htcenter
    exact Or.inl ⟨hs, ht⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · apply Subtype.ext
      rw [P.radialPoint_coe_eq_lineMap, P.radialPoint_coe_eq_lineMap]
      simp only [unitInterval_coe_zero, AffineMap.lineMap_apply_zero]
    · rfl

/-- Helper for Proposition 74.1: the joint cyclic edge parameterization is continuous. -/
lemma continuous_edgePoint (P : CyclicPolygon n) :
    Continuous (fun z : Fin n × unitInterval ↦ P.edgePoint z.1 z.2) := by
  -- The finite index is discrete, and each affine edge parameterization is continuous.
  refine continuous_prod_of_discrete_left.mpr ?_
  intro i
  rw [continuous_induced_rng]
  have hline : Continuous (fun s : unitInterval ↦
      AffineMap.lineMap (P.toPolygon.vertices i)
        (P.toPolygon.vertices (finRotate n i)) (s : ℝ)) :=
    AffineMap.lineMap_continuous.comp continuous_subtype_val
  refine hline.congr ?_
  intro s
  exact (P.edgePoint_coe_eq_lineMap i s).symm

/-- Helper for Proposition 74.1: the cyclic edge parameterization covers the boundary. -/
lemma edgePoint_surjective (P : CyclicPolygon n) :
    Function.Surjective (fun z : Fin n × unitInterval ↦ P.edgePoint z.1 z.2) := by
  -- Choose an edge containing the boundary point and then its affine segment parameter.
  intro x
  have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ P.boundary := x.property
  have hxUnion : (x : EuclideanSpace ℝ (Fin 2)) ∈ ⋃ i, P.edgeSet i :=
    Eq.mp (congrArg (fun S : Set (EuclideanSpace ℝ (Fin 2)) ↦ (x : EuclideanSpace ℝ (Fin 2)) ∈ S)
      P.boundary_def) hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxUnion
  rw [edgeSet_def] at hxi
  unfold Polygon.edgeSet at hxi
  rw [affineSegment_eq_segment, segment_eq_image_lineMap] at hxi
  obtain ⟨r, hr, hline⟩ := hxi
  let s : unitInterval := ⟨r, hr⟩
  refine ⟨(i, s), ?_⟩
  apply Subtype.ext
  rw [P.edgePoint_coe_eq_lineMap]
  exact hline

/-- Helper for Proposition 74.1: radial interpolation varies continuously in both its
boundary endpoint and affine parameter. -/
lemma continuous_radialPoint (P : CyclicPolygon n) (p : P.interior) :
    Continuous (fun z : P.boundary × unitInterval ↦ P.radialPoint p z.1 z.2) := by
  -- After coercing to the plane, this is the standard jointly continuous affine line map.
  rw [continuous_induced_rng]
  have hline : Continuous (fun z : P.boundary × unitInterval ↦
      AffineMap.lineMap (p : EuclideanSpace ℝ (Fin 2))
        (z.1 : EuclideanSpace ℝ (Fin 2)) (z.2 : ℝ)) :=
    continuous_const.lineMap (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)
  refine hline.congr ?_
  intro z
  exact (P.radialPoint_coe_eq_lineMap p z.1 z.2).symm

/-- Helper for Proposition 74.1: radial interpolation from an interior point covers the
filled polygonal region. -/
lemma radialPoint_surjective (P : CyclicPolygon n) (p : P.interior) :
    Function.Surjective (fun z : P.boundary × unitInterval ↦ P.radialPoint p z.1 z.2) := by
  -- Use the radial segment cover and choose the affine parameter on the selected segment.
  intro z
  have hz : (z : EuclideanSpace ℝ (Fin 2)) ∈ P.region := z.property
  have hzUnion : (z : EuclideanSpace ℝ (Fin 2)) ∈
      ⋃ q ∈ P.boundary,
        segment ℝ (p : EuclideanSpace ℝ (Fin 2)) q :=
    Eq.mp (congrArg (fun S : Set (EuclideanSpace ℝ (Fin 2)) ↦ (z : EuclideanSpace ℝ (Fin 2)) ∈ S)
      (P.region_eq_iUnion_segments p.property)) hz
  obtain ⟨q, hz⟩ := mem_iUnion.mp hzUnion
  obtain ⟨hq, hzsegment⟩ := mem_iUnion.mp hz
  rw [segment_eq_image_lineMap] at hzsegment
  obtain ⟨r, hr, hline⟩ := hzsegment
  let x : P.boundary := ⟨q, hq⟩
  let s : unitInterval := ⟨r, hr⟩
  refine ⟨(x, s), ?_⟩
  apply Subtype.ext
  rw [P.radialPoint_coe_eq_lineMap]
  exact hline

/-- Helper for Proposition 74.1: a cyclic reindexing preserves the complete edge-parameter
fiber relation. -/
lemma edgePoint_eq_map_iff (P Q : CyclicPolygon n) (e : Fin n ≃ Fin n)
    (he : Function.Commute e (finRotate n)) (i j : Fin n) (s t : unitInterval) :
    P.edgePoint i s = P.edgePoint j t ↔
      Q.edgePoint (e i) s = Q.edgePoint (e j) t := by
  -- Transport each of the three combinatorial fiber cases through the cyclic equivalence.
  rw [P.edgePoint_eq_iff, Q.edgePoint_eq_iff]
  constructor
  · rintro (⟨hij, hst⟩ | ⟨hs, ht, hij⟩ | ⟨hs, ht, hij⟩)
    · exact Or.inl ⟨congrArg e hij, hst⟩
    · exact Or.inr (Or.inl ⟨hs, ht, (congrArg e hij).trans (he j)⟩)
    · exact Or.inr (Or.inr ⟨hs, ht, (he i).symm.trans (congrArg e hij)⟩)
  · rintro (⟨hij, hst⟩ | ⟨hs, ht, hij⟩ | ⟨hs, ht, hij⟩)
    · exact Or.inl ⟨e.injective hij, hst⟩
    · exact Or.inr (Or.inl ⟨hs, ht, e.injective (hij.trans (he j).symm)⟩)
    · exact Or.inr (Or.inr ⟨hs, ht, e.injective ((he i).trans hij)⟩)

/-- Helper for Proposition 74.1: a boundary homeomorphism preserves the cone fiber
relation of radial parameterizations. -/
lemma radialPoint_eq_map_iff (P Q : CyclicPolygon n) (p : P.interior) (q : Q.interior)
    (h : P.boundary ≃ₜ Q.boundary) (x y : P.boundary) (s t : unitInterval) :
    P.radialPoint p x s = P.radialPoint p y t ↔
      Q.radialPoint q (h x) s = Q.radialPoint q (h y) t := by
  -- The center case is unchanged, while equality of boundary endpoints is reflected by `h`.
  rw [P.radialPoint_eq_iff, Q.radialPoint_eq_iff]
  exact or_congr Iff.rfl (and_congr h.injective.eq_iff.symm Iff.rfl)

/-- Helper for Proposition 74.1: the boundary of a cyclic polygon is compact. -/
lemma boundary_isCompact (P : CyclicPolygon n) : IsCompact (Set.univ : Set P.boundary) := by
  -- It is the continuous image of the compact finite family of unit intervals.
  have himage : Set.range (fun z : Fin n × unitInterval ↦ P.edgePoint z.1 z.2) = Set.univ :=
    Set.range_eq_univ.mpr P.edgePoint_surjective
  rw [← himage]
  simpa only [Set.image_univ] using isCompact_univ.image P.continuous_edgePoint

/-- Helper for Proposition 74.1: compatible compact quotient presentations induce a
homeomorphism carrying each presented point to its corresponding point. -/
lemma existsHomeomorphOfQuotientPresentations
    {X Y A B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B]
    (f : C(X, A)) (g : C(Y, B)) (hf : Topology.IsQuotientMap f)
    (hg : Topology.IsQuotientMap g) (e : X ≃ₜ Y)
    (hker : ∀ x x', f x = f x' ↔ g (e x) = g (e x')) :
    ∃ h : A ≃ₜ B, ∀ x, h (f x) = g (e x) := by
  -- Transport the kernel quotient along `e`, then identify both quotients with their targets.
  let hquot := Homeomorph.Quotient.congr (rX := Setoid.ker f) (rY := Setoid.ker g) e hker
  let h := hf.homeomorph.symm.trans (hquot.trans hg.homeomorph)
  refine ⟨h, ?_⟩
  intro x
  have hsource : hf.homeomorph.symm (f x) = Quotient.mk'' x := by
    apply hf.homeomorph.injective
    simp only [Homeomorph.apply_symm_apply]
    rfl
  dsimp only [h]
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, hsource]
  rfl

/-- A boundary homeomorphism agrees on each cyclic edge with the positive homeomorphism
between the equally indexed oriented segments. -/
def PreservesEdgeParameters (P Q : CyclicPolygon n)
    (h : P.boundary ≃ₜ Q.boundary) : Prop :=
  ∀ (i : Fin n) (s : unitInterval), h (P.edgePoint i s) = Q.edgePoint i s

/-- A parameter-preserving boundary homeomorphism carries the point with parameter `s`
on the `i`th edge to the point with the same parameter on the corresponding edge. -/
theorem PreservesEdgeParameters.map_edgePoint {P Q : CyclicPolygon n}
    {h : P.boundary ≃ₜ Q.boundary} (hh : PreservesEdgeParameters P Q h)
    (i : Fin n) (s : unitInterval) :
    h (P.edgePoint i s) = Q.edgePoint i s :=
  hh i s

/-- A boundary homeomorphism preserves affine edge parameters along a specified cyclic
reindexing of the vertices. -/
def PreservesEdgeParametersAlong (P Q : CyclicPolygon n) (e : Fin n ≃ Fin n)
    (h : P.boundary ≃ₜ Q.boundary) : Prop :=
  ∀ (i : Fin n) (s : unitInterval), h (P.edgePoint i s) = Q.edgePoint (e i) s

/-- Edge-parameter preservation along a cyclic reindexing maps each parameterized edge point
to the corresponding reindexed edge point. -/
theorem PreservesEdgeParametersAlong.map_edgePoint {P Q : CyclicPolygon n}
    {e : Fin n ≃ Fin n} {h : P.boundary ≃ₜ Q.boundary}
    (hh : PreservesEdgeParametersAlong P Q e h) (i : Fin n) (s : unitInterval) :
    h (P.edgePoint i s) = Q.edgePoint (e i) s :=
  hh i s

/-- A homeomorphism of filled cyclic polygons is the radial affine extension
of a specified boundary homeomorphism from chosen interior points. -/
def IsRadialExtension (P Q : CyclicPolygon n) (p : P.interior) (q : Q.interior)
    (h : P.boundary ≃ₜ Q.boundary) (H : P.region ≃ₜ Q.region) : Prop :=
  ∀ (x : P.boundary) (s : unitInterval),
    H (P.radialPoint p x s) = Q.radialPoint q (h x) s

/-- A radial extension carries the point with parameter `s` on the ray from `p` to `x`
to the point with the same parameter on the ray from `q` to `h x`. -/
theorem IsRadialExtension.map_radialPoint {P Q : CyclicPolygon n}
    {p : P.interior} {q : Q.interior} {h : P.boundary ≃ₜ Q.boundary}
    {H : P.region ≃ₜ Q.region} (hH : IsRadialExtension P Q p q h H)
    (x : P.boundary) (s : unitInterval) :
    H (P.radialPoint p x s) = Q.radialPoint q (h x) s :=
  hH x s

/-- Helper for Proposition 74.1: a cyclic reindexing produces the boundary homeomorphism
that preserves all corresponding affine edge parameters. -/
lemma existsBoundaryHomeomorphAlong (P Q : CyclicPolygon n) (e : Fin n ≃ Fin n)
    (he : Function.Commute e (finRotate n)) :
    ∃ h : P.boundary ≃ₜ Q.boundary, PreservesEdgeParametersAlong P Q e h := by
  -- Present each boundary as the compact quotient of its indexed unit intervals.
  let f : C(Fin n × unitInterval, P.boundary) :=
    ⟨fun z ↦ P.edgePoint z.1 z.2, P.continuous_edgePoint⟩
  let g : C(Fin n × unitInterval, Q.boundary) :=
    ⟨fun z ↦ Q.edgePoint z.1 z.2, Q.continuous_edgePoint⟩
  have hf : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous P.edgePoint_surjective
      P.continuous_edgePoint
  have hg : Topology.IsQuotientMap g :=
    Topology.IsQuotientMap.of_surjective_continuous Q.edgePoint_surjective
      Q.continuous_edgePoint
  let etop := (Homeomorph.ofDiscrete e).prodCongr (Homeomorph.refl unitInterval)
  have etop_apply (z : Fin n × unitInterval) : etop z = (e z.1, z.2) := rfl
  have hker : ∀ z z', f z = f z' ↔ g (etop z) = g (etop z') := by
    intro z z'
    dsimp only [f, g]
    rw [etop_apply, etop_apply]
    exact P.edgePoint_eq_map_iff Q e he z.1 z'.1 z.2 z'.2
  obtain ⟨h, hh⟩ := existsHomeomorphOfQuotientPresentations f g hf hg etop hker
  refine ⟨h, ?_⟩
  intro i s
  have hspec := hh (i, s)
  dsimp only [f, g, etop] at hspec
  exact hspec

/-- Helper for Proposition 74.1: every boundary homeomorphism extends radially between
chosen interior points. -/
lemma existsRadialExtension (P Q : CyclicPolygon n) (p : P.interior) (q : Q.interior)
    (h : P.boundary ≃ₜ Q.boundary) :
    ∃ H : P.region ≃ₜ Q.region, IsRadialExtension P Q p q h H := by
  -- Compactness turns the two radial parameterizations into quotient maps.
  letI : CompactSpace P.boundary := isCompact_univ_iff.mp P.boundary_isCompact
  letI : CompactSpace Q.boundary := isCompact_univ_iff.mp Q.boundary_isCompact
  let f : C(P.boundary × unitInterval, P.region) :=
    ⟨fun z ↦ P.radialPoint p z.1 z.2, P.continuous_radialPoint p⟩
  let g : C(Q.boundary × unitInterval, Q.region) :=
    ⟨fun z ↦ Q.radialPoint q z.1 z.2, Q.continuous_radialPoint q⟩
  have hf : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous (P.radialPoint_surjective p)
      (P.continuous_radialPoint p)
  have hg : Topology.IsQuotientMap g :=
    Topology.IsQuotientMap.of_surjective_continuous (Q.radialPoint_surjective q)
      (Q.continuous_radialPoint q)
  let etop := h.prodCongr (Homeomorph.refl unitInterval)
  have etop_apply (z : P.boundary × unitInterval) : etop z = (h z.1, z.2) := rfl
  have hker : ∀ z z', f z = f z' ↔ g (etop z) = g (etop z') := by
    intro z z'
    dsimp only [f, g]
    rw [etop_apply, etop_apply]
    exact P.radialPoint_eq_map_iff Q p q h z.1 z'.1 z.2 z'.2
  obtain ⟨H, hH⟩ := existsHomeomorphOfQuotientPresentations f g hf hg etop hker
  refine ⟨H, ?_⟩
  intro x s
  have hspec := hH (x, s)
  dsimp only [f, g, etop] at hspec
  exact hspec

/-- Proposition 74.1: Two cyclic polygonal regions with the same number of indexed vertices
have a boundary homeomorphism that maps each equally indexed edge positively and linearly;
for any chosen interior points, it has a radial affine extension. -/
theorem existsBoundaryHomeomorphWithRadialExtension (P Q : CyclicPolygon n) :
    ∃ h : P.boundary ≃ₜ Q.boundary, PreservesEdgeParameters P Q h ∧
      ∀ (p : P.interior) (q : Q.interior),
        ∃ H : P.region ≃ₜ Q.region, IsRadialExtension P Q p q h H := by
  -- Use the identity cyclic reindexing, then attach the radial quotient extension.
  obtain ⟨h, hh⟩ := existsBoundaryHomeomorphAlong P Q (Equiv.refl (Fin n))
    (fun _ ↦ rfl)
  refine ⟨h, ?_, ?_⟩
  · intro i s
    simpa using hh i s
  · intro p q
    exact existsRadialExtension P Q p q h

/-- Proposition 74.1 after a cyclic reindexing of the vertices: corresponding reindexed edges
are matched positively and linearly, and the boundary map has radial affine extensions. -/
theorem existsBoundaryHomeomorphWithRadialExtensionAlong (P Q : CyclicPolygon n)
    (e : Fin n ≃ Fin n) (he : Function.Commute e (finRotate n)) :
    ∃ h : P.boundary ≃ₜ Q.boundary, PreservesEdgeParametersAlong P Q e h ∧
      ∀ (p : P.interior) (q : Q.interior),
        ∃ H : P.region ≃ₜ Q.region, IsRadialExtension P Q p q h H := by
  -- Build the reindexed boundary map and use the same radial extension construction.
  obtain ⟨h, hh⟩ := existsBoundaryHomeomorphAlong P Q e he
  refine ⟨h, hh, ?_⟩
  intro p q
  exact existsRadialExtension P Q p q h

end

end CyclicPolygon
