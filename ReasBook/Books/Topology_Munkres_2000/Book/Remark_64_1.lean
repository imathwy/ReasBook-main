module

public import Topology_Munkres_2000.Book.Definition_64_1
public import Topology_Munkres_2000.Book.Definition_64_2.ThetaSpace
import all Topology_Munkres_2000.Book.Definition_64_2.ThetaSpace
public import Mathlib.Topology.Subpath

public section

open Set

universe u

namespace Topology.ThetaPresentation

variable {X : Type u} [TopologicalSpace X]

noncomputable section

/-- Companion for Remark 64.1: The intersection of two distinct edges of a theta presentation
is not a subsingleton, so the given three-edge presentation is not a finite linear graph. -/
theorem edge_inter_edge_not_subsingleton (P : Topology.ThetaPresentation X) {i j : Fin 3}
    (hij : i ≠ j) : ¬ (P.edge i ∩ P.edge j).Subsingleton := by
  -- The two distinct common endpoints both lie in the intersection.
  rw [P.edge_inter_edge i j hij]
  intro h
  apply P.endpoint_ne
  exact h (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Helper for Remark 64.1: the real midpoint lies in the closed unit interval. -/
private lemma unitIntervalMidpoint_mem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Both midpoint inequalities are elementary.
  constructor
  · norm_num
  · norm_num

/-- Helper for Remark 64.1: the midpoint of `unitInterval`. -/
private def unitIntervalMidpoint : unitInterval :=
  ⟨1 / 2, unitIntervalMidpoint_mem⟩

/-- Helper for Remark 64.1: the unit-interval midpoint is not zero. -/
private lemma unitIntervalMidpoint_ne_zero : unitIntervalMidpoint ≠ 0 := by
  -- Equality would force the real numbers `1 / 2` and `0` to coincide.
  intro h
  have hval := congrArg Subtype.val h
  norm_num [unitIntervalMidpoint] at hval

/-- Helper for Remark 64.1: the unit-interval midpoint is not one. -/
private lemma unitIntervalMidpoint_ne_one : unitIntervalMidpoint ≠ 1 := by
  -- Equality would force the real numbers `1 / 2` and `1` to coincide.
  intro h
  have hval := congrArg Subtype.val h
  norm_num [unitIntervalMidpoint] at hval

/-- Helper for Remark 64.1: the full closed interval in `unitInterval` is universal. -/
private lemma unitInterval_Icc_zero_one :
    Set.Icc (0 : unitInterval) 1 = Set.univ := by
  -- Every point of the subtype already satisfies the defining endpoint bounds.
  apply Set.eq_univ_of_forall
  intro t
  exact ⟨unitInterval.nonneg t, unitInterval.le_one t⟩

/-- Helper for Remark 64.1: the initial parameter of a lower or upper half-edge. -/
private def subdivisionStart : Fin 2 → unitInterval :=
  fun k ↦ if k = 0 then 0 else unitIntervalMidpoint

/-- Helper for Remark 64.1: the terminal parameter of a lower or upper half-edge. -/
private def subdivisionEnd : Fin 2 → unitInterval :=
  fun k ↦ if k = 0 then unitIntervalMidpoint else 1

/-- Helper for Remark 64.1: the affine parameterization of a half of `unitInterval`. -/
private def subdivisionParam (k : Fin 2) : unitInterval → unitInterval :=
  Set.Icc.convexComb (subdivisionStart k) (subdivisionEnd k)

/-- Helper for Remark 64.1: a half-edge obtained by subdividing one theta arc. -/
private def subdivisionEdge (P : Topology.ThetaPresentation X) (q : Fin 3 × Fin 2) :
    unitInterval → X :=
  P.arc q.1 ∘ subdivisionParam q.2

/-- Helper for Remark 64.1: every index in `Fin 2` is zero or one. -/
private lemma finTwo_eq_zero_or_one (k : Fin 2) : k = 0 ∨ k = 1 := by
  -- The bound on the underlying natural number leaves exactly two cases.
  omega

/-- Helper for Remark 64.1: the two canonical indices in `Fin 2` are distinct. -/
private lemma finTwo_one_ne_zero : (1 : Fin 2) ≠ 0 := by
  -- Their underlying natural numbers are distinct.
  decide

/-- Helper for Remark 64.1: each affine half-interval parameterization is an embedding. -/
private lemma subdivisionParam_isEmbedding (k : Fin 2) :
    Topology.IsEmbedding (subdivisionParam k) := by
  -- Compact-to-Hausdorff embedding reduces the claim to affine injectivity.
  unfold subdivisionParam
  refine ((Set.Icc.continuous_convexComb (subdivisionStart k)
    (subdivisionEnd k)).isClosedEmbedding ?_).isEmbedding
  intro s t hst
  apply Subtype.ext
  have hval := congrArg Subtype.val hst
  rcases finTwo_eq_zero_or_one k with rfl | rfl
  · simp only [subdivisionStart, subdivisionEnd,
      unitIntervalMidpoint, Set.Icc.coe_convexComb] at hval
    norm_num at hval ⊢
    linarith
  · simp only [subdivisionStart, subdivisionEnd,
      unitIntervalMidpoint, Set.Icc.coe_convexComb] at hval
    norm_num at hval ⊢
    linarith

/-- Helper for Remark 64.1: each subdivided theta edge is embedded. -/
private lemma subdivisionEdge_isEmbedding (P : Topology.ThetaPresentation X)
    (q : Fin 3 × Fin 2) : Topology.IsEmbedding (subdivisionEdge P q) := by
  -- Compose the affine half-interval embedding with the stored theta-arc embedding.
  exact (P.isEmbedding q.1).comp (subdivisionParam_isEmbedding q.2)

/-- Helper for Remark 64.1: the lower and upper parameter intervals are ordered. -/
private lemma subdivisionStart_le_end (k : Fin 2) :
    subdivisionStart k ≤ subdivisionEnd k := by
  -- There are only the intervals `[0, 1/2]` and `[1/2, 1]`.
  rcases finTwo_eq_zero_or_one k with rfl | rfl
  · exact unitIntervalMidpoint.property.1
  · exact unitIntervalMidpoint.property.2

/-- Helper for Remark 64.1: a half-edge range is the image of its parameter interval. -/
private lemma subdivisionEdge_range (P : Topology.ThetaPresentation X) (i : Fin 3)
    (k : Fin 2) :
    Set.range (subdivisionEdge P (i, k)) =
      P.arc i '' Set.Icc (subdivisionStart k) (subdivisionEnd k) := by
  -- First expose the composite range, then use the affine interval range theorem.
  unfold subdivisionEdge
  rw [Set.range_comp]
  unfold subdivisionParam
  rw [Path.range_subpathAux, Set.uIcc_of_le (subdivisionStart_le_end k)]

/-- Helper for Remark 64.1: the endpoints of a subdivided edge are its interval ends. -/
private lemma subdivisionEdge_zero (P : Topology.ThetaPresentation X) (i : Fin 3)
    (k : Fin 2) :
    subdivisionEdge P (i, k) 0 = P.arc i (subdivisionStart k) := by
  -- Convex combination at parameter zero selects the first interval endpoint.
  simpa only [subdivisionEdge, Function.comp_apply, subdivisionParam] using
    congrArg (P.arc i) (Set.Icc.convexComb_zero (subdivisionStart k) (subdivisionEnd k))

/-- Helper for Remark 64.1: the terminal endpoint of a subdivided edge is its interval end. -/
private lemma subdivisionEdge_one (P : Topology.ThetaPresentation X) (i : Fin 3)
    (k : Fin 2) :
    subdivisionEdge P (i, k) 1 = P.arc i (subdivisionEnd k) := by
  -- Convex combination at parameter one selects the second interval endpoint.
  simpa only [subdivisionEdge, Function.comp_apply, subdivisionParam] using
    congrArg (P.arc i) (Set.Icc.convexComb_one (subdivisionStart k) (subdivisionEnd k))

/-- Helper for Remark 64.1: every subdivided edge lies in its original theta edge. -/
private lemma subdivisionEdge_range_subset_edge (P : Topology.ThetaPresentation X)
    (i : Fin 3) (k : Fin 2) :
    Set.range (subdivisionEdge P (i, k)) ⊆ P.edge i := by
  -- Forgetting the restricted parameter leaves a point in the full arc range.
  intro x hx
  obtain ⟨t, ht⟩ := hx
  have hxedge : x ∈ Set.range (P.arc i) := ⟨subdivisionParam k t, ht⟩
  exact hxedge

/-- Helper for Remark 64.1: the two halves of one theta arc meet exactly at its midpoint. -/
private lemma subdivisionEdge_halves_inter (P : Topology.ThetaPresentation X) (i : Fin 3) :
    Set.range (subdivisionEdge P (i, 0)) ∩ Set.range (subdivisionEdge P (i, 1)) =
      {P.arc i unitIntervalMidpoint} := by
  -- Injectivity transports the interval intersection through the original arc.
  rw [subdivisionEdge_range, subdivisionEdge_range]
  rw [← Set.image_inter (P.isEmbedding i).injective]
  simp only [subdivisionStart, subdivisionEnd, if_pos, finTwo_one_ne_zero, if_false]
  rw [Set.Icc_inter_Icc_eq_singleton]
  · exact Set.image_singleton
  · exact unitIntervalMidpoint.property.1
  · exact unitIntervalMidpoint.property.2

/-- Helper for Remark 64.1: a half-edge meeting an original endpoint meets its outer endpoint. -/
private lemma subdivisionEdge_originalEndpoint_eq (P : Topology.ThetaPresentation X)
    (i : Fin 3) (k : Fin 2) {x : X} (hx : x ∈ Set.range (subdivisionEdge P (i, k)))
    (hend : x ∈ ({P.initial, P.terminal} : Set X)) :
    x = if k = 0 then P.initial else P.terminal := by
  -- Arc injectivity excludes the far endpoint from either half interval.
  rw [subdivisionEdge_range] at hx
  obtain ⟨t, ht, htx⟩ := hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hend
  rcases hend with hinit | hterminal
  · rcases finTwo_eq_zero_or_one k with rfl | rfl
    · simpa using hinit
    · have ht0 : t = 0 := by
        apply (P.isEmbedding i).injective
        rw [P.map_zero]
        exact htx.trans hinit
      subst t
      have hle : unitIntervalMidpoint ≤ 0 := by
        simpa only [subdivisionStart, finTwo_one_ne_zero, if_false] using ht.1
      have hmid : unitIntervalMidpoint = 0 :=
        le_antisymm hle (unitInterval.nonneg unitIntervalMidpoint)
      exact (unitIntervalMidpoint_ne_zero hmid).elim
  · rcases finTwo_eq_zero_or_one k with rfl | rfl
    · have ht1 : t = 1 := by
        apply (P.isEmbedding i).injective
        rw [P.map_one]
        exact htx.trans hterminal
      subst t
      have hle : (1 : unitInterval) ≤ unitIntervalMidpoint := by
        simpa only [subdivisionEnd, if_pos] using ht.2
      have hmid : unitIntervalMidpoint = 1 :=
        le_antisymm unitIntervalMidpoint.property.2 hle
      exact (unitIntervalMidpoint_ne_one hmid).elim
    · simpa using hterminal

/-- Helper for Remark 64.1: an original endpoint on a half-edge is one of its own endpoints. -/
private lemma subdivisionEdge_originalEndpoint_mem_endpointPair
    (P : Topology.ThetaPresentation X) (i : Fin 3) (k : Fin 2) {x : X}
    (hx : x ∈ Set.range (subdivisionEdge P (i, k)))
    (hend : x ∈ ({P.initial, P.terminal} : Set X)) :
    x ∈ ({subdivisionEdge P (i, k) 0, subdivisionEdge P (i, k) 1} : Set X) := by
  -- The preceding classification identifies the appropriate outer endpoint.
  have hxouter := subdivisionEdge_originalEndpoint_eq P i k hx hend
  rcases finTwo_eq_zero_or_one k with rfl | rfl
  · simp only [if_pos] at hxouter
    rw [hxouter, subdivisionEdge_zero]
    simp only [subdivisionStart, if_pos, P.map_zero, Set.mem_insert_iff, true_or]
  · simp only [finTwo_one_ne_zero, if_false] at hxouter
    rw [hxouter, subdivisionEdge_one]
    simp only [subdivisionEnd, finTwo_one_ne_zero, if_false, P.map_one,
      Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

/-- Helper for Remark 64.1: the six half-edges cover the theta space. -/
private lemma subdivisionEdge_iUnion_range (P : Topology.ThetaPresentation X) :
    ⋃ q : Fin 3 × Fin 2, Set.range (subdivisionEdge P q) = Set.univ := by
  -- Choose the lower or upper half according to the original arc parameter.
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ i, P.edge i := by
    rw [P.iUnion_edge]
    exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hi' : x ∈ Set.range (P.arc i) := hi
  obtain ⟨t, rfl⟩ := hi'
  rcases le_total t unitIntervalMidpoint with ht | ht
  · apply Set.mem_iUnion.mpr
    refine ⟨(i, 0), ?_⟩
    rw [subdivisionEdge_range]
    refine ⟨t, ?_, rfl⟩
    have htIcc : t ∈ Set.Icc (0 : unitInterval) unitIntervalMidpoint :=
      ⟨unitInterval.nonneg t, ht⟩
    simpa only [subdivisionStart, subdivisionEnd, if_pos] using htIcc
  · apply Set.mem_iUnion.mpr
    refine ⟨(i, 1), ?_⟩
    rw [subdivisionEdge_range]
    refine ⟨t, ?_, rfl⟩
    have htIcc : t ∈ Set.Icc unitIntervalMidpoint (1 : unitInterval) :=
      ⟨ht, unitInterval.le_one t⟩
    simpa only [subdivisionStart, subdivisionEnd, finTwo_one_ne_zero, if_false] using htIcc

/-- Helper for Remark 64.1: distinct half-edges meet only at endpoints of both. -/
private lemma subdivisionEdge_inter_subset_endpoints (P : Topology.ThetaPresentation X)
    {q r : Fin 3 × Fin 2} (hqr : q ≠ r) :
    Set.range (subdivisionEdge P q) ∩ Set.range (subdivisionEdge P r) ⊆
      ({subdivisionEdge P q 0, subdivisionEdge P q 1} ∩
        {subdivisionEdge P r 0, subdivisionEdge P r 1} : Set X) := by
  -- Separate halves of one arc from halves belonging to distinct original arcs.
  rintro x ⟨hxq, hxr⟩
  rcases q with ⟨i, k⟩
  rcases r with ⟨j, l⟩
  by_cases hij : i = j
  · subst j
    have hkl : k ≠ l := by
      intro h
      exact hqr (Prod.ext rfl h)
    rcases finTwo_eq_zero_or_one k with rfl | rfl
    · rcases finTwo_eq_zero_or_one l with rfl | rfl
      · exact (hkl rfl).elim
      · have hxmid : x = P.arc i unitIntervalMidpoint := by
          have hx : x ∈ Set.range (subdivisionEdge P (i, 0)) ∩
              Set.range (subdivisionEdge P (i, 1)) := ⟨hxq, hxr⟩
          rw [subdivisionEdge_halves_inter P i] at hx
          exact Set.mem_singleton_iff.mp hx
        subst x
        constructor
        · rw [subdivisionEdge_one]
          simp only [subdivisionEnd, if_pos]
          exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
        · rw [subdivisionEdge_zero]
          simp only [subdivisionStart, finTwo_one_ne_zero, if_false]
          exact Set.mem_insert _ _
    · rcases finTwo_eq_zero_or_one l with rfl | rfl
      · have hxmid : x = P.arc i unitIntervalMidpoint := by
          have hx : x ∈ Set.range (subdivisionEdge P (i, 0)) ∩
              Set.range (subdivisionEdge P (i, 1)) := ⟨hxr, hxq⟩
          rw [subdivisionEdge_halves_inter P i] at hx
          exact Set.mem_singleton_iff.mp hx
        subst x
        constructor
        · rw [subdivisionEdge_zero]
          simp only [subdivisionStart, finTwo_one_ne_zero, if_false]
          exact Set.mem_insert _ _
        · rw [subdivisionEdge_one]
          simp only [subdivisionEnd, if_pos]
          exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · exact (hkl rfl).elim
  · have hxedge : x ∈ P.edge i ∩ P.edge j :=
      ⟨subdivisionEdge_range_subset_edge P i k hxq,
        subdivisionEdge_range_subset_edge P j l hxr⟩
    rw [P.edge_inter_edge i j hij] at hxedge
    exact ⟨subdivisionEdge_originalEndpoint_mem_endpointPair P i k hxq hxedge,
      subdivisionEdge_originalEndpoint_mem_endpointPair P j l hxr hxedge⟩

/-- Helper for Remark 64.1: the intersection of distinct half-edges is a subsingleton. -/
private lemma subdivisionEdge_inter_subsingleton (P : Topology.ThetaPresentation X)
    {q r : Fin 3 × Fin 2} (hqr : q ≠ r) :
    (Set.range (subdivisionEdge P q) ∩ Set.range (subdivisionEdge P r)).Subsingleton := by
  -- On one arc the common point is the midpoint; on different arcs the first half fixes it.
  intro x hx y hy
  rcases q with ⟨i, k⟩
  rcases r with ⟨j, l⟩
  by_cases hij : i = j
  · subst j
    have hkl : k ≠ l := by
      intro h
      exact hqr (Prod.ext rfl h)
    rcases finTwo_eq_zero_or_one k with rfl | rfl
    · rcases finTwo_eq_zero_or_one l with rfl | rfl
      · exact (hkl rfl).elim
      · rw [subdivisionEdge_halves_inter P i] at hx hy
        exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
    · rcases finTwo_eq_zero_or_one l with rfl | rfl
      · have hx' : x ∈ Set.range (subdivisionEdge P (i, 0)) ∩
            Set.range (subdivisionEdge P (i, 1)) := ⟨hx.2, hx.1⟩
        have hy' : y ∈ Set.range (subdivisionEdge P (i, 0)) ∩
            Set.range (subdivisionEdge P (i, 1)) := ⟨hy.2, hy.1⟩
        rw [subdivisionEdge_halves_inter P i] at hx' hy'
        exact (Set.mem_singleton_iff.mp hx').trans (Set.mem_singleton_iff.mp hy').symm
      · exact (hkl rfl).elim
  · have hxedge : x ∈ P.edge i ∩ P.edge j :=
      ⟨subdivisionEdge_range_subset_edge P i k hx.1,
        subdivisionEdge_range_subset_edge P j l hx.2⟩
    have hyedge : y ∈ P.edge i ∩ P.edge j :=
      ⟨subdivisionEdge_range_subset_edge P i k hy.1,
        subdivisionEdge_range_subset_edge P j l hy.2⟩
    rw [P.edge_inter_edge i j hij] at hxedge hyedge
    calc
      x = if k = 0 then P.initial else P.terminal :=
        subdivisionEdge_originalEndpoint_eq P i k hx.1 hxedge
      _ = y := (subdivisionEdge_originalEndpoint_eq P i k hy.1 hyedge).symm

/-- Helper for Remark 64.1: the canonical six-edge subdivision graph. -/
private def linearSubdivision [T2Space X] (P : Topology.ThetaPresentation X) :
    FiniteLinearGraph.{u, 0} X :=
  { t2Space := inferInstance
    Edge := Fin 3 × Fin 2
    edgeFinite := inferInstance
    edge := subdivisionEdge P
    edgeEmbedding := subdivisionEdge_isEmbedding P
    iUnion_range := subdivisionEdge_iUnion_range P
    interSubsetEndpoints := subdivisionEdge_inter_subset_endpoints P
    interSubsingleton := subdivisionEdge_inter_subsingleton P }

/-- Helper for Remark 64.1: the constructed graph stores the canonical half-edge map. -/
private lemma linearSubdivision_edge [T2Space X] (P : Topology.ThetaPresentation X)
    (q : Fin 3 × Fin 2) :
    (linearSubdivision P).edge q = subdivisionEdge P q := by
  -- This is the edge projection of the graph construction.
  rfl

/-- Helper for Remark 64.1: the two constructed half-edge sets recover one theta edge. -/
private lemma linearSubdivision_edge_union [T2Space X] (P : Topology.ThetaPresentation X)
    (i : Fin 3) :
    P.edge i = (linearSubdivision P).edgeSet (i, 0) ∪
      (linearSubdivision P).edgeSet (i, 1) := by
  -- Union the two normalized parameter intervals and recover the full arc range.
  rw [FiniteLinearGraph.edgeSet_def, FiniteLinearGraph.edgeSet_def]
  rw [linearSubdivision_edge, linearSubdivision_edge]
  rw [subdivisionEdge_range, subdivisionEdge_range]
  rw [← Set.image_union]
  simp only [subdivisionStart, subdivisionEnd, if_pos, finTwo_one_ne_zero, if_false]
  rw [Set.Icc_union_Icc_eq_Icc]
  · rw [unitInterval_Icc_zero_one, Set.image_univ]
    rfl
  · exact unitIntervalMidpoint.property.1
  · exact unitIntervalMidpoint.property.2

/-- Helper for Remark 64.1: the two constructed half-edge sets meet at the midpoint. -/
private lemma linearSubdivision_halves_inter [T2Space X]
    (P : Topology.ThetaPresentation X) (i : Fin 3) :
    (linearSubdivision P).edgeSet (i, 0) ∩ (linearSubdivision P).edgeSet (i, 1) =
      {P.arc i unitIntervalMidpoint} := by
  -- The graph accessor reduces to the already normalized half-edge intersection.
  rw [FiniteLinearGraph.edgeSet_def, FiniteLinearGraph.edgeSet_def]
  rw [linearSubdivision_edge, linearSubdivision_edge]
  exact subdivisionEdge_halves_inter P i

/-- Remark 64.1 (2): Each edge of a theta presentation can be subdivided into two edges
of a six-edge finite linear graph, with the two resulting edges meeting at one point. -/
theorem exists_linearSubdivision [T2Space X] (P : Topology.ThetaPresentation X) :
    ∃ (G : FiniteLinearGraph.{u, 0} X) (e : G.Edge ≃ Fin 3 × Fin 2),
      ∀ i : Fin 3, ∃ x : X,
        P.edge i = G.edgeSet (e.symm (i, 0)) ∪ G.edgeSet (e.symm (i, 1)) ∧
          G.edgeSet (e.symm (i, 0)) ∩ G.edgeSet (e.symm (i, 1)) = {x} := by
  -- Use the canonical six-edge graph and expose only its two subdivision specifications.
  refine ⟨linearSubdivision P, Equiv.refl _, ?_⟩
  intro i
  refine ⟨P.arc i unitIntervalMidpoint, linearSubdivision_edge_union P i,
    linearSubdivision_halves_inter P i⟩

end

end Topology.ThetaPresentation

namespace Topology.IsThetaSpace

variable {X : Type u} [TopologicalSpace X] [Topology.IsThetaSpace X]

/-- Every theta space admits some finite linear graph presentation. -/
theorem nonempty_finiteLinearGraph : Nonempty (FiniteLinearGraph.{u, 0} X) := by
  -- Choose a theta presentation and retain the graph supplied by its canonical subdivision.
  obtain ⟨P⟩ := Topology.IsThetaSpace.presentation (X := X)
  obtain ⟨G, _, _⟩ := P.exists_linearSubdivision
  exact ⟨G⟩

end Topology.IsThetaSpace
