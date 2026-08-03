import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19

noncomputable section

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Theorem_4_23

universe u

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- Helper for Theorem 4.23: evaluating a finite weighted sum of edge-vectors at one edge turns
the functional convex-combination identity into an ordinary scalar identity. -/
private lemma weightedSumApply {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → G.edgeSet → ℝ)
    {x : G.edgeSet → ℝ} (hx : ∑ i, w i • z i = x) (e : G.edgeSet) :
    ∑ i, w i * z i e = x e := by
  -- Apply the vector identity at a single edge coordinate.
  simpa [Pi.smul_apply, smul_eq_mul] using congrFun hx e

/-- Helper for Theorem 4.23: incidence vectors of subgraphs have nonnegative edge coordinates. -/
private lemma subgraphIncidenceVectorNonneg (M : G.Subgraph) :
    ∀ e : G.edgeSet, 0 ≤ G.subgraphIncidenceVector ℝ M e := by
  intro e
  -- Each edge coordinate is the `0/1` indicator of membership in `M.edgeSet`.
  by_cases h : e.1 ∈ M.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, h]
  · simp [SimpleGraph.subgraphIncidenceVector, h]

/-- Helper for Theorem 4.23: if a vertex is not covered by a subgraph, then its incidence sum in
the subgraph incidence vector is `0`. -/
private lemma subgraphIncidenceSumEqZeroOfNotMemVerts {M : G.Subgraph} {v : V}
    (hv : v ∉ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 0 := by
  -- Any incident edge with positive coordinate would force `v` into the support subgraph.
  refine Finset.sum_eq_zero ?_
  intro e he
  have hv_mem : v ∈ (e : Sym2 V) := by
    have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using he_inc
  by_cases heM : e.1 ∈ M.edgeSet
  · exact (hv (Subgraph.mem_verts_of_mem_edge heM hv_mem)).elim
  · simp [SimpleGraph.subgraphIncidenceVector, heM]

/-- Helper for Theorem 4.23: at a covered vertex of a matching, the matching incidence sum is
exactly `1`. -/
private lemma matchingIncidenceSumEqOneOfMemVerts {M : G.Subgraph} (hM : M.IsMatching)
    {v : V} (hv : v ∈ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  obtain ⟨w, hvw, huniq⟩ := hM hv
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have he₀_mem :
      e₀ ∈ Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
    -- The unique matching edge at `v` lies in the incidence filter at `v`.
    simp [e₀, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have he₀_val : G.subgraphIncidenceVector ℝ M e₀ = 1 := by
    have he₀_edge : e₀.1 ∈ M.edgeSet := Subgraph.mem_edgeSet.2 hvw
    simp [SimpleGraph.subgraphIncidenceVector, he₀_edge]
  calc
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = G.subgraphIncidenceVector ℝ M e₀ := by
          refine Finset.sum_eq_single_of_mem e₀ he₀_mem ?_
          intro e he he_ne
          by_cases heM : e.1 ∈ M.edgeSet
          · have hv_e : v ∈ (e : Sym2 V) := by
              have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
              simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
                using he_inc
            have hAdj_e : M.Adj v (Sym2.Mem.other hv_e) := by
              exact Subgraph.mem_edgeSet.1 (by simpa [Sym2.other_spec hv_e] using heM)
            have he_eq : e.1 = e₀.1 := by
              calc
                e.1 = s(v, Sym2.Mem.other hv_e) := by
                  symm
                  exact Sym2.other_spec hv_e
                _ = s(v, w) := by rw [huniq _ hAdj_e]
                _ = e₀.1 := rfl
            exact (he_ne (Subtype.ext he_eq)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
    _ = 1 := he₀_val

/-- Helper for Theorem 4.23: every matching incidence sum at a vertex is bounded by `1`. -/
private lemma matchingIncidenceSumLeOne {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
  -- A matching contributes `1` on covered vertices and `0` on uncovered vertices.
  by_cases hv : v ∈ M.verts
  · have hsum_eq_one := matchingIncidenceSumEqOneOfMemVerts (G := G) hM hv
    linarith
  · rw [subgraphIncidenceSumEqZeroOfNotMemVerts (G := G) hv]
    norm_num

/-- Helper for Theorem 4.23: a perfect matching contributes exactly one incident edge at every
vertex. -/
private lemma perfectMatchingIncidenceSumEqOne {M : G.Subgraph} (hM : M.IsPerfectMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  -- Perfect matchings are matchings that cover every vertex.
  simpa using matchingIncidenceSumEqOneOfMemVerts (G := G) hM.1 (hM.2 v)

/-- Helper for Theorem 4.23: every odd cut contains at least one edge of a perfect matching. -/
private lemma perfectMatchingCutLowerBound {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {S : Set V} (hS : Odd S.ncard) :
    1 ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
  classical
  by_contra hcut
  have hcut_lt : (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) < 1 := by
    linarith
  have hno_cut :
      ∀ {e : G.edgeSet}, e.1 ∈ M.edgeSet → e ∉ δ[G] S := by
    intro e heM heCut
    -- A cut edge of the perfect matching already forces the cut sum to be at least `1`.
    have hsum_ge :
        1 ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
      calc
        1 = G.subgraphIncidenceVector ℝ M e := by
              simp [SimpleGraph.subgraphIncidenceVector, heM]
        _ ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
              exact Finset.single_le_sum
                (fun e' _ ↦ subgraphIncidenceVectorNonneg (G := G) M e') heCut
    linarith
  have hinduced_match : (M.induce S).IsMatching := by
    intro v hv
    have hvS : v ∈ S := by
      simpa [Subgraph.induce_verts, hM.2.verts_eq_univ] using hv
    obtain ⟨w, hvw, huniq⟩ := (Subgraph.isPerfectMatching_iff.mp hM) v
    have hwS : w ∈ S := by
      by_contra hwS
      let e : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
      have heCut : e ∈ δ[G] S := by
        exact (SimpleGraph.mem_cutEdgeFinset_iff (G := G)).2 ⟨v, hvS, w, hwS, rfl⟩
      have heM : e.1 ∈ M.edgeSet := Subgraph.mem_edgeSet.2 hvw
      exact hno_cut heM heCut
    -- Once no matching edge crosses the cut, the matched neighbor stays inside `S`.
    refine ⟨w, ?_, ?_⟩
    · exact ⟨hvS, hwS, hvw⟩
    · intro x hx
      exact huniq x hx.2.2
  letI : Fintype ↑((M.induce S).verts) := Fintype.ofFinite _
  have hEven : Even S.ncard := by
    -- The induced matching covers exactly the odd-set vertices, so the odd set has even size.
    simpa [Subgraph.induce_verts, hM.2.verts_eq_univ, Set.inter_univ,
      Set.ncard_eq_toFinset_card'] using hinduced_match.even_card
  exact (Nat.not_even_iff_odd.mpr hS) hEven

/-- Helper for Theorem 4.23: every perfect-matching incidence vector satisfies the Chapter 4.19
constraint system. -/
private lemma subgraphIncidenceVector_mem_perfectMatchingConstraintSet {M : G.Subgraph}
    (hM : M.IsPerfectMatching) :
    G.subgraphIncidenceVector ℝ M ∈ perfectMatchingConstraintSet G := by
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact subgraphIncidenceVectorNonneg (G := G) M
  · intro v
    -- Perfect matchings contribute one incident edge at each vertex.
    exact perfectMatchingIncidenceSumEqOne (G := G) hM v
  · intro S hS
    -- Every odd cut of a perfect matching is hit by at least one matching edge.
    exact perfectMatchingCutLowerBound (G := G) hM hS

/-- Helper for Theorem 4.23: the edges with at least one endpoint in a finite set `S`, viewed as
edge coordinates of `G`. -/
private def oddSetIncidentEdgeFinset (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter fun e : G.edgeSet ↦ ∃ v ∈ S, (e : Sym2 V) ∈ G.incidenceFinset v

/-- Helper for Theorem 4.23: summing over `G.edgeSet` with an indicator `if` rewrites to the
corresponding filtered edge sum. -/
private lemma edgeSetSumIteEqSumFilter
    (p : G.edgeSet → Prop) [DecidablePred p] (f : G.edgeSet → ℝ) :
    (∑ e : G.edgeSet, if p e then f e else 0) = (Finset.univ.filter p).sum f := by
  -- This is the edge-coordinate form of `Finset.sum_filter`.
  rw [Finset.sum_filter]

/-- Helper for Theorem 4.23: the endpoint finset of an edge-coordinate is its unordered pair of
canonical `Sym2.out` endpoints. -/
private lemma edgeToFinsetEqPairFinset (e : G.edgeSet) :
    ((e : Sym2 V).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the edge through its canonical `Sym2.out` endpoints.
  calc
    ((e : Sym2 V).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Theorem 4.23: filtering `{a, b}` by membership in `S` has size `2`, `1`, or `0`
according as both, one, or neither endpoint lies in `S`. -/
private lemma pairFilterCardOfNeFinset
    (a b : V) (hab : a ≠ b) (S : Finset V) :
    (((({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) =
      if a ∈ (S : Set V) ∧ b ∈ (S : Set V) then 2
      else if a ∈ (S : Set V) ∨ b ∈ (S : Set V) then 1 else 0 := by
  -- Split into the four endpoint-membership cases and let `simp` normalize the filtered pair.
  by_cases ha : a ∈ (S : Set V)
  · by_cases hb : b ∈ (S : Set V)
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({a, b} : Finset V) := by
          ext v
          constructor
          · intro hv
            simpa using (Finset.mem_filter.mp hv).1
          · intro hv
            refine Finset.mem_filter.mpr ⟨hv, ?_⟩
            rcases Finset.mem_insert.mp hv with rfl | hvb
            · simpa using ha
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              simpa using hb
      rw [hfilter]
      simp [ha, hb, hab]
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({a} : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp hvpair with rfl | hvb
            · rfl
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              exact (hb (by simpa using hvS)).elim
          · intro hv
            have hv' : v = a := by simpa using hv
            subst hv'
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · simp
            · simpa using ha
      rw [hfilter]
      simp [ha, hb]
  · by_cases hb : b ∈ (S : Set V)
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({b} : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp hvpair with hva | hvb
            · subst hva
              exact (ha (by simpa using hvS)).elim
            · simpa using hvb
          · intro hv
            have hv' : v = b := by simpa using hv
            subst hv'
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · simp [hab]
            · simpa using hb
      rw [hfilter]
      simp [ha, hb]
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = (∅ : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rcases Finset.mem_insert.mp hvpair with hva | hvb
            · subst hva
              exact (ha (by simpa using hvS)).elim
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              exact (hb (by simpa using hvS)).elim
          · intro hv
            simpa using hv
      rw [hfilter]
      simp [ha, hb]

/-- Helper for Theorem 4.23: an induced edge is characterized by both canonical endpoints lying
in the chosen vertex set. -/
private lemma memInducedEdgeFinsetEndpointsIff
    (S : Set V) (e : G.edgeSet) :
    e ∈ E[G] S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  -- Rewrite induced-edge membership through the canonical endpoint presentation of `e`.
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Theorem 4.23: a cut edge is characterized by its canonical endpoints lying on
opposite sides of the chosen vertex set. -/
private lemma memCutEdgeFinsetEndpointsIff
    (S : Set V) (e : G.edgeSet) :
    e ∈ δ[G] S ↔
      (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) := by
  constructor
  · intro he
    rcases (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).1 he with ⟨u, hu, v, hv, huv⟩
    -- Normalize the witness edge equality to the canonical endpoints of `e`.
    rw [← e.1.out_eq] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).2
        ⟨e.1.out.1, h₁, e.1.out.2, h₂, e.1.out_eq⟩
    · exact (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).2
        ⟨e.1.out.2, h₁, e.1.out.1, h₂, Sym2.eq_swap.trans e.1.out_eq⟩

/-- Helper for Theorem 4.23: an induced edge cannot simultaneously lie in the cut of the same
vertex set. -/
private lemma notMemCutEdgeFinsetOfMemInducedEdgeFinset
    {S : Set V} {e : G.edgeSet} (he : e ∈ E[G] S) :
    e ∉ δ[G] S := by
  rcases (memInducedEdgeFinsetEndpointsIff (G := G) S e).1 he with ⟨h₁, h₂⟩
  intro hcut
  rcases (memCutEdgeFinsetEndpointsIff (G := G) S e).1 hcut with
    (⟨_, h₂'⟩ | ⟨_, h₁'⟩)
  · exact h₂' h₂
  · exact h₁' h₁

/-- Helper for Theorem 4.23: an edge belongs to `oddSetIncidentEdgeFinset S` exactly when one of
its two canonical endpoints lies in `S`. -/
private lemma memOddSetIncidentEdgeFinsetIff
    (S : Finset V) (e : G.edgeSet) :
    e ∈ oddSetIncidentEdgeFinset (G := G) S ↔
      e.1.out.1 ∈ (S : Set V) ∨ e.1.out.2 ∈ (S : Set V) := by
  rw [oddSetIncidentEdgeFinset, Finset.mem_filter]
  constructor
  · rintro ⟨_, v, hvS, hvInc⟩
    have hvMem : v ∈ (e : Sym2 V) := by
      exact
        (G.edge_mem_incidenceSet_iff (a := v) (e := e)).1
          ((G.mem_incidenceFinset (v := v) (e := (e : Sym2 V))).1 hvInc)
    rw [← e.1.out_eq] at hvMem
    rw [Sym2.mem_iff] at hvMem
    rcases hvMem with rfl | rfl
    · exact Or.inl (by simpa using hvS)
    · exact Or.inr (by simpa using hvS)
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases h with h₁ | h₂
    · refine ⟨e.1.out.1, by simpa using h₁, ?_⟩
      exact
        (G.mem_incidenceFinset (v := e.1.out.1) (e := (e : Sym2 V))).2
          ((G.edge_mem_incidenceSet_iff (a := e.1.out.1) (e := e)).2 (Sym2.out_fst_mem _))
    · refine ⟨e.1.out.2, by simpa using h₂, ?_⟩
      exact
        (G.mem_incidenceFinset (v := e.1.out.2) (e := (e : Sym2 V))).2
          ((G.edge_mem_incidenceSet_iff (a := e.1.out.2) (e := e)).2 (Sym2.out_snd_mem _))

/-- Helper for Theorem 4.23: an edge incident to `S` is either internal to `S` or crosses the
cut of `S`. -/
private lemma memOddSetIncidentEdgeFinsetIffMemInducedOrCut
    (S : Finset V) (e : G.edgeSet) :
    e ∈ oddSetIncidentEdgeFinset (G := G) S ↔
      e ∈ E[G] (S : Set V) ∨ e ∈ δ[G] (S : Set V) := by
  constructor
  · intro he
    rcases (memOddSetIncidentEdgeFinsetIff (G := G) S e).1 he with h₁ | h₂
    · by_cases h₂S : e.1.out.2 ∈ (S : Set V)
      · exact Or.inl <|
          (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).2 ⟨h₁, h₂S⟩
      · exact Or.inr <|
          (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).2 (Or.inl ⟨h₁, h₂S⟩)
    · by_cases h₁S : e.1.out.1 ∈ (S : Set V)
      · exact Or.inl <|
          (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).2 ⟨h₁S, h₂⟩
      · exact Or.inr <|
          (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).2 (Or.inr ⟨h₂, h₁S⟩)
  · intro he
    rcases he with hind | hcut
    · exact (memOddSetIncidentEdgeFinsetIff (G := G) S e).2
        (Or.inl ((memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 hind).1)
    · rcases (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 hcut with
        (⟨h₁, _⟩ | ⟨h₂, _⟩)
      · exact (memOddSetIncidentEdgeFinsetIff (G := G) S e).2 (Or.inl h₁)
      · exact (memOddSetIncidentEdgeFinsetIff (G := G) S e).2 (Or.inr h₂)

/-- Helper for Theorem 4.23: the edges incident to `S` split disjointly into the edges induced by
`S` and the cut edges of `S`. -/
private lemma oddSetIncidentEdgeFinsetSumEqInducedAddCut
    (S : Finset V) (x : G.edgeSet → ℝ) :
    (oddSetIncidentEdgeFinset (G := G) S).sum x =
      (E[G] (S : Set V)).sum x + (δ[G] (S : Set V)).sum x := by
  have hUnion :
      oddSetIncidentEdgeFinset (G := G) S = E[G] (S : Set V) ∪ δ[G] (S : Set V) := by
    ext e
    simp [memOddSetIncidentEdgeFinsetIffMemInducedOrCut]
  have hDisj : Disjoint (E[G] (S : Set V)) (δ[G] (S : Set V)) := by
    rw [Finset.disjoint_left]
    intro e he hind
    exact notMemCutEdgeFinsetOfMemInducedEdgeFinset (G := G) he hind
  -- Split the incident-edge sum along the induced/cut partition.
  rw [hUnion, Finset.sum_union hDisj]

/-- Helper for Theorem 4.23: filtering the vertices of `S` that lie on an edge agrees with
filtering the endpoint finset of that edge by membership in `S`. -/
private lemma edgeFilterEqEndpointFilter
    (S : Finset V) (e : G.edgeSet) :
    S.filter (fun v ↦ v ∈ (e : Sym2 V)) =
      ((e : Sym2 V).toFinset.filter fun v ↦ v ∈ (S : Set V)) := by
  -- Both sides describe the finite intersection `S ∩ ((e : Sym2 V).toFinset)`.
  ext v
  simpa [Finset.mem_filter, and_comm] using
    (show v ∈ S.filter (fun w ↦ w ∈ (e : Sym2 V)) ↔
      v ∈ ((e : Sym2 V).toFinset.filter fun w ↦ w ∈ (S : Set V)) by
        simp [Finset.mem_filter, Sym2.mem_toFinset])

/-- Helper for Theorem 4.23: the filtered endpoint cardinality of an edge is the sum of the
incident-edge indicator and the induced-edge indicator. -/
private lemma endpointFilterCardEqIncidentAddInduced
    (S : Finset V) (e : G.edgeSet) :
    ((((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) =
      (if e ∈ oddSetIncidentEdgeFinset (G := G) S then 1 else 0) +
        if e ∈ E[G] (S : Set V) then 1 else 0 := by
  have hne : e.1.out.1 ≠ e.1.out.2 := by
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
        simpa [e.1.out_eq] using e.prop
      exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
    exact G.ne_of_adj hadj
  -- Compute the filtered endpoint cardinality by splitting on the two endpoints.
  rw [edgeToFinsetEqPairFinset (G := G) e, pairFilterCardOfNeFinset _ _ hne]
  by_cases h₁ : e.1.out.1 ∈ (S : Set V)
  · by_cases h₂ : e.1.out.2 ∈ (S : Set V)
    · norm_num [h₁, h₂, memOddSetIncidentEdgeFinsetIff, memInducedEdgeFinsetEndpointsIff]
    · norm_num [h₁, h₂, memOddSetIncidentEdgeFinsetIff, memInducedEdgeFinsetEndpointsIff]
  · by_cases h₂ : e.1.out.2 ∈ (S : Set V)
    · norm_num [h₁, h₂, memOddSetIncidentEdgeFinsetIff, memInducedEdgeFinsetEndpointsIff]
    · norm_num [h₁, h₂, memOddSetIncidentEdgeFinsetIff, memInducedEdgeFinsetEndpointsIff]

/-- Helper for Theorem 4.23: summing the vertex-incidence equations on `S` counts each edge
incident to `S` once, plus one extra copy for each edge internal to `S`. -/
private lemma sumIncidenceOnFinsetEqOddSetIncidentAddInduced
    (S : Finset V) (x : G.edgeSet → ℝ) :
    Finset.sum S
      (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      (oddSetIncidentEdgeFinset (G := G) S).sum x + (E[G] (S : Set V)).sum x := by
  calc
    Finset.sum S
        (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        Finset.sum S
          (fun v ↦ ∑ e : G.edgeSet, if (e : Sym2 V) ∈ G.incidenceFinset v then x e else 0) := by
            -- Rewrite each incidence-filter sum as a full edge-set sum with an indicator.
            refine Finset.sum_congr rfl ?_
            intro v hv
            rw [Finset.sum_filter]
    _ = Finset.sum Finset.univ
          (fun e : G.edgeSet ↦
            Finset.sum S (fun v ↦ if (e : Sym2 V) ∈ G.incidenceFinset v then x e else 0)) := by
          -- Swap the vertex and edge summations.
          rw [Finset.sum_comm]
    _ = ∑ e : G.edgeSet,
          (S.filter fun v ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum (fun _ ↦ x e) := by
          -- Repackage the inner indicator sum as a filtered sum over the chosen vertices.
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [Finset.sum_filter]
    _ = ∑ e : G.edgeSet,
          ((((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) * x e := by
          -- Replace the filtered vertex set by the filtered endpoint set of `e`.
          refine Finset.sum_congr rfl ?_
          intro e he
          have hfilter :
              S.filter (fun v ↦ (e : Sym2 V) ∈ G.incidenceFinset v) =
                S.filter (fun v ↦ v ∈ (e : Sym2 V)) := by
            ext v
            simp [G.edge_mem_incidenceSet_iff]
          rw [hfilter, edgeFilterEqEndpointFilter (G := G) S e, Finset.sum_const]
          simp [nsmul_eq_mul]
    _ = ∑ e : G.edgeSet,
          (((if e ∈ oddSetIncidentEdgeFinset (G := G) S then 1 else 0) +
              if e ∈ E[G] (S : Set V) then 1 else 0) * x e) := by
          -- Replace the endpoint multiplicity by the incident-plus-induced decomposition.
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [endpointFilterCardEqIncidentAddInduced (G := G) S e]
    _ = ∑ e : G.edgeSet,
          ((if e ∈ oddSetIncidentEdgeFinset (G := G) S then x e else 0) +
            if e ∈ E[G] (S : Set V) then x e else 0) := by
          -- Each `0/1` coefficient turns into the corresponding indicator term.
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hOdd : e ∈ oddSetIncidentEdgeFinset (G := G) S <;>
            by_cases hInd : e ∈ E[G] (S : Set V) <;>
            simp [hOdd, hInd, add_mul]
    _ = (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ oddSetIncidentEdgeFinset (G := G) S).sum x +
          (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ E[G] (S : Set V)).sum x := by
          rw [Finset.sum_add_distrib]
          congr 1
          · exact edgeSetSumIteEqSumFilter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ oddSetIncidentEdgeFinset (G := G) S) x
          · exact edgeSetSumIteEqSumFilter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ E[G] (S : Set V)) x
    _ = (oddSetIncidentEdgeFinset (G := G) S).sum x + (E[G] (S : Set V)).sum x := by
          simp

/-- Helper for Theorem 4.23: summing the incidence equations on `S` counts each internal edge
twice and each cut edge once. -/
private lemma sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum
    (S : Set V) (x : G.edgeSet → ℝ) :
    Finset.sum S.toFinset
      (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      2 * (E[G] S).sum x + (δ[G] S).sum x := by
  calc
    Finset.sum S.toFinset
        (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        (oddSetIncidentEdgeFinset (G := G) S.toFinset).sum x + (E[G] S).sum x := by
          simpa using sumIncidenceOnFinsetEqOddSetIncidentAddInduced (G := G) S.toFinset x
    _ = ((E[G] (S.toFinset : Set V)).sum x + (δ[G] (S.toFinset : Set V)).sum x) + (E[G] S).sum x := by
          rw [oddSetIncidentEdgeFinsetSumEqInducedAddCut (G := G) S.toFinset x]
    _ = ((E[G] S).sum x + (δ[G] S).sum x) + (E[G] S).sum x := by
          simp
    _ = 2 * (E[G] S).sum x + (δ[G] S).sum x := by
          ring

/-- Helper for Theorem 4.23: summing the degree-one equations over a finite vertex set gives the
cardinality of that set. -/
private lemma incidenceSum_eq_card_of_eq_one {x : G.edgeSet → ℝ}
    (hx_deg : ∀ v : V,
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1)
    (S : Set V) :
    Finset.sum S.toFinite.toFinset
      (fun v ↦
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      (S.ncard : ℝ) := by
  -- Replace each incidence sum by the degree-one value and evaluate the constant finite sum.
  calc
    Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        Finset.sum S.toFinite.toFinset (fun _ : V ↦ (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            exact hx_deg v
    _ = (S.toFinite.toFinset.card : ℝ) := by
          simp
    _ = (S.ncard : ℝ) := by
          have hcard : S.toFinite.toFinset.card = S.ncard := by
            simpa [Set.toFinite_toFinset] using (Set.ncard_eq_toFinset_card' S).symm
          exact_mod_cast hcard

/-- Helper for Theorem 4.23: any point satisfying the perfect-matching constraints also satisfies
the matching constraints. -/
private lemma mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G) :
    x ∈ matchingConstraintSet G := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, hx_cut⟩
  rw [SimpleGraph.mem_matchingConstraintSet_iff]
  refine ⟨hx_nonneg, ?_, ?_⟩
  · intro v
    linarith [hx_deg v]
  · intro S hS
    have hdegreeSum :
        Finset.sum S.toFinite.toFinset
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
          (S.ncard : ℝ) :=
      incidenceSum_eq_card_of_eq_one (G := G) hx_deg S
    have hsplit :
        Finset.sum S.toFinite.toFinset
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
          2 * (E[G] S).sum x + (δ[G] S).sum x := by
      simpa using sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) S x
    have hcut_lb : 1 ≤ (δ[G] S).sum x := hx_cut S hS
    linarith

/-- Helper for Theorem 4.23: inside `matchingConstraintSet G`, the degree equations `= 1`
recover the full perfect-matching constraint system. -/
private lemma mem_perfectMatchingConstraintSet_of_mem_matchingConstraintSet_of_incidenceEqOne
    {x : G.edgeSet → ℝ}
    (hxMatch : x ∈ matchingConstraintSet G)
    (hx_deg : ∀ v : V,
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1) :
    x ∈ perfectMatchingConstraintSet G := by
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hxMatch with
    ⟨hx_nonneg, -, hx_odd⟩
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
  refine ⟨hx_nonneg, hx_deg, ?_⟩
  intro S hS
  have hdegreeSum :
      Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        (S.ncard : ℝ) :=
    incidenceSum_eq_card_of_eq_one (G := G) hx_deg S
  have hsplit :
      Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        2 * (E[G] S).sum x + (δ[G] S).sum x := by
    simpa using sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) S x
  have hinduced : (E[G] S).sum x ≤ ((S.ncard : ℝ) - 1) / 2 := hx_odd S hS
  linarith

/-- Helper for Theorem 4.23: once an odd-set inequality is tight inside the degree-one face, the
corresponding odd cut has total weight exactly `1`. -/
private lemma tightOddCut_eq_one_of_mem_perfectMatchingConstraintSet_of_tightOddSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) {S : Set V}
    (hTight : (E[G] S).sum x = ((S.ncard : ℝ) - 1) / 2) :
    (δ[G] S).sum x = 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨-, hx_deg, -⟩
  -- Sum the degree equations on `S`, then rewrite the resulting incidence count by induced
  -- edges plus the cut. Tightness of the odd-set inequality forces the cut weight to be `1`.
  have hdegreeSum :
      Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        (S.ncard : ℝ) :=
    incidenceSum_eq_card_of_eq_one (G := G) hx_deg S
  have hsplit :
      Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        2 * (E[G] S).sum x + (δ[G] S).sum x := by
    simpa using sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) S x
  linarith

/-- Helper for Theorem 4.23: `perfectMatchingConstraintSet G` is the degree-one extreme slice of
`matchingConstraintSet G`. -/
private lemma perfectMatchingConstraintSet_isExtremeIn_matchingConstraintSet :
    IsExtreme ℝ (matchingConstraintSet G) (perfectMatchingConstraintSet G) := by
  refine ⟨fun x hx ↦
    mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet (G := G) hx, ?_⟩
  intro x hxMatch y hyMatch z hzPerfect hzSeg
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hxMatch with
    ⟨-, hx_deg_le, -⟩
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := y)).1 hyMatch with
    ⟨-, hy_deg_le, -⟩
  rw [openSegment_eq_image₂ ℝ x y] at hzSeg
  rcases hzSeg with ⟨p, hp, hzEq⟩
  let a : ℝ := p.1
  let b : ℝ := p.2
  have ha : 0 < a := hp.1
  have hb_pos : 0 < b := hp.2.1
  have hab : a + b = 1 := hp.2.2
  have hzPerfect' : a • x + b • y ∈ perfectMatchingConstraintSet G := by
    simpa [a, b, hzEq] using hzPerfect
  rcases
      (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := a • x + b • y)).1
        hzPerfect' with
    ⟨-, hz_deg, -⟩
  have hxDegreeEqOne :
      ∀ v : V,
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1 := by
    intro v
    have havg :
        a *
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x +
          b *
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum y =
        1 := by
      calc
        a *
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x +
          b *
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum y =
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum (a • x + b • y) := by
                simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
                  Finset.sum_add_distrib]
        _ = 1 := hz_deg v
    nlinarith [havg, hx_deg_le v, hy_deg_le v, ha, hb_pos]
  exact mem_perfectMatchingConstraintSet_of_mem_matchingConstraintSet_of_incidenceEqOne
    (G := G) hxMatch hxDegreeEqOne

/-- Helper for Theorem 4.23: extreme points of `perfectMatchingConstraintSet G` remain extreme in
the larger owner `matchingConstraintSet G`. -/
private lemma mem_extremePoints_matchingConstraintSet_of_mem_extremePoints_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ) :
    x ∈ (matchingConstraintSet G).extremePoints ℝ := by
  exact IsExtreme.extremePoints_subset_extremePoints
    (perfectMatchingConstraintSet_isExtremeIn_matchingConstraintSet (G := G)) hx

/-- Helper for Theorem 4.23: `perfectMatchingConstraintSet G` is convex. -/
private lemma convexPerfectMatchingConstraintSet :
    Convex ℝ (perfectMatchingConstraintSet G) := by
  intro x hx y hy a b ha hb hab
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, hx_cut⟩
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := y)).1 hy with
    ⟨hy_nonneg, hy_deg, hy_cut⟩
  refine (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := a • x + b • y)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro e
    -- Nonnegativity is preserved coordinatewise under convex combinations.
    have hcoord : (a • x + b • y) e = a * x e + b * y e := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcoord]
    nlinarith [hx_nonneg e, hy_nonneg e, ha, hb]
  · intro v
    -- The degree equations are affine, so the convex combination still sums to `1`.
    calc
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum (a • x + b • y)
          = a *
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x +
            b *
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum y := by
                simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
                  Finset.sum_add_distrib]
      _ = a * 1 + b * 1 := by rw [hx_deg v, hy_deg v]
      _ = 1 := by nlinarith
  · intro S hS
    -- Odd-cut lower bounds are preserved because the coefficients are nonnegative and sum to `1`.
    calc
      1 = a * 1 + b * 1 := by nlinarith
      _ ≤ a * (δ[G] S).sum x + b * (δ[G] S).sum y := by
            nlinarith [hx_cut S hS, hy_cut S hS, ha, hb]
      _ = (δ[G] S).sum (a • x + b • y) := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
              Finset.sum_add_distrib]

/-- Helper for Theorem 4.23: in a weighted average of numbers in `[0, 1]` with total weight `1`,
every positive-weight support term must already equal `1` if the average is `1`. -/
private lemma eqOneOfWeightedAverageEqOne {ι : Type*} [Fintype ι] {w a : ι → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (ha_le_one : ∀ i, a i ≤ 1)
    (hw_sum : ∑ i, w i = 1)
    (havg : ∑ i, w i * a i = 1) :
    ∀ i, w i ≠ 0 → a i = 1 := by
  have hterm_nonneg : ∀ i, 0 ≤ w i * (1 - a i) := by
    intro i
    exact mul_nonneg (hw_nonneg i) (sub_nonneg.mpr (ha_le_one i))
  have hterm_sum : ∑ i, w i * (1 - a i) = 0 := by
    calc
      ∑ i, w i * (1 - a i) = ∑ i, (w i - w i * a i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = (∑ i, w i) - ∑ i, w i * a i := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := by
            nlinarith [hw_sum, havg]
  have hzero : ∀ i, w i * (1 - a i) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _hj ↦ hterm_nonneg j)).1 hterm_sum i
      (Finset.mem_univ i)
  intro i hwi
  have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
  have hslack_nonneg : 0 ≤ 1 - a i := sub_nonneg.mpr (ha_le_one i)
  have hslack_zero : 1 - a i = 0 := by
    nlinarith [hzero i, hwi_pos, hslack_nonneg]
  nlinarith [hslack_zero]

/-- Helper for Theorem 4.23: a convex decomposition by matchings upgrades to one by perfect
matchings once the barycenter already satisfies the perfect-matching degree equations. -/
private lemma perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ}
    (hx_matchingPolytope : x ∈ matchingPolytope G)
    (hxPerfect : x ∈ perfectMatchingConstraintSet G) :
    x ∈ perfectMatchingPolytope G := by
  rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype] at hx_matchingPolytope
  rcases hx_matchingPolytope with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hx_sum⟩
  have hz' : ∀ i, ∃ M : G.Subgraph, M.IsMatching ∧ z i = G.subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hz i
  choose M hMatch hVec using hz'
  have hx_sum_match :
      ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = x := by
    calc
      ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = ∑ i, w i • z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hVec i]
      _ = x := hx_sum
  have hsupport_perfect :
      ∀ i, w i ≠ 0 → (M i).IsPerfectMatching := by
    rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hxPerfect with
      ⟨-, hx_deg, -⟩
    intro i hwi
    refine ⟨hMatch i, ?_⟩
    intro v
    let I : Finset G.edgeSet :=
      Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v
    have hterm :
        ∀ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) =
          Finset.sum I (fun e ↦ w j * G.subgraphIncidenceVector ℝ (M j) e) := by
      intro j
      rw [Finset.mul_sum]
    have havg :
        ∑ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) = 1 := by
      calc
        ∑ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) =
            ∑ j, Finset.sum I (fun e ↦ w j * G.subgraphIncidenceVector ℝ (M j) e) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              exact hterm j
        _ = Finset.sum I (fun e ↦ ∑ j, w j * G.subgraphIncidenceVector ℝ (M j) e) := by
              rw [Finset.sum_comm]
        _ = Finset.sum I x := by
              refine Finset.sum_congr rfl ?_
              intro e he
              simpa using
                weightedSumApply (G := G) w (fun j ↦ G.subgraphIncidenceVector ℝ (M j))
                  hx_sum_match e
        _ = 1 := by
              exact hx_deg v
    have hle :
        ∀ j, I.sum (G.subgraphIncidenceVector ℝ (M j)) ≤ 1 := by
      intro j
      simpa [I] using matchingIncidenceSumLeOne (G := G) (hMatch j) v
    have hi_sum_eq_one :
        I.sum (G.subgraphIncidenceVector ℝ (M i)) = 1 :=
      eqOneOfWeightedAverageEqOne hw_nonneg hle hw_sum havg i hwi
    by_contra hv
    have hi_sum_eq_zero :
        I.sum (G.subgraphIncidenceVector ℝ (M i)) = 0 := by
      simpa [I] using subgraphIncidenceSumEqZeroOfNotMemVerts (G := G) (M := M i) hv
    linarith
  have hweight_nonzero : ∑ i, w i ≠ 0 := by
    rw [hw_sum]
    norm_num
  obtain ⟨i₀, -, hi₀_nonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hweight_nonzero
  have hM₀_perfect : (M i₀).IsPerfectMatching := hsupport_perfect i₀ hi₀_nonzero
  let zPerfect : ι → G.edgeSet → ℝ :=
    fun i ↦ if hwi : w i = 0 then G.subgraphIncidenceVector ℝ (M i₀) else z i
  have hzPerfect :
      ∀ i, ∃ N : G.Subgraph, N.IsPerfectMatching ∧ zPerfect i = G.subgraphIncidenceVector ℝ N := by
    intro i
    by_cases hwi : w i = 0
    · refine ⟨M i₀, hM₀_perfect, ?_⟩
      simp [zPerfect, hwi]
    · refine ⟨M i, hsupport_perfect i hwi, ?_⟩
      simp [zPerfect, hwi, hVec i]
  have hx_sum_perfect : ∑ i, w i • zPerfect i = x := by
    calc
      ∑ i, w i • zPerfect i = ∑ i, w i • z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hwi : w i = 0
        · ext e
          simp [zPerfect, hwi]
        · ext e
          simp [zPerfect, hwi]
      _ = x := hx_sum
  rw [SimpleGraph.perfectMatchingPolytope, mem_convexHull_iff_exists_fintype]
  refine ⟨ι, inferInstance, w, zPerfect, hw_nonneg, hw_sum, ?_, hx_sum_perfect⟩
  intro i
  rcases hzPerfect i with ⟨N, hN, hzN⟩
  exact ⟨N, hN, hzN⟩

/-- Helper for Theorem 4.23: every perfect-matching generator already satisfies the perfect
constraint system, so the whole perfect matching polytope lies in the constraint set. -/
private lemma perfectMatchingPolytope_subset_perfectMatchingConstraintSet :
    perfectMatchingPolytope G ⊆ perfectMatchingConstraintSet G := by
  intro x hx
  -- The generator feasibility check extends from perfect matchings to their convex hull.
  rw [SimpleGraph.perfectMatchingPolytope] at hx
  refine convexHull_min ?_ (convexPerfectMatchingConstraintSet (G := G)) hx
  intro y hy
  rcases hy with ⟨M, hM, rfl⟩
  exact subgraphIncidenceVector_mem_perfectMatchingConstraintSet (G := G) hM

/-- Helper for Theorem 4.23: every perfect-matching generator is already a matching generator, so
the perfect matching polytope sits inside the ambient matching polytope. -/
private lemma perfectMatchingPolytope_subset_matchingPolytope :
    perfectMatchingPolytope G ⊆ matchingPolytope G := by
  -- Rewrite both owners as convex hulls and use the inclusion of perfect-matchings into
  -- matchings generatorwise.
  rw [SimpleGraph.perfectMatchingPolytope, SimpleGraph.matchingPolytope]
  exact convexHull_mono <| by
    intro x hx
    rcases hx with ⟨M, hM, rfl⟩
    exact ⟨M, hM.1, rfl⟩

/-- Helper for Theorem 4.23: every feasible edge coordinate of `perfectMatchingConstraintSet G`
is bounded above by `1`. -/
private lemma edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) (e : G.edgeSet) :
    x e ≤ 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, -⟩
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset e.1.out.1
  have heI : e ∈ I := by
    simp [I, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff,
      Sym2.out_fst_mem]
  have hsingle : x e ≤ I.sum x := by
    exact Finset.single_le_sum (fun f _ ↦ hx_nonneg f) heI
  have hsum_eq : I.sum x = 1 := by
    simpa [I] using hx_deg e.1.out.1
  linarith

/-- Helper for Theorem 4.23: if a feasible perfect-matching point avoids the reducible `0/1`
coordinates, then every edge coordinate lies strictly between `0` and `1`. -/
private lemma edgeCoordinateStrictBounds_of_mem_perfectMatchingConstraintSet_of_ne_zero_ne_one
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G)
    (hx_ne_zero : ∀ e : G.edgeSet, x e ≠ 0)
    (hx_ne_one : ∀ e : G.edgeSet, x e ≠ 1) :
    ∀ e : G.edgeSet, 0 < x e ∧ x e < 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, -⟩
  intro e
  constructor
  · -- Without a zero coordinate, nonnegativity upgrades to strict positivity.
    exact lt_of_le_of_ne (hx_nonneg e) (by
      intro h
      exact hx_ne_zero e h.symm)
  · -- Without a unit coordinate, the degree-one upper bound upgrades to strict inequality.
    exact lt_of_le_of_ne
      (edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet (G := G) hx e)
      (hx_ne_one e)

/-- Helper for Theorem 4.23: if one incident edge already has weight `1`, then every other edge
incident to the same vertex must have weight `0`. -/
private lemma eqZeroOfOtherIncidentEdge_of_incidenceSumEqOne
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) {v : V}
    {e f : G.edgeSet}
    (heI : e ∈ Finset.univ.filter
      fun g : G.edgeSet ↦ (g : Sym2 V) ∈ G.incidenceFinset v)
    (hxe : x e = 1)
    (hfI : f ∈ Finset.univ.filter
      fun g : G.edgeSet ↦ (g : Sym2 V) ∈ G.incidenceFinset v)
    (hf_ne : f ≠ e) :
    x f = 0 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, -⟩
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun g : G.edgeSet ↦ (g : Sym2 V) ∈ G.incidenceFinset v
  have hsum_eq : I.sum x = 1 := by
    -- The Chapter 4.23 degree equation fixes the whole incidence sum at `v`.
    simpa [I] using hx_deg v
  have hdecomp : x e + (I.erase e).sum x = I.sum x := by
    exact Finset.add_sum_erase I x (by simpa [I] using heI)
  have hfErase : f ∈ I.erase e := by
    simpa [I] using Finset.mem_erase.mpr ⟨hf_ne, hfI⟩
  have hsingle : x f ≤ (I.erase e).sum x := by
    -- Any second incident edge is bounded by the residual incidence mass at `v`.
    exact Finset.single_le_sum (fun g _ ↦ hx_nonneg g) hfErase
  have hrest_zero : (I.erase e).sum x = 0 := by
    linarith
  have hxf_le_zero : x f ≤ 0 := by
    simpa [hrest_zero] using hsingle
  linarith [hx_nonneg f, hxf_le_zero]

/-- Helper for Theorem 4.23: an integer point of `perfectMatchingConstraintSet G` has only `0/1`
edge coordinates. -/
private lemma edgeCoordinateEqZeroOrOneOfMemPerfectMatchingConstraintSetOfInteger
    {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G)
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (e : G.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, -⟩
  rcases hx_int with ⟨z, rfl⟩
  have hz_nonneg : (0 : ℤ) ≤ z e := by
    have hreal : (0 : ℝ) ≤ (z e : ℝ) := by simpa using hx_nonneg e
    exact_mod_cast hreal
  have hz_le_one : z e ≤ 1 := by
    have hreal : ((z e : ℝ) ≤ 1) := by
      simpa using edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet
        (G := G) (x := Int.cast ∘ z) hx e
    exact_mod_cast hreal
  have hz_cases : z e = 0 ∨ z e = 1 := by
    omega
  rcases hz_cases with hzero | hone
  · left
    simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hzero
  · right
    simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hone

/-- Helper for Theorem 4.23: an integer point of `perfectMatchingConstraintSet G` is already the
incidence vector of a perfect matching. -/
private lemma integerPoint_eq_subgraphIncidenceVector_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G)
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = G.subgraphIncidenceVector ℝ M := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, -⟩
  have hx_zero_one : ∀ e : G.edgeSet, x e = 0 ∨ x e = 1 := by
    intro e
    exact edgeCoordinateEqZeroOrOneOfMemPerfectMatchingConstraintSetOfInteger
      (G := G) hx hx_int e
  let M : G.Subgraph :=
    { verts := {v : V | ∃ w, ∃ h : G.Adj v w, x ⟨s(v, w), G.mem_edgeSet.2 h⟩ = 1}
      Adj := fun v w ↦ ∃ h : G.Adj v w, x ⟨s(v, w), G.mem_edgeSet.2 h⟩ = 1
      adj_sub := fun h ↦ h.1
      edge_vert := fun h ↦ ⟨_, h⟩
      symm := by
        intro v w h
        rcases h with ⟨hvw, hxvw⟩
        refine ⟨hvw.symm, ?_⟩
        simpa [Sym2.eq_swap] using hxvw }
  have hMemEdge :
      ∀ e : G.edgeSet, e.1 ∈ M.edgeSet ↔ x e = 1 := by
    intro e
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      rw [← G.mem_edgeSet]
      simpa [e.1.out_eq] using e.2
    rw [← e.1.out_eq, Subgraph.mem_edgeSet]
    constructor
    · rintro ⟨hG, hxG⟩
      have hSubtype :
          (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hG⟩ : G.edgeSet) = e := by
        apply Subtype.ext
        exact e.1.out_eq
      simpa [hSubtype] using hxG
    · intro hx1
      refine ⟨hadj, ?_⟩
      have hSubtype :
          (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hadj⟩ : G.edgeSet) = e := by
        apply Subtype.ext
        exact e.1.out_eq
      simpa [hSubtype] using hx1
  have hAllVerts : ∀ v : V, v ∈ M.verts := by
    intro v
    let I : Finset G.edgeSet :=
      Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v
    have hsum_ne_zero : I.sum x ≠ 0 := by
      rw [hx_deg v]
      norm_num
    obtain ⟨e, heI, hxe_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne_zero
    have hxe_one : x e = 1 := by
      rcases hx_zero_one e with hxe_zero | hxe_one
      · exact (hxe_ne hxe_zero).elim
      · exact hxe_one
    have hvMem : v ∈ (e : Sym2 V) := by
      have heInc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp heI).2
      simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using heInc
    let w : V := Sym2.Mem.other hvMem
    have hAdj : G.Adj v w := by
      exact (SimpleGraph.mem_edgeSet (G := G) (v := v) (w := w)).1
        (by simpa [w, Sym2.other_spec hvMem] using e.prop)
    have hSubtype : (⟨s(v, w), G.mem_edgeSet.2 hAdj⟩ : G.edgeSet) = e := by
      apply Subtype.ext
      simpa [w] using Sym2.other_spec hvMem
    -- A nonzero incidence term at `v` provides a support edge through `v`.
    refine ⟨w, hAdj, ?_⟩
    simpa [hSubtype] using hxe_one
  have hMatching : M.IsMatching := by
    intro v hv
    rcases hv with ⟨w, hvw, hxvw⟩
    refine ⟨w, ⟨hvw, hxvw⟩, ?_⟩
    intro u hu
    let I : Finset G.edgeSet :=
      Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v
    let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.2 hvw⟩
    let f : G.edgeSet := ⟨s(v, u), G.mem_edgeSet.2 hu.1⟩
    have heI : e ∈ I := by
      simp [I, e, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
    have hfI : f ∈ I := by
      simp [I, f, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
    have hxe_one : x e = 1 := by simpa [e] using hxvw
    have hxf_one : x f = 1 := by simpa [f] using hu.2
    by_contra hwu
    have hfe : f ≠ e := by
      intro hfeEq
      apply hwu
      have hs : s(v, u) = s(v, w) := by
        simpa [f, e] using congrArg Subtype.val hfeEq
      exact Sym2.congr_right.mp hs
    have hfErase : f ∈ I.erase e := Finset.mem_erase.mpr ⟨hfe, hfI⟩
    have hsum_erase_ge_one : 1 ≤ (I.erase e).sum x := by
      have hsingle : x f ≤ (I.erase e).sum x := by
        exact Finset.single_le_sum (fun g _ ↦ hx_nonneg g) hfErase
      linarith
    have hsum_eq_one : I.sum x = 1 := by
      simpa [I] using hx_deg v
    have hdecomp : x e + (I.erase e).sum x = I.sum x := by
      exact Finset.add_sum_erase I x heI
    linarith
  have hPerfect : M.IsPerfectMatching := by
    refine ⟨hMatching, ?_⟩
    intro v
    exact hAllVerts v
  refine ⟨M, hPerfect, ?_⟩
  funext e
  by_cases hxe : x e = 1
  · have heM : e.1 ∈ M.edgeSet := (hMemEdge e).2 hxe
    simp [SimpleGraph.subgraphIncidenceVector, heM, hxe]
  · have hxe_zero : x e = 0 := by
      rcases hx_zero_one e with hzero | hone
      · exact hzero
      · exact (hxe hone).elim
    have heM : e.1 ∉ M.edgeSet := by
      intro heM
      exact hxe ((hMemEdge e).1 heM)
    simp [SimpleGraph.subgraphIncidenceVector, heM, hxe_zero]

/-- Helper for Theorem 4.23: a subgraph incidence vector is an integer lattice point in the edge
coordinate space. -/
private lemma subgraphIncidenceVector_memIntegerRange (M : G.Subgraph) :
    G.subgraphIncidenceVector ℝ M ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z) := by
  refine ⟨fun e : G.edgeSet ↦ if e.1 ∈ M.edgeSet then 1 else 0, ?_⟩
  -- Evaluate the coordinatewise `0/1` witness at each edge.
  funext e
  by_cases heM : e.1 ∈ M.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, heM]
  · simp [SimpleGraph.subgraphIncidenceVector, heM]

/-- Helper for Theorem 4.23: a nonintegral point of the perfect-matching constraint set has a
truly fractional edge coordinate. -/
private lemma exists_fractionalEdge_of_mem_perfectMatchingConstraintSet_of_not_integer
    {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G)
    (hx_not_int : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    ∃ e : G.edgeSet, 0 < x e ∧ x e < 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, -⟩
  by_contra hfrac
  have hzero_one : ∀ e : G.edgeSet, x e = 0 ∨ x e = 1 := by
    intro e
    by_cases hpos : 0 < x e
    · right
      have hone_le : 1 ≤ x e := by
        by_contra hone_lt
        exact hfrac ⟨e, hpos, lt_of_not_ge hone_lt⟩
      linarith [edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet (G := G) hx e, hone_le]
    · left
      linarith [hx_nonneg e]
  let z : G.edgeSet → ℤ := fun e ↦ if x e = 0 then 0 else 1
  have hz : x = Int.cast ∘ z := by
    -- Every coordinate is already forced into the `0/1` integer range.
    funext e
    rcases hzero_one e with hzero | hone
    · simp [z, hzero]
    · simp [z, hone]
  exact hx_not_int ⟨z, hz.symm⟩

/-- Helper for Theorem 4.23: a nonintegral extreme point of the perfect-matching constraint set
cannot come from the bipartite case, because there the constraint set already equals the perfect
matching polytope. -/
private lemma not_isBipartite_of_mem_extremePoints_perfectMatchingConstraintSet_of_not_integer
    {x : G.edgeSet → ℝ}
    (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ)
    (hx_not_int : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    ¬ G.IsBipartite := by
  intro hG
  have hxExtremePoly :
      x ∈ (perfectMatchingPolytope G).extremePoints ℝ := by
    -- In the bipartite case both owners share the same matrix description.
    simpa [SimpleGraph.perfectMatchingConstraintSet_eq_setOf_mulVec_eq_one,
      SimpleGraph.perfectMatchingPolytope_eq_setOf_mulVec_eq_one, hG] using hx
  rw [SimpleGraph.perfectMatchingPolytope] at hxExtremePoly
  rcases extremePoints_convexHull_subset hxExtremePoly with ⟨M, hM, rfl⟩
  -- A perfect-matching generator is visibly integer-valued, contradicting nonintegrality.
  exact hx_not_int (subgraphIncidenceVector_memIntegerRange (G := G) M)

/-- Helper for Theorem 4.23: the matching-polytope theorem upgrades feasible perfect-matching
constraint points to points of `matchingPolytope G`. -/
private lemma mem_matchingPolytope_of_mem_extremePoints_perfectMatchingConstraintSet_of_not_integer_of_smaller
    (_hsmaller :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet < Fintype.card V + Fintype.card G.edgeSet →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H)
    {x : G.edgeSet → ℝ}
    (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ)
    (_hx_not_int : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    x ∈ matchingPolytope G := by
  -- TODO: replace this placeholder with the tight-odd-set contraction route so the smaller-graph
  -- hypothesis `hsmaller` proves the matching-polytope bridge without importing Theorem 4.24.
  sorry

/-- Helper for Theorem 4.23: every extreme point of `perfectMatchingConstraintSet G` is one of the
perfect-matching generators. -/
private lemma exists_isPerfectMatching_of_mem_extremePoints_perfectMatchingConstraintSet_of_smaller
    (hsmaller :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet < Fintype.card V + Fintype.card G.edgeSet →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H)
    {x : G.edgeSet → ℝ} (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = G.subgraphIncidenceVector ℝ M := by
  by_cases hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)
  · -- Integer extreme points are reconstructed directly from their `0/1` support.
    exact integerPoint_eq_subgraphIncidenceVector_of_mem_perfectMatchingConstraintSet
      (G := G) (extremePoints_subset hx) hx_int
  · have hxMatch :
        x ∈ matchingPolytope G :=
      mem_matchingPolytope_of_mem_extremePoints_perfectMatchingConstraintSet_of_not_integer_of_smaller
        (G := G) hsmaller hx hx_int
    have hxPerfect : x ∈ perfectMatchingConstraintSet G := extremePoints_subset hx
    have hxPerfectPoly : x ∈ perfectMatchingPolytope G :=
      perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
        (G := G) hxMatch hxPerfect
    have hxExtremePerfect :
        x ∈ (perfectMatchingPolytope G).extremePoints ℝ := by
      -- Extremality in the larger perfect-constraint owner restricts to the smaller polytope.
      exact inter_extremePoints_subset_extremePoints_of_subset
        (perfectMatchingPolytope_subset_perfectMatchingConstraintSet (G := G))
        ⟨hxPerfectPoly, hx⟩
    rw [SimpleGraph.perfectMatchingPolytope] at hxExtremePerfect
    have hxGenerator :
        x ∈ {y : G.edgeSet → ℝ |
          ∃ M : G.Subgraph, M.IsPerfectMatching ∧ y = G.subgraphIncidenceVector ℝ M} :=
      extremePoints_convexHull_subset hxExtremePerfect
    exact hxGenerator

/-- Helper for Theorem 4.23: the perfect-matching constraint set is compact. -/
private lemma perfectMatchingConstraintSet_isCompact :
    IsCompact (perfectMatchingConstraintSet G) := by
  have hclosed : IsClosed (perfectMatchingConstraintSet G) := by
    have hrepr :
        perfectMatchingConstraintSet G =
          ((⋂ e : G.edgeSet, {x : G.edgeSet → ℝ | 0 ≤ x e}) ∩
              ⋂ v : V,
                {x : G.edgeSet → ℝ |
                  (Finset.univ.filter
                    fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1}) ∩
            ⋂ S : Set V, {x : G.edgeSet → ℝ | Odd S.ncard → 1 ≤ (δ[G] S).sum x} := by
      ext x
      simp [SimpleGraph.mem_perfectMatchingConstraintSet_iff, and_assoc]
    rw [hrepr]
    have hcoordClosed :
        IsClosed (⋂ e : G.edgeSet, {x : G.edgeSet → ℝ | 0 ≤ x e}) := by
      refine isClosed_iInter fun e : G.edgeSet ↦ ?_
      -- Each coordinate nonnegativity constraint is a closed halfspace.
      simpa using isClosed_le continuous_const
        (continuous_apply e : Continuous fun x : G.edgeSet → ℝ ↦ x e)
    have hdegClosed :
        IsClosed (⋂ v : V,
          {x : G.edgeSet → ℝ |
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1}) := by
      refine isClosed_iInter fun v : V ↦ ?_
      let incidenceMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun x ↦
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x
          map_add' := by
            intro x y
            simp [Finset.sum_add_distrib]
          map_smul' := by
            intro a x
            simp [smul_eq_mul, Finset.mul_sum] }
      -- Each degree equation cuts out a closed affine hyperplane.
      change IsClosed (incidenceMap ⁻¹' ({1} : Set ℝ))
      exact isClosed_singleton.preimage incidenceMap.continuous_of_finiteDimensional
    have hcutClosed :
        IsClosed (⋂ S : Set V, {x : G.edgeSet → ℝ | Odd S.ncard → 1 ≤ (δ[G] S).sum x}) := by
      refine isClosed_iInter fun S : Set V ↦ ?_
      by_cases hS : Odd S.ncard
      · let cutMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
          { toFun := fun x ↦ (δ[G] S).sum x
            map_add' := by
              intro x y
              simp [Finset.sum_add_distrib]
            map_smul' := by
              intro a x
              simp [smul_eq_mul, Finset.mul_sum] }
        have hEq :
            {x : G.edgeSet → ℝ | Odd S.ncard → 1 ≤ (δ[G] S).sum x} =
              {x : G.edgeSet → ℝ | 1 ≤ (δ[G] S).sum x} := by
          ext x
          simp [hS]
        rw [hEq]
        -- Each odd-cut inequality is a closed halfspace.
        change IsClosed (cutMap ⁻¹' Set.Ici (1 : ℝ))
        exact isClosed_Ici.preimage cutMap.continuous_of_finiteDimensional
      · have hEq :
            {x : G.edgeSet → ℝ | Odd S.ncard → 1 ≤ (δ[G] S).sum x} = Set.univ := by
          ext x
          simp [hS]
        rw [hEq]
        exact isClosed_univ
    simpa [Set.inter_assoc] using hcoordClosed.inter (hdegClosed.inter hcutClosed)
  have hsubset_cube : perfectMatchingConstraintSet G ⊆ Set.Icc (0 : G.edgeSet → ℝ) 1 := by
    intro x hx
    rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
      ⟨hx_nonneg, -, -⟩
    refine ⟨hx_nonneg, ?_⟩
    intro e
    exact edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet (G := G) hx e
  -- The feasible region is a closed subset of the compact edge-coordinate cube.
  exact IsCompact.of_isClosed_subset isCompact_Icc hclosed hsubset_cube

/-- Helper for Theorem 4.23: the perfect matching polytope is compact because it is the convex
hull of finitely many perfect-matching generators. -/
private lemma perfectMatchingPolytope_isCompact :
    IsCompact (perfectMatchingPolytope G) := by
  let perfectGenerators : Set (G.edgeSet → ℝ) :=
    Set.range fun M : {M : G.Subgraph // M.IsPerfectMatching} ↦
      G.subgraphIncidenceVector ℝ M.1
  have hgenerators :
      {x | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = G.subgraphIncidenceVector ℝ M} =
        perfectGenerators := by
    ext x
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact ⟨⟨M, hM⟩, rfl⟩
    · rintro ⟨M, rfl⟩
      exact ⟨M.1, M.2, rfl⟩
  have hfinite : perfectGenerators.Finite := by
    -- The subtype of perfect matchings is finite, so its incidence-vector image is finite.
    exact Set.finite_range _
  -- Rewrite the polytope as a convex hull of a finite family of generators.
  rw [SimpleGraph.perfectMatchingPolytope, hgenerators]
  simpa [perfectGenerators] using hfinite.isCompact_convexHull ℝ

/-- Helper for Theorem 4.23: the reverse inclusion is best organized as strong induction on
`|V| + |E|`, so smaller contractions can call the theorem itself instead of re-proving a closed
world bridge. -/
private theorem perfectMatchingConstraintSet_subset_perfectMatchingPolytope_byCard :
    ∀ n : ℕ,
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet = n →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro W _ H hcard x hx
  let _ : DecidableEq W := Classical.decEq W
  let _ : DecidableRel H.Adj := Classical.decRel H.Adj
  have hsmaller :
      ∀ {W' : Type u} [Fintype W'] (H' : SimpleGraph W'),
        Fintype.card W' + Fintype.card H'.edgeSet < Fintype.card W + Fintype.card H.edgeSet →
          perfectMatchingConstraintSet H' ⊆ perfectMatchingPolytope H' := by
    intro W' _ H' hlt
    let _ : DecidableEq W' := Classical.decEq W'
    let _ : DecidableRel H'.Adj := Classical.decRel H'.Adj
    have hlt' : Fintype.card W' + Fintype.card H'.edgeSet < n := by
      simpa [← hcard] using hlt
    exact ih (Fintype.card W' + Fintype.card H'.edgeSet) hlt' H' rfl
  have hclosure :
      closure (convexHull ℝ ((perfectMatchingConstraintSet H).extremePoints ℝ)) =
        perfectMatchingConstraintSet H := by
    exact closure_convexHull_extremePoints
      (perfectMatchingConstraintSet_isCompact (G := H))
      (convexPerfectMatchingConstraintSet (G := H))
  have hxClosure :
      x ∈ closure (convexHull ℝ ((perfectMatchingConstraintSet H).extremePoints ℝ)) := by
    -- Krein-Milman rewrites the compact convex owner as the closure of the convex hull of its
    -- extreme points.
    simpa [hclosure] using hx
  have hExtremeSubset :
      (perfectMatchingConstraintSet H).extremePoints ℝ ⊆ perfectMatchingPolytope H := by
    intro y hy
    -- Route correction: classify extreme points using the smaller-graph inclusion owner, rather
    -- than asking one closed-world bridge to synthesize the whole recursion.
    rcases exists_isPerfectMatching_of_mem_extremePoints_perfectMatchingConstraintSet_of_smaller
        (G := H) hsmaller hy with ⟨M, hM, rfl⟩
    rw [SimpleGraph.perfectMatchingPolytope]
    exact subset_convexHull ℝ _ ⟨M, hM, rfl⟩
  have hHullSubset :
      convexHull ℝ ((perfectMatchingConstraintSet H).extremePoints ℝ) ⊆ perfectMatchingPolytope H := by
    -- The convex hull stays inside the perfect matching polytope because the latter is convex.
    refine convexHull_min hExtremeSubset ?_
    rw [SimpleGraph.perfectMatchingPolytope]
    exact convex_convexHull ℝ _
  have hxClosurePerfect : x ∈ closure (perfectMatchingPolytope H) := by
    -- Once every extreme point is a perfect-matching generator, the same holds for their convex
    -- hull and hence for its closure.
    exact (closure_mono hHullSubset) hxClosure
  -- The perfect matching polytope is compact, hence closed, so the closure can be removed.
  simpa [(perfectMatchingPolytope_isCompact (G := H)).isClosed.closure_eq] using hxClosurePerfect

/-- Helper for Theorem 4.23: the reverse inclusion is the specialization of the strong-induction
owner to the current graph `G`. -/
lemma perfectMatchingConstraintSet_subset_perfectMatchingPolytope :
    perfectMatchingConstraintSet G ⊆ perfectMatchingPolytope G := by
  -- Route correction: the theorem-level induction owner now carries the smaller-graph calls.
  exact perfectMatchingConstraintSet_subset_perfectMatchingPolytope_byCard
    (n := Fintype.card V + Fintype.card G.edgeSet) (H := G) rfl

/-- Theorem 4.23 (Perfect Matching Polytope Theorem). The perfect matching polytope of a finite
graph `G` is exactly the set of edge-vectors that are nonnegative and satisfy the degree
equations and odd-cut inequalities. -/
theorem perfectMatchingPolytope_eq_perfectMatchingConstraintSet :
    perfectMatchingPolytope G = perfectMatchingConstraintSet G := by
  refine le_antisymm ?_ ?_
  · -- The forward inclusion is the generator-feasibility half of the theorem.
    exact perfectMatchingPolytope_subset_perfectMatchingConstraintSet (G := G)
  · -- Route correction: the reverse inclusion is not reduced by unfolding; it needs the native
    -- extreme-point bridge into `matchingPolytope G` before the matching-to-perfect upgrade.
    exact perfectMatchingConstraintSet_subset_perfectMatchingPolytope (G := G)

end Theorem_4_23
