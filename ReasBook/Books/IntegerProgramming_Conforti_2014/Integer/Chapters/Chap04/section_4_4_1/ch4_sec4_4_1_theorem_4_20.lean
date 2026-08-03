import Mathlib
import Integer.Chapters.Chap04.section_4_4_1.ch4_sec4_4_1_definition_4_4_1_extra_1

namespace SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

open scoped symmDiff
open Walk (IsMatchingAugmenting)

namespace Subgraph

/-- Helper for Theorem 4.20: membership in the symmetric difference of two spanning subgraphs means
that exactly one of the two matchings contains the edge. -/
lemma mem_symmDiff_spanningCoe_iff {M N : Subgraph G} {v w : V} :
    s(v, w) ∈ M.spanningCoe.edgeSet ∆ N.spanningCoe.edgeSet ↔
      (M.Adj v w ∨ N.Adj v w) ∧ ¬ (M.Adj v w ∧ N.Adj v w) := by
  -- Expand the symmetric-difference edge predicate to the xor description used in the source proof.
  constructor
  · intro h
    simp [symmDiff_def, Subgraph.mem_edgeSet] at h
    rcases h with ⟨hMvw, hNvw⟩ | ⟨hNvw, hMvw⟩
    · exact ⟨Or.inl hMvw, fun hBoth ↦ hNvw hBoth.2⟩
    · exact ⟨Or.inr hNvw, fun hBoth ↦ hMvw hBoth.1⟩
  · intro h
    rcases h.1 with hMvw | hNvw
    · exact Or.inl ⟨hMvw, fun hNvw ↦ h.2 ⟨hMvw, hNvw⟩⟩
    · exact Or.inr ⟨hNvw, fun hMvw ↦ h.2 ⟨hMvw, hNvw⟩⟩

/-- Helper for Theorem 4.20: the symmetric difference of two matchings is alternating with
respect to the first matching. -/
lemma matching_symmDiff_is_alternating {M N : Subgraph G}
    (hM : M.IsMatching) (hN : N.IsMatching) :
    (M.spanningCoe ∆ N.spanningCoe).IsAlternating M.spanningCoe := by
  intro v w w' hww' hvw hvw'
  -- Two distinct symmetric-difference neighbors of one vertex cannot both come from the same
  -- matching, because matchings give each vertex a unique incident edge.
  have hxor : (M.Adj v w ∨ N.Adj v w) ∧ ¬ (M.Adj v w ∧ N.Adj v w) := by
    simpa [Subgraph.mem_edgeSet] using
      (mem_symmDiff_spanningCoe_iff (M := M) (N := N) (v := v) (w := w)).mp hvw
  have hxor' : (M.Adj v w' ∨ N.Adj v w') ∧ ¬ (M.Adj v w' ∧ N.Adj v w') := by
    simpa [Subgraph.mem_edgeSet] using
      (mem_symmDiff_spanningCoe_iff (M := M) (N := N) (v := v) (w := w')).mp hvw'
  have hM_iff : M.Adj v w ↔ ¬ M.Adj v w' := by
    constructor
    · intro hMv
      intro hMw'
      exact hww' (hM.eq_of_adj_left hMv hMw')
    · intro hnot
      rcases hxor.1 with hMv | hNv
      · exact hMv
      · exfalso
        have hNw' : ¬ N.Adj v w' := by
          intro hNw'
          exact hww' (hN.eq_of_adj_left hNv hNw')
        rcases hxor'.1 with hMw' | hNalt
        · exact hnot hMw'
        · exact hNw' hNalt
  simpa [Subgraph.spanningCoe_adj] using hM_iff

/-- Helper for Theorem 4.20: every vertex of the symmetric difference of two matchings has at most
two neighbors. -/
lemma matching_symmDiff_neighborSet_ncard_le_two [Finite V] {M N : Subgraph G}
    (hM : M.IsMatching) (hN : N.IsMatching) (v : V) :
    ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).ncard ≤ 2 := by
  classical
  by_contra hgt
  have hthree : 2 < ((M.spanningCoe ∆ N.spanningCoe).neighborSet v).ncard := by
    exact lt_of_not_ge hgt
  obtain ⟨w, hw, w', hw', z, hz, hww', hwz, hw'z⟩ :=
    (Set.two_lt_ncard (s := (M.spanningCoe ∆ N.spanningCoe).neighborSet v)).mp hthree
  have halt := matching_symmDiff_is_alternating (M := M) (N := N) hM hN
  have hmww' : M.spanningCoe.Adj v w ↔ ¬ M.spanningCoe.Adj v w' := halt hww' hw hw'
  have hmwz : M.spanningCoe.Adj v w ↔ ¬ M.spanningCoe.Adj v z := halt hwz hw hz
  have hmw'z : M.spanningCoe.Adj v w' ↔ ¬ M.spanningCoe.Adj v z := halt hw'z hw' hz
  by_cases hMw : M.spanningCoe.Adj v w
  · have hMw' : ¬ M.spanningCoe.Adj v w' := (hmww'.mp hMw)
    have hMz : ¬ M.spanningCoe.Adj v z := (hmwz.mp hMw)
    have hMw'' : M.spanningCoe.Adj v w' := hmw'z.mpr hMz
    exact hMw' hMw''
  · have hMw' : M.spanningCoe.Adj v w' := by
      by_contra hMw''
      exact hMw (hmww'.mpr hMw'')
    have hMz : M.spanningCoe.Adj v z := by
      by_contra hMz'
      exact hMw (hmwz.mpr hMz')
    exact hw'z (hM.eq_of_adj_left hMw' hMz)

/-- Helper for Theorem 4.20: a matching covers exactly twice as many vertices as it has edges. -/
lemma matching_verts_ncard_eq_two_mul_edgeSet_ncard [Finite V] {K : Subgraph G}
    (hK : K.IsMatching) :
    K.verts.ncard = 2 * K.edgeSet.ncard := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  -- On a matching, each covered vertex has degree `1` and each uncovered vertex has degree `0`.
  have hdeg : ∀ v : V, K.spanningCoe.degree v = if v ∈ K.verts then 1 else 0 := by
    intro v
    by_cases hv : v ∈ K.verts
    · have hdegK : K.degree v = 1 :=
        (SimpleGraph.Subgraph.isMatching_iff_forall_degree (M := K)).mp hK v hv
      simp [hv, Subgraph.degree_spanningCoe, hdegK]
    · have hdegK : K.degree v = 0 := K.degree_of_notMem_verts hv
      simp [hv, Subgraph.degree_spanningCoe, hdegK]
  have hsum : Fintype.card K.verts = 2 * Fintype.card K.spanningCoe.edgeSet := by
    -- Summing the degree function counts exactly the covered vertices, then the handshaking lemma
    -- converts the total degree into twice the number of matching edges.
    calc
      Fintype.card K.verts = ∑ v : V, K.spanningCoe.degree v := by
        rw [Fintype.card_subtype]
        rw [Finset.card_eq_sum_ones]
        simpa [hdeg]
      _ = 2 * K.spanningCoe.edgeFinset.card := K.spanningCoe.sum_degrees_eq_twice_card_edges
      _ = 2 * Fintype.card K.spanningCoe.edgeSet := by
        simpa using congrArg (fun n : ℕ ↦ 2 * n) K.spanningCoe.edgeFinset_card
  have hsum' : Nat.card K.verts = 2 * Nat.card K.spanningCoe.edgeSet := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hsum
  -- Convert the finite-cardinality identity back to `Set.ncard` and the original subgraph.
  calc
    K.verts.ncard = Nat.card K.verts := by rw [Nat.card_coe_set_eq]
    _ = 2 * Nat.card K.spanningCoe.edgeSet := hsum'
    _ = 2 * K.spanningCoe.edgeSet.ncard := by rw [Nat.card_coe_set_eq]
    _ = 2 * K.edgeSet.ncard := by rw [Subgraph.edgeSet_spanningCoe]

/-- Helper for Theorem 4.20: augmenting along an augmenting path yields a larger matching of `G`. -/
lemma exists_larger_matching_of_augmenting_path [Finite V] {M : Subgraph G} (hM : M.IsMatching)
    {u v : V} {p : G.Walk u v} (hp : IsMatchingAugmenting M p) :
    ∃ N : Subgraph G, N.IsMatching ∧ M.edgeSet.ncard < N.edgeSet.ncard := by
  let N := Walk.augment_matching M p
  have hN : N.IsMatching := Walk.augment_matching_isMatching hM hp
  have hcard : N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
    simpa [N] using Walk.ncard_edgeSet_augment_matching (M := M) (p := p) hM hp
  refine ⟨N, hN, ?_⟩
  -- The augmented matching has exactly one more edge, hence in particular strictly more edges.
  omega

/-- Helper for Theorem 4.20: a strictly larger matching should yield an augmenting path via the
textbook symmetric-difference decomposition into paths and cycles. -/
lemma exists_augmenting_path_of_exists_larger_matching [Finite V] {M N : Subgraph G}
    (hM : M.IsMatching) (hN : N.IsMatching) (hMN : M.edgeSet.ncard < N.edgeSet.ncard) :
    ∃ (u v : V) (p : G.Walk u v), IsMatchingAugmenting M p := by
  classical
  -- TODO: Follow the source proof in `H := M.spanningCoe ∆ N.spanningCoe`.
  -- First show every vertex of `H` has at most two incident edges, because `M` and `N` are
  -- matchings. Then decompose each nontrivial connected component of `H` into either a cycle or a
  -- spanning path, observe that cycle components contribute equally many `M`- and `N`-edges, and
  -- finally choose a path component with one extra `N`-edge; its endpoints are uncovered by `M`,
  -- so the corresponding walk is `M`-augmenting.
  let H : SimpleGraph V := M.spanningCoe ∆ N.spanningCoe
  have hHalt : H.IsAlternating M.spanningCoe := by
    simpa [H] using matching_symmDiff_is_alternating (M := M) (N := N) hM hN
  have hHdeg : ∀ v : V, (H.neighborSet v).ncard ≤ 2 := by
    intro v
    simpa [H] using matching_symmDiff_neighborSet_ncard_le_two (M := M) (N := N) hM hN v
  have hMverts : M.verts.ncard = 2 * M.edgeSet.ncard :=
    matching_verts_ncard_eq_two_mul_edgeSet_ncard (K := M) hM
  have hNverts : N.verts.ncard = 2 * N.edgeSet.ncard :=
    matching_verts_ncard_eq_two_mul_edgeSet_ncard (K := N) hN
  -- Route correction: the remaining gap is not the local xor/degree bookkeeping but the global
  -- component-selection step turning `|N| > |M|` into a path component of `H` with `N`-surplus.
  -- That step still needs the connected-component edge-count partition formalized.
  -- TODO: Localize the strict edge-count surplus to one connected component of `H`, show that a
  -- surplus component cannot be a cycle using `matching_verts_ncard_eq_two_mul_edgeSet_ncard`, and
  -- then map a spanning path of that component back to an `M`-augmenting walk in `G`.
  sorry

/-- A matching of `G` has maximum cardinality when no other matching of `G` uses more edges. -/
@[mk_iff]
structure IsMaximumCardinalityMatching [Finite V] (M : Subgraph G) : Prop where
  isMatching : M.IsMatching
  maximum (N : Subgraph G) (_ : N.IsMatching) : N.edgeSet.ncard ≤ M.edgeSet.ncard

/-- A finite graph admits a maximum-cardinality matching. -/
theorem exists_isMaximumCardinalityMatching [Finite V] :
    ∃ M : G.Subgraph, M.IsMaximumCardinalityMatching := by
  classical
  letI : Fintype G.Subgraph := Fintype.ofFinite _
  have hbot : (⊥ : G.Subgraph).IsMatching := by
    intro v hv
    simp at hv
  let admissible : Finset G.Subgraph :=
    (Finset.univ : Finset G.Subgraph).filter fun M ↦ M.IsMatching
  have hadmissible : admissible.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [admissible, hbot]
  obtain ⟨M, hMmem, hMmax⟩ :=
    admissible.exists_max_image (fun M ↦ M.edgeSet.ncard) hadmissible
  refine ⟨M, ?_⟩
  refine ⟨(Finset.mem_filter.mp hMmem).2, ?_⟩
  intro N hN
  have hNmem : N ∈ admissible := by
    simp [admissible, hN]
  exact hMmax N hNmem

/-- Theorem 4.20. A matching `M` has maximum cardinality if and only if there is no
`M`-augmenting path. -/
theorem matching_has_maximum_cardinality_iff_no_augmenting_path [Finite V] {M : Subgraph G}
    (hM : M.IsMatching) :
    M.IsMaximumCardinalityMatching ↔
      ¬ ∃ (u v : V) (p : G.Walk u v), IsMatchingAugmenting M p := by
  constructor
  · intro hmax hAug
    rcases hAug with ⟨u, v, p, hp⟩
    -- An augmenting path produces a larger matching, contradicting maximality.
    rcases exists_larger_matching_of_augmenting_path hM hp with ⟨N, hN, hlt⟩
    exact Nat.not_lt_of_ge (hmax.maximum N hN) hlt
  · intro hNoAug
    refine ⟨hM, ?_⟩
    intro N hN
    by_contra hle
    have hlt : M.edgeSet.ncard < N.edgeSet.ncard := lt_of_not_ge hle
    -- The source-proof converse extracts an augmenting path from any strictly larger matching.
    exact hNoAug (exists_augmenting_path_of_exists_larger_matching hM hN hlt)

end Subgraph

end SimpleGraph
