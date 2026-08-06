import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Sym.Sym2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_2_7

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall via `lean_leansearch`: mathlib proves the combinatorial tree-count identity
-- for `SimpleGraph.IsTree`; this chapter's `IsTree boundary` is a realization-level notion, so
-- the source-facing statement stays on `boundary` in explicit vertex-minus-edge form.

/-- Helper for Lemma 4.4.2: in a realized tree, an unordered endpoint pair comes from a unique
edge index. -/
theorem boundaryEdgeIndex_eq_of_sym2_eq
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] {j j' : J}
    (h :
      Sym2.mk (boundary j 0) (boundary j 1) =
        Sym2.mk (boundary j' 0) (boundary j' 1)) :
    j = j' := by
  -- Either the ordered endpoint maps agree, or the swapped case creates a closed reduced
  -- two-edge loop, impossible in a tree.
  rcases Sym2.eq_iff.mp h with hdir | hrev
  · apply boundary.injective
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact hdir.1
    · exact hdir.2
  · let p : EdgePath boundary :=
      { length := 1
        toEdge := fun
          | ⟨0, _⟩ => ⟨j, .forward⟩
          | ⟨1, _⟩ => ⟨j', .forward⟩
        composable := fun m => by
          have hm : m = 0 := by omega
          subst hm
          calc
            (⟨j', .forward⟩ : OrientedEdge boundary).initialVertex
                = graphVertex boundary (boundary j' 0) := by simp
            _ = graphVertex boundary (boundary j 1) := by simp [hrev.2]
            _ = (⟨j, .forward⟩ : OrientedEdge boundary).terminalVertex := by simp }
    have hpClosed : p.IsClosed := by
      -- The swapped endpoint identification closes the two-edge loop.
      change (⟨j, .forward⟩ : OrientedEdge boundary).initialVertex =
        (⟨j', .forward⟩ : OrientedEdge boundary).terminalVertex
      calc
        (⟨j, .forward⟩ : OrientedEdge boundary).initialVertex
            = graphVertex boundary (boundary j 0) := by simp
        _ = graphVertex boundary (boundary j' 1) := by simp [hrev.1]
        _ = (⟨j', .forward⟩ : OrientedEdge boundary).terminalVertex := by simp
    have hpReduced : p.Reduced := by
      -- Two consecutive forward traversals cannot be reverses of one another.
      intro m
      change Fin 1 at m
      have hm : m = 0 := Fin.eq_zero m
      subst hm
      change (⟨j', .forward⟩ : OrientedEdge boundary) ≠
        (⟨j, .forward⟩ : OrientedEdge boundary).reverse
      intro hEq
      have horient : EdgeOrientation.forward = EdgeOrientation.forward.reverse := by
        simpa using congrArg OrientedEdge.orientation hEq
      simp [EdgeOrientation.reverse] at horient
    exact False.elim <|
      IsTree.not_reduced_of_isClosed (boundary := boundary) p hpClosed hpReduced

/-- Helper for Lemma 4.4.2: the auxiliary simple graph `boundaryGraph boundary` has exactly one
edge-set element for each source edge index `j : J`. -/
theorem boundaryGraph_card_edgeSet_eq_card_edges
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] :
    Nat.card (boundaryGraph boundary).edgeSet = Nat.card J := by
  classical
  -- Transport the source edge index set to the auxiliary graph edge set by unordered endpoints.
  let edgeToEdgeSet : J → (boundaryGraph boundary).edgeSet := fun j ↦
    ⟨Sym2.mk (boundary j 0) (boundary j 1), by
      rw [SimpleGraph.mem_edgeSet]
      exact ⟨boundary_ne_endpoints boundary j, ⟨j, rfl⟩⟩⟩
  have hedgeToEdgeSet_injective : Function.Injective edgeToEdgeSet := by
    intro j j' h
    exact
      boundaryEdgeIndex_eq_of_sym2_eq boundary
        (congrArg Subtype.val h)
  have hedgeToEdgeSet_surjective : Function.Surjective edgeToEdgeSet := by
    intro e
    -- Recover the unique source edge whose unordered endpoints represent `e`.
    have hadj : (boundaryGraph boundary).Adj e.1.out.1 e.1.out.2 := by
      rw [← SimpleGraph.mem_edgeSet]
      simpa [e.1.out_eq] using e.property
    rcases (boundaryGraph_adj_iff boundary e.1.out.1 e.1.out.2).mp hadj with ⟨_, ⟨j, hj⟩⟩
    refine ⟨j, Subtype.ext ?_⟩
    exact hj.trans e.1.out_eq
  rw [Nat.card_congr (Equiv.ofBijective edgeToEdgeSet
    ⟨hedgeToEdgeSet_injective, hedgeToEdgeSet_surjective⟩)]

/-- Helper for Lemma 4.4.2: the auxiliary simple graph attached to a realized tree is acyclic. -/
theorem boundaryGraph_isAcyclic_of_isTree
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] :
    (boundaryGraph boundary).IsAcyclic := by
  intro u w hw
  -- Translate a graph cycle into the forbidden source-level closed reduced edge path.
  rcases exists_closedReducedEdgePath_of_boundaryGraph_cycle boundary w hw with
    ⟨p, hpClosed, hpReduced⟩
  exact IsTree.not_reduced_of_isClosed (boundary := boundary) p hpClosed hpReduced

/-- Lemma 4.4.2. Every finite realized tree satisfies the canonical cardinality identity
`Nat.card J + 1 = Nat.card X₀`, equivalently Euler characteristic `1`. -/
theorem card_edges_add_one_eq_card_vertices_of_isTree
    (boundary : J ↪ Fin 2 → X₀) [FiniteGraph boundary] [IsTree boundary] :
    Nat.card J + 1 = Nat.card X₀ := by
  -- Route correction: the earlier blocker was the missing `boundaryGraph_connected` bridge;
  -- with that dependency available again, the proof reduces to the canonical simple-graph tree
  -- counting theorem.
  let G := boundaryGraph boundary
  let _ : Finite X₀ := FiniteGraph.finiteVertices (boundary := boundary)
  have hGConnected : G.Connected := by
    simpa [G] using boundaryGraph_connected boundary
  have hGAcyclic : G.IsAcyclic := by
    simpa [G] using boundaryGraph_isAcyclic_of_isTree boundary
  have hGTree : G.IsTree := ⟨hGConnected, hGAcyclic⟩
  have hcard : Nat.card G.edgeSet + 1 = Nat.card X₀ :=
    (G.isTree_iff_connected_and_card.mp hGTree).2
  -- Rewrite the auxiliary graph edge count back to the original edge index type `J`.
  calc
    Nat.card J + 1 = Nat.card G.edgeSet + 1 := by
      rw [boundaryGraph_card_edgeSet_eq_card_edges boundary]
    _ = Nat.card X₀ := hcard

/-- Helper for Lemma 4.4.2: the explicit Euler-characteristic formulation of the tree-count
identity for a finite graph realization `boundary : J ↪ Fin 2 → X₀`. -/
theorem eulerCharacteristic_eq_one_of_isTree
    (boundary : J ↪ Fin 2 → X₀) [FiniteGraph boundary] [IsTree boundary] :
    (Nat.card X₀ : Int) - Nat.card J = 1 := by
  -- Recast the natural-number tree identity as an integer equality.
  have hcard : Nat.card J + 1 = Nat.card X₀ :=
    card_edges_add_one_eq_card_vertices_of_isTree boundary
  -- Rearranging the cast equality gives the explicit Euler-characteristic formula.
  refine sub_eq_iff_eq_add.mpr ?_
  simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
    congrArg (fun n : ℕ ↦ (n : Int)) hcard.symm
