import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4.FiniteGraph
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_2_7.BoundaryGraph
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Lemma_4_2_7.SourceFaithfulTree

open scoped unitInterval
open SimpleGraph
open Set Filter Topology

universe u v

variable {X₀ : Type u} {J : Type v}

/-- Helper for Lemma 4.2.7: in a realized tree, each source edge has distinct endpoints, since a
degenerate edge would already give a closed reduced edge path. -/
theorem boundary_ne_endpoints_of_isTree (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (j : J) :
    boundary j 0 ≠ boundary j 1 := by
  -- A degenerate edge would itself be a closed reduced edge path, contradicting the tree axiom.
  intro hdeg
  let p : EdgePath boundary :=
    { length := 0
      toEdge := fun _ ↦ ⟨j, .forward⟩
      composable := fun m ↦ Fin.elim0 m }
  have hpClosed : p.IsClosed := by
    simp [EdgePath.IsClosed, EdgePath.initialVertex, EdgePath.terminalVertex, p, hdeg]
  have hpReduced : p.Reduced := by
    intro m
    exact Fin.elim0 m
  exact ‹IsTree boundary›.not_reduced_of_isClosed p hpClosed hpReduced

/-- Helper for Lemma 4.2.7: in a tree, an unordered endpoint pair determines at most one source
edge. Two distinct source edges with the same endpoints would already form a closed reduced
two-edge path. -/
theorem boundary_eq_of_sym2_eq_of_isTree
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] {j k : J}
    (hjk : Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk (boundary k 0) (boundary k 1)) :
    j = k := by
  classical
  by_cases hEq : j = k
  · exact hEq
  · rcases Sym2.eq_iff.mp hjk with hdir | hrev
    · let p : EdgePath boundary :=
        { length := 1
          toEdge := fun
            | ⟨0, _⟩ => ⟨j, .forward⟩
            | ⟨1, _⟩ => ⟨k, .backward⟩
          composable := by
            intro m
            fin_cases m
            simp [hdir.2] }
      have hpZero : p 0 = ⟨j, .forward⟩ := by
        rfl
      have hpLast : p (Fin.last 1) = ⟨k, .backward⟩ := by
        rfl
      have hpClosed : p.IsClosed := by
        -- The second edge traverses the same endpoints in reverse, so the two-edge path closes.
        rw [EdgePath.isClosed_iff, EdgePath.initialVertex_apply_zero, EdgePath.terminalVertex_apply_last,
          hpZero, hpLast]
        simpa [hdir.1]
      have hpReduced : p.Reduced := by
        -- Distinct parallel edges do not immediately backtrack, so the resulting loop is reduced.
        intro m
        fin_cases m
        intro hBacktrack
        have hEdge : k = j := by
          simpa [p] using congrArg OrientedEdge.edge hBacktrack
        exact hEq hEdge.symm
      exact (‹IsTree boundary›.not_reduced_of_isClosed p hpClosed hpReduced).elim
    · let p : EdgePath boundary :=
        { length := 1
          toEdge := fun
            | ⟨0, _⟩ => ⟨j, .forward⟩
            | ⟨1, _⟩ => ⟨k, .forward⟩
          composable := by
            intro m
            fin_cases m
            simp [hrev.2] }
      have hpZero : p 0 = ⟨j, .forward⟩ := by
        rfl
      have hpLast : p (Fin.last 1) = ⟨k, .forward⟩ := by
        rfl
      have hpClosed : p.IsClosed := by
        -- In the swapped-endpoint case, traversing both edges forward still returns to the start.
        rw [EdgePath.isClosed_iff, EdgePath.initialVertex_apply_zero, EdgePath.terminalVertex_apply_last,
          hpZero, hpLast]
        simpa [hrev.1]
      have hpReduced : p.Reduced := by
        -- The two forward traversals cannot be reverse to one another.
        intro m
        fin_cases m
        intro hBacktrack
        have hOrient :
            (⟨k, .forward⟩ : OrientedEdge boundary).orientation =
              (⟨j, .forward⟩ : OrientedEdge boundary).reverse.orientation := by
          simpa [p] using congrArg OrientedEdge.orientation hBacktrack
        cases hOrient
      exact (‹IsTree boundary›.not_reduced_of_isClosed p hpClosed hpReduced).elim

/-- Helper for Lemma 4.2.7: an adjacency in `boundaryGraph boundary` determines the corresponding
path between the endpoint vertices in the default realization topology. -/
theorem boundaryGraphAdjPathDefault (boundary : J ↪ Fin 2 → X₀) {u v : X₀}
    (h : (boundaryGraph boundary).Adj u v) :
    Nonempty (_root_.Path (graphVertex boundary u) (graphVertex boundary v)) := by
  classical
  change u ≠ v ∧ ∃ j : J, Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk u v at h
  let j : J := Classical.choose h.2
  let hj : Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk u v := Classical.choose_spec h.2
  by_cases h0 : boundary j 0 = u
  · have h1 : boundary j 1 = v := by
      have hor :
          (boundary j 0 = u ∧ boundary j 1 = v) ∨
            (boundary j 0 = v ∧ boundary j 1 = u) :=
        Sym2.eq_iff.mp hj
      rcases hor with hdir | hrev
      · exact hdir.2
      · exact (h.1 (h0.symm.trans hrev.1)).elim
    refine ⟨
      { toFun := graphEdgePoint boundary j
        continuous_toFun := ?_
        source' := ?_
        target' := ?_ }⟩
    · let _ : TopologicalSpace X₀ := ⊥
      let _ : TopologicalSpace J := ⊥
      have hsource :
          Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) := by
        simpa using
          (continuous_inr.comp
            (continuous_const.prodMk continuous_id) :
              Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))))
      simpa [graphEdgePoint, graphRealizationPoint] using continuous_quotient_mk'.comp hsource
    · simpa [h0] using (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm
    · simpa [h1] using (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm
  · have h0' : boundary j 0 = v := by
      have hor :
          (boundary j 0 = u ∧ boundary j 1 = v) ∨
            (boundary j 0 = v ∧ boundary j 1 = u) :=
        Sym2.eq_iff.mp hj
      rcases hor with hdir | hrev
      · exact (h0 hdir.1).elim
      · exact hrev.1
    have h1' : boundary j 1 = u := by
      have hor :
          (boundary j 0 = u ∧ boundary j 1 = v) ∨
            (boundary j 0 = v ∧ boundary j 1 = u) :=
        Sym2.eq_iff.mp hj
      rcases hor with hdir | hrev
      · exact (h0 hdir.1).elim
      · exact hrev.2
    refine ⟨
      { toFun := fun t ↦ graphEdgePoint boundary j (σ t)
        continuous_toFun := ?_
        source' := ?_
        target' := ?_ }⟩
    · let _ : TopologicalSpace X₀ := ⊥
      let _ : TopologicalSpace J := ⊥
      have hsource :
          Continuous (fun t : I ↦ (Sum.inr (j, σ t) : X₀ ⊕ (J × I))) := by
        simpa using
          (continuous_inr.comp
            (continuous_const.prodMk unitInterval.continuous_symm) :
              Continuous (fun t : I ↦ (Sum.inr (j, σ t) : X₀ ⊕ (J × I))))
      simpa [graphEdgePoint, graphRealizationPoint] using continuous_quotient_mk'.comp hsource
    · simpa [h1'] using (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm
    · simpa [h0'] using (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

/-- Helper for Lemma 4.2.7: a walk in `boundaryGraph boundary` induces a realization path in the
default topology by traversing the corresponding edges in order. -/
noncomputable def boundaryGraphWalkPathDefaultPath (boundary : J ↪ Fin 2 → X₀) {u v : X₀} :
    (boundaryGraph boundary).Walk u v →
      _root_.Path (graphVertex boundary u) (graphVertex boundary v)
  | .nil =>
      _root_.Path.refl _
  | .cons h p =>
      (Classical.choice <| boundaryGraphAdjPathDefault boundary h).trans
        (boundaryGraphWalkPathDefaultPath boundary p)

/-- Helper for Lemma 4.2.7: a walk in `boundaryGraph boundary` induces a realization path in the
default topology by traversing the corresponding edges in order. -/
theorem boundaryGraphWalkPathDefault (boundary : J ↪ Fin 2 → X₀) {u v : X₀} :
    (boundaryGraph boundary).Walk u v →
      Nonempty (_root_.Path (graphVertex boundary u) (graphVertex boundary v)) := by
  intro w
  -- The recursive path construction already packages the realized walk as a genuine path.
  exact ⟨boundaryGraphWalkPathDefaultPath boundary w⟩

/-- Helper for Lemma 4.2.7: a default-topology tree realization still has a genuine vertex
representative. -/
theorem nonempty_vertex_of_isTreeDefault (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] :
    Nonempty X₀ := by
  let _ : Nonempty (graphRealization boundary) := inferInstance
  rcases ‹Nonempty (graphRealization boundary)› with ⟨x⟩
  refine Quotient.inductionOn x ?_
  intro z
  cases z with
  | inl x => exact ⟨x⟩
  | inr jt => exact ⟨boundary jt.1 0⟩

/-- Helper for Lemma 4.2.7: the two endpoints of each source edge lie in the same connected
component of `boundaryGraph boundary`. -/
theorem boundaryGraph_endpointComponentEqOfIsTree
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) :
    (boundaryGraph boundary).connectedComponentMk (boundary j 0) =
      (boundaryGraph boundary).connectedComponentMk (boundary j 1) := by
  -- The source edge `j` itself witnesses adjacency between its endpoints in `boundaryGraph`.
  exact ConnectedComponent.connectedComponentMk_eq_of_adj
    ⟨boundary_ne_endpoints_of_isTree boundary j, ⟨j, rfl⟩⟩

/-- Helper for Lemma 4.2.7: orient an adjacency in `boundaryGraph boundary` by a source edge whose
realized endpoints are the two adjacent vertices, while recording the underlying unoriented edge
data needed later for cycle arguments. -/
theorem boundaryGraph_adj_exists_orientedEdge_spec
    (boundary : J ↪ Fin 2 → X₀) {u v : X₀} (h : (boundaryGraph boundary).Adj u v) :
    ∃ k : OrientedEdge boundary,
      k.initialVertex = graphVertex boundary u ∧
        k.terminalVertex = graphVertex boundary v ∧
          Sym2.mk (boundary k.edge 0) (boundary k.edge 1) = Sym2.mk u v := by
  -- Unpack the adjacency witness and orient the underlying source edge to match `u` and `v`.
  rcases (boundaryGraph_adj_iff boundary u v).mp h with ⟨_, ⟨j, hj⟩⟩
  rcases Sym2.eq_iff.mp hj with hdir | hrev
  · refine ⟨⟨j, .forward⟩, ?_⟩
    refine ⟨?_, ?_, hj⟩
    · rw [OrientedEdge.initialVertex_forward, hdir.1]
    · rw [OrientedEdge.terminalVertex_forward, hdir.2]
  · refine ⟨⟨j, .backward⟩, ?_⟩
    refine ⟨?_, ?_, hj⟩
    · rw [OrientedEdge.initialVertex_backward, hrev.2]
    · rw [OrientedEdge.terminalVertex_backward, hrev.1]

/-- Helper for Lemma 4.2.7: a cycle in `boundaryGraph boundary` yields a closed reduced source
`EdgePath boundary`. -/
theorem exists_closedReducedEdgePath_of_boundaryGraph_cycle
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] {u : X₀}
    (w : (boundaryGraph boundary).Walk u u) (hw : w.IsCycle) :
    ∃ p : EdgePath boundary, p.IsClosed ∧ p.Reduced := by
  classical
  have hlen : 0 < w.length := by
    simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hw.not_nil
  let edgeAt : ∀ n : ℕ, n < w.length → OrientedEdge boundary := fun n hn ↦
    Classical.choose <|
      boundaryGraph_adj_exists_orientedEdge_spec boundary
        (w.adj_getVert_succ hn)
  have edgeAt_initial :
      ∀ n : ℕ, ∀ hn : n < w.length,
        (edgeAt n hn).initialVertex = graphVertex boundary (w.getVert n) := by
    intro n hn
    exact
      (Classical.choose_spec <|
        boundaryGraph_adj_exists_orientedEdge_spec boundary
          (w.adj_getVert_succ hn)).1
  have edgeAt_terminal :
      ∀ n : ℕ, ∀ hn : n < w.length,
        (edgeAt n hn).terminalVertex = graphVertex boundary (w.getVert (n + 1)) := by
    intro n hn
    exact
      (Classical.choose_spec <|
        boundaryGraph_adj_exists_orientedEdge_spec boundary
          (w.adj_getVert_succ hn)).2.1
  have edgeAt_sym2 :
      ∀ n : ℕ, ∀ hn : n < w.length,
        Sym2.mk (boundary (edgeAt n hn).edge 0) (boundary (edgeAt n hn).edge 1) =
          Sym2.mk (w.getVert n) (w.getVert (n + 1)) := by
    intro n hn
    exact
      (Classical.choose_spec <|
        boundaryGraph_adj_exists_orientedEdge_spec boundary
          (w.adj_getVert_succ hn)).2.2
  have pathIndex_lt_length :
      ∀ n : Fin ((w.length - 1) + 1), (n : ℕ) < w.length := by
    intro n
    have hn : (n : ℕ) ≤ w.length - 1 := by
      simpa using n.isLt
    exact Nat.lt_of_le_of_lt hn (Nat.pred_lt (Nat.ne_of_gt hlen))
  let pathToEdge : Fin ((w.length - 1) + 1) → OrientedEdge boundary := fun n ↦
    edgeAt n (pathIndex_lt_length n)
  have pathComposable :
      ∀ m : Fin (w.length - 1),
        (pathToEdge m.succ).initialVertex =
          (pathToEdge (Fin.castSucc m)).terminalVertex := by
    intro m
    have hm0 : (m : ℕ) < w.length :=
      pathIndex_lt_length (Fin.castSucc m)
    have hm1 : (m : ℕ) + 1 < w.length :=
      pathIndex_lt_length m.succ
    -- Consecutive chosen edges meet at the shared walk vertex `w.getVert (m + 1)`.
    calc
      (pathToEdge m.succ).initialVertex
          = graphVertex boundary (w.getVert ((m : ℕ) + 1)) := by
            simpa [pathToEdge] using edgeAt_initial ((m : ℕ) + 1) hm1
      _ = (pathToEdge (Fin.castSucc m)).terminalVertex := by
            simpa [pathToEdge] using (edgeAt_terminal (m : ℕ) hm0).symm
  let p : EdgePath boundary :=
    { length := w.length - 1
      toEdge := pathToEdge
      composable := pathComposable }
  refine ⟨p, ?_, ?_⟩
  · -- The cycle starts and ends at `u`, so the induced source path is closed.
    change (pathToEdge 0).initialVertex =
      (pathToEdge (Fin.last (w.length - 1))).terminalVertex
    have hlast : w.length - 1 < w.length := Nat.pred_lt (Nat.ne_of_gt hlen)
    have hstart : (pathToEdge 0).initialVertex = graphVertex boundary u := by
      simpa [pathToEdge] using edgeAt_initial 0 hlen
    have hend : (pathToEdge (Fin.last (w.length - 1))).terminalVertex = graphVertex boundary u := by
      have hget : w.getVert (w.length - 1 + 1) = u := by
        calc
          w.getVert (w.length - 1 + 1) = w.getVert w.length := by
            exact congrArg w.getVert (Nat.succ_pred_eq_of_pos hlen)
          _ = u := w.getVert_length
      calc
        (pathToEdge (Fin.last (w.length - 1))).terminalVertex
            = graphVertex boundary (w.getVert (w.length - 1 + 1)) := by
              simpa [pathToEdge] using edgeAt_terminal (w.length - 1) hlast
        _ = graphVertex boundary u := by rw [hget]
    exact hstart.trans hend.symm
  · -- Immediate backtracking would repeat an edge of the cycle walk, contradicting `w.IsTrail`.
    intro m
    have htrail : w.IsTrail := (SimpleGraph.Walk.isCycle_def w).mp hw |>.1
    have hm0 : (m : ℕ) < w.length :=
      pathIndex_lt_length (Fin.castSucc m)
    have hm1 : (m : ℕ) + 1 < w.length :=
      pathIndex_lt_length m.succ
    have hm0edges : (m : ℕ) < w.edges.length := by
      simpa [SimpleGraph.Walk.length_edges] using hm0
    have hm1edges : (m : ℕ) + 1 < w.edges.length := by
      simpa [SimpleGraph.Walk.length_edges] using hm1
    intro hreverse
    have hedge :
        (pathToEdge m.succ).edge = (pathToEdge (Fin.castSucc m)).edge := by
      simpa [pathToEdge] using congrArg OrientedEdge.edge hreverse
    have hsym2 :
        Sym2.mk (w.getVert ((m : ℕ) + 1)) (w.getVert ((m : ℕ) + 2)) =
          Sym2.mk (w.getVert (m : ℕ)) (w.getVert ((m : ℕ) + 1)) := by
      -- Reversing a chosen oriented edge preserves its underlying unordered source edge.
      calc
        Sym2.mk (w.getVert ((m : ℕ) + 1)) (w.getVert ((m : ℕ) + 2))
            =
              Sym2.mk
                (boundary (pathToEdge m.succ).edge 0)
                (boundary (pathToEdge m.succ).edge 1) := by
              simpa [pathToEdge] using (edgeAt_sym2 ((m : ℕ) + 1) hm1).symm
        _ = Sym2.mk (boundary (pathToEdge (Fin.castSucc m)).edge 0)
              (boundary (pathToEdge (Fin.castSucc m)).edge 1) := by
              rw [hedge]
        _ = Sym2.mk (w.getVert (m : ℕ)) (w.getVert ((m : ℕ) + 1)) := by
              simpa [pathToEdge] using edgeAt_sym2 (m : ℕ) hm0
    have hedges :
        w.edges[m] = w.edges[(m : ℕ) + 1] := by
      calc
        w.edges[m] = Sym2.mk (w.getVert (m : ℕ)) (w.getVert ((m : ℕ) + 1)) := by
          simpa using walk_edges_getElem_eq_sym2 w (m : ℕ) hm0edges
        _ = Sym2.mk (w.getVert ((m : ℕ) + 1)) (w.getVert ((m : ℕ) + 2)) := hsym2.symm
        _ = w.edges[(m : ℕ) + 1] := by
          simpa using (walk_edges_getElem_eq_sym2 w ((m : ℕ) + 1) hm1edges).symm
    have hmEq : (m : ℕ) = (m : ℕ) + 1 :=
      (List.Nodup.getElem_inj_iff htrail.edges_nodup).mp hedges
    exact (Nat.ne_of_lt (Nat.lt_succ_self (m : ℕ)) hmEq).elim

/-- Helper for Lemma 4.2.7: the auxiliary simple graph attached to a realized tree is acyclic. -/
theorem boundaryGraph_isAcyclicOfIsTree
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] :
    (boundaryGraph boundary).IsAcyclic := by
  intro u w hw
  -- Translate a graph cycle into the forbidden source-level closed reduced edge path.
  rcases exists_closedReducedEdgePath_of_boundaryGraph_cycle boundary w hw with
    ⟨p, hpClosed, hpReduced⟩
  exact ‹IsTree boundary›.not_reduced_of_isClosed p hpClosed hpReduced

/-- Helper for Lemma 4.2.7: connectedness of the auxiliary graph gives a realized edge path
between any two vertices of a tree. -/
theorem graphVertexJumpPath_exists
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (x v₀ : X₀) :
    Nonempty (_root_.Path (graphVertex boundary x) (graphVertex boundary v₀)) := by
  classical
  let w : (boundaryGraph boundary).Walk x v₀ :=
    Classical.choose ((boundaryGraph_connected boundary).exists_walk_length_eq_dist x v₀)
  exact ⟨boundaryGraphWalkPath boundary w⟩

/-- Helper for Lemma 4.2.7: choose the realized edge path from `x` to `v₀`. -/
noncomputable def graphVertexJumpPath
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (x v₀ : X₀) :
    _root_.Path (graphVertex boundary x) (graphVertex boundary v₀) :=
  Classical.choice (graphVertexJumpPath_exists boundary x v₀)

/-- Helper for Lemma 4.2.7: choose one vertex representative of each connected component of the
forest `boundaryGraph boundary`. -/
noncomputable def boundaryGraphComponentRoot
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (c : (boundaryGraph boundary).ConnectedComponent) : X₀ :=
  c.nonempty_supp.some

/-- Helper for Lemma 4.2.7: the chosen component root lies in the component it represents. -/
theorem boundaryGraphComponentRoot_mem
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (c : (boundaryGraph boundary).ConnectedComponent) :
    (boundaryGraph boundary).connectedComponentMk (boundaryGraphComponentRoot boundary c) = c :=
  c.nonempty_supp.some_mem

/-- Helper for Lemma 4.2.7: choose a shortest path in the forest component from the chosen root
to the given vertex. -/
noncomputable def boundaryGraphShortestWalkFromComponentRoot
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (x : X₀) :
    (boundaryGraph boundary).Walk
      (boundaryGraphComponentRoot boundary ((boundaryGraph boundary).connectedComponentMk x)) x :=
  Classical.choose <|
    (ConnectedComponent.eq.mp <|
      boundaryGraphComponentRoot_mem boundary
        ((boundaryGraph boundary).connectedComponentMk x)).exists_path_of_dist

/-- Helper for Lemma 4.2.7: the chosen component-root walk is a simple path. -/
theorem boundaryGraphShortestWalkFromComponentRoot_isPath
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (x : X₀) :
    (boundaryGraphShortestWalkFromComponentRoot boundary x).IsPath :=
  (Classical.choose_spec <|
    (ConnectedComponent.eq.mp <|
      boundaryGraphComponentRoot_mem boundary
        ((boundaryGraph boundary).connectedComponentMk x)).exists_path_of_dist).1

/-- Helper for Lemma 4.2.7: the chosen component-root walk has the expected combinatorial
distance length. -/
theorem boundaryGraphShortestWalkFromComponentRoot_length
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (x : X₀) :
    (boundaryGraphShortestWalkFromComponentRoot boundary x).length =
      (boundaryGraph boundary).dist
        (boundaryGraphComponentRoot boundary ((boundaryGraph boundary).connectedComponentMk x)) x :=
  (Classical.choose_spec <|
    (ConnectedComponent.eq.mp <|
      boundaryGraphComponentRoot_mem boundary
        ((boundaryGraph boundary).connectedComponentMk x)).exists_path_of_dist).2

/-- Helper for Lemma 4.2.7: traverse the chosen shortest component-root walk backwards, then use
the coarse vertex jump to the global basepoint `v₀`. -/
noncomputable def vertexPathToGlobalRoot
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ x : X₀) :
    _root_.Path (graphVertex boundary x) (graphVertex boundary v₀) :=
  (boundaryGraphWalkPathDefaultPath boundary
      (boundaryGraphShortestWalkFromComponentRoot boundary x)).symm.trans
    (graphVertexJumpPath boundary
      (boundaryGraphComponentRoot boundary ((boundaryGraph boundary).connectedComponentMk x)) v₀)

/-- Helper for Lemma 4.2.7: choose `v₀` itself as the distinguished root of its own connected
component, and keep the previously chosen component root on every other component. -/
noncomputable def boundaryGraphPreferredRoot
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (c : (boundaryGraph boundary).ConnectedComponent) : X₀ :=
  let _ : DecidableEq ((boundaryGraph boundary).ConnectedComponent) := Classical.decEq _
  if c = (boundaryGraph boundary).connectedComponentMk v₀ then
    v₀
  else
    boundaryGraphComponentRoot boundary c

/-- Helper for Lemma 4.2.7: the preferred root belongs to the component it was chosen from. -/
theorem boundaryGraphPreferredRoot_mem
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (c : (boundaryGraph boundary).ConnectedComponent) :
    (boundaryGraph boundary).connectedComponentMk
        (boundaryGraphPreferredRoot boundary v₀ c) = c := by
  classical
  -- Split on whether `c` is the basepoint component, then reduce to the corresponding branch.
  by_cases hc : c = (boundaryGraph boundary).connectedComponentMk v₀
  · subst hc
    -- On the basepoint component the preferred root is literally `v₀`.
    simp [boundaryGraphPreferredRoot]
  · -- Away from the basepoint component we fall back to the previously chosen component root.
    simp [boundaryGraphPreferredRoot, hc, boundaryGraphComponentRoot_mem]

/-- Helper for Lemma 4.2.7: the preferred root of the basepoint component is exactly `v₀`. -/
theorem boundaryGraphPreferredRoot_basepoint
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    boundaryGraphPreferredRoot boundary v₀
        ((boundaryGraph boundary).connectedComponentMk v₀) = v₀ := by
  classical
  -- The preferred-root definition takes the distinguished `v₀` branch on its own component.
  simp [boundaryGraphPreferredRoot]

/-- Helper for Lemma 4.2.7: choose a shortest walk from the preferred component root to `x`. -/
noncomputable def boundaryGraphShortestWalkFromPreferredRoot
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ x : X₀) :
    (boundaryGraph boundary).Walk
      (boundaryGraphPreferredRoot boundary v₀
        ((boundaryGraph boundary).connectedComponentMk x)) x :=
  Classical.choose <|
    (ConnectedComponent.eq.mp <|
      boundaryGraphPreferredRoot_mem boundary v₀
        ((boundaryGraph boundary).connectedComponentMk x)).exists_path_of_dist

/-- Helper for Lemma 4.2.7: the chosen preferred-root walk is the `exists_path_of_dist` witness,
so it is a path and its length realizes the graph distance from the preferred root. -/
theorem boundaryGraphShortestWalkFromPreferredRoot_spec
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ x : X₀) :
    (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ x).IsPath ∧
      (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ x).length =
        (boundaryGraph boundary).dist
          (boundaryGraphPreferredRoot boundary v₀
            ((boundaryGraph boundary).connectedComponentMk x)) x := by
  -- The definition is exactly the chosen shortest-path witness from `exists_path_of_dist`.
  exact
    Classical.choose_spec <|
      (ConnectedComponent.eq.mp <|
        boundaryGraphPreferredRoot_mem boundary v₀
          ((boundaryGraph boundary).connectedComponentMk x)).exists_path_of_dist

/-- Helper for Lemma 4.2.7: the preferred-root walk is a simple path. -/
theorem boundaryGraphShortestWalkFromPreferredRoot_isPath
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ x : X₀) :
    (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ x).IsPath :=
  by
    -- Read off the path property from the packaged shortest-walk specification.
    exact (boundaryGraphShortestWalkFromPreferredRoot_spec boundary v₀ x).1

/-- Helper for Lemma 4.2.7: the preferred-root walk has the expected combinatorial distance
length. -/
theorem boundaryGraphShortestWalkFromPreferredRoot_length
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ x : X₀) :
    (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ x).length =
      (boundaryGraph boundary).dist
        (boundaryGraphPreferredRoot boundary v₀
          ((boundaryGraph boundary).connectedComponentMk x)) x :=
  by
    -- Read off the distance formula from the same packaged specification.
    exact (boundaryGraphShortestWalkFromPreferredRoot_spec boundary v₀ x).2

/-- Helper for Lemma 4.2.7: pick the realized edge path corresponding to a boundary-graph
adjacency in the default realization topology. -/
noncomputable def boundaryGraphAdjPathDefaultPath
    (boundary : J ↪ Fin 2 → X₀) {u v : X₀}
    (h : (boundaryGraph boundary).Adj u v) :
    _root_.Path (graphVertex boundary u) (graphVertex boundary v) :=
  by
    classical
    change u ≠ v ∧ ∃ j : J, Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk u v at h
    let j : J := Classical.choose h.2
    let hj : Sym2.mk (boundary j 0) (boundary j 1) = Sym2.mk u v := Classical.choose_spec h.2
    by_cases h0 : boundary j 0 = u
    · have h1 : boundary j 1 = v := by
        have hor :
            (boundary j 0 = u ∧ boundary j 1 = v) ∨
              (boundary j 0 = v ∧ boundary j 1 = u) :=
          Sym2.eq_iff.mp hj
        rcases hor with hdir | hrev
        · exact hdir.2
        · exact (h.1 (h0.symm.trans hrev.1)).elim
      refine
        { toFun := graphEdgePoint boundary j
          continuous_toFun := ?_
          source' := ?_
          target' := ?_ }
      · -- The canonical adjacency path is the source edge parameterization itself.
        let _ : TopologicalSpace X₀ := ⊥
        let _ : TopologicalSpace J := ⊥
        have hsource :
            Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) := by
          simpa using
            (continuous_inr.comp
              (continuous_const.prodMk continuous_id) :
                Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))))
        simpa [graphEdgePoint, graphRealizationPoint] using continuous_quotient_mk'.comp hsource
      · simpa [h0] using (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm
      · simpa [h1] using (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm
    · have h0' : boundary j 0 = v := by
        have hor :
            (boundary j 0 = u ∧ boundary j 1 = v) ∨
              (boundary j 0 = v ∧ boundary j 1 = u) :=
          Sym2.eq_iff.mp hj
        rcases hor with hdir | hrev
        · exact (h0 hdir.1).elim
        · exact hrev.1
      have h1' : boundary j 1 = u := by
        have hor :
            (boundary j 0 = u ∧ boundary j 1 = v) ∨
              (boundary j 0 = v ∧ boundary j 1 = u) :=
          Sym2.eq_iff.mp hj
        rcases hor with hdir | hrev
        · exact (h0 hdir.1).elim
        · exact hrev.2
      refine
        { toFun := fun t ↦ graphEdgePoint boundary j (σ t)
          continuous_toFun := ?_
          source' := ?_
          target' := ?_ }
      · -- Reversing the unit interval gives the canonical path when the chosen orientation flips.
        let _ : TopologicalSpace X₀ := ⊥
        let _ : TopologicalSpace J := ⊥
        have hsource :
            Continuous (fun t : I ↦ (Sum.inr (j, σ t) : X₀ ⊕ (J × I))) := by
          simpa using
            (continuous_inr.comp
              (continuous_const.prodMk unitInterval.continuous_symm) :
                Continuous (fun t : I ↦ (Sum.inr (j, σ t) : X₀ ⊕ (J × I))))
        simpa [graphEdgePoint, graphRealizationPoint] using continuous_quotient_mk'.comp hsource
      · simpa [h1'] using (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm
      · simpa [h0'] using (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

/-- Helper for Lemma 4.2.7: the source edge `j` determines the forward boundary-graph adjacency
from `boundary j 0` to `boundary j 1`. -/
theorem boundaryGraphEdgeAdj_forward
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) :
    (boundaryGraph boundary).Adj (boundary j 0) (boundary j 1) := by
  -- The source edge itself realizes the required unordered endpoint pair.
  exact ⟨boundary_ne_endpoints_of_isTree boundary j, ⟨j, rfl⟩⟩

/-- Helper for Lemma 4.2.7: the source edge `j` also determines the reverse boundary-graph
adjacency from `boundary j 1` to `boundary j 0`. -/
theorem boundaryGraphEdgeAdj_backward
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) :
    (boundaryGraph boundary).Adj (boundary j 1) (boundary j 0) :=
  (boundaryGraphEdgeAdj_forward boundary j).symm

/-- Helper for Lemma 4.2.7: the realized source edge `j` gives the default path from its initial
endpoint to its terminal endpoint. -/
noncomputable def graphEdgePath
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) :
    _root_.Path
      (graphVertex boundary (boundary j 0))
      (graphVertex boundary (boundary j 1)) where
  toFun := graphEdgePoint boundary j
  continuous_toFun := by
    -- The edge parameter map is continuous before passing to the realization quotient.
    let _ : TopologicalSpace X₀ := ⊥
    let _ : TopologicalSpace J := ⊥
    have hsource :
        Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))) := by
      simpa using
        (continuous_inr.comp
          (continuous_const.prodMk continuous_id) :
            Continuous (fun t : I ↦ (Sum.inr (j, t) : X₀ ⊕ (J × I))))
    simpa [graphEdgePoint, graphRealizationPoint] using continuous_quotient_mk'.comp hsource
  source' := by
    simpa using (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm
  target' := by
    simpa using (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm

/-- Helper for Lemma 4.2.7: the canonical adjacency path for the forward source edge `j` is the
explicit realized edge path. -/
theorem boundaryGraphAdjPathDefaultPath_forward_eq_graphEdgePath
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) :
    boundaryGraphAdjPathDefaultPath boundary (boundaryGraphEdgeAdj_forward boundary j) =
      graphEdgePath boundary j := by
  classical
  let hForward : (boundaryGraph boundary).Adj (boundary j 0) (boundary j 1) :=
    ⟨boundary_ne_endpoints_of_isTree boundary j, ⟨j, rfl⟩⟩
  have hadj :
      boundaryGraphEdgeAdj_forward boundary j = hForward := by
    -- The forward adjacency theorem and the explicit witness are proofs of the same proposition.
    apply Subsingleton.elim
  have hchooseSpec :
      Sym2.mk (boundary (Classical.choose hForward.2) 0)
          (boundary (Classical.choose hForward.2) 1) =
        Sym2.mk (boundary j 0) (boundary j 1) := by
    -- The explicit forward witness still determines the same unoriented edge.
    exact Classical.choose_spec hForward.2
  have hchoose : Classical.choose hForward.2 = j :=
    boundary_eq_of_sym2_eq_of_isTree boundary hchooseSpec
  have hforward : boundary (Classical.choose hForward.2) 0 = boundary j 0 := by
    simpa using congrArg (fun k => boundary k 0) hchoose
  -- Replacing the proof argument by the canonical witness makes the chosen source edge literal.
  suffices
      boundaryGraphAdjPathDefaultPath boundary hForward = graphEdgePath boundary j by
    simpa [hadj] using this
  ext t
  have hEval :
      (boundaryGraphAdjPathDefaultPath boundary hForward) t =
        graphEdgePoint boundary (Classical.choose hForward.2) t := by
    -- The forward explicit witness forces the first branch of the adjacency-path definition.
    simp only [boundaryGraphAdjPathDefaultPath, id_eq]
    split_ifs with h0
    · rfl
    · exact (h0 hforward).elim
  calc
    (boundaryGraphAdjPathDefaultPath boundary hForward) t =
        graphEdgePoint boundary (Classical.choose hForward.2) t := hEval
    _ = graphEdgePoint boundary j t := congrArg (fun k => graphEdgePoint boundary k t) hchoose

/-- Helper for Lemma 4.2.7: the canonical adjacency path for the backward source edge `j` is the
reverse of the explicit realized edge path. -/
theorem boundaryGraphAdjPathDefaultPath_backward_eq_graphEdgePath_symm
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) :
    boundaryGraphAdjPathDefaultPath boundary (boundaryGraphEdgeAdj_backward boundary j) =
      (graphEdgePath boundary j).symm := by
  classical
  let hBackward : (boundaryGraph boundary).Adj (boundary j 1) (boundary j 0) :=
    ⟨(boundary_ne_endpoints_of_isTree boundary j).symm, ⟨j, Sym2.eq_swap⟩⟩
  have hadj :
      boundaryGraphEdgeAdj_backward boundary j = hBackward := by
    -- The backward adjacency theorem and the explicit swapped witness are propositionally equal.
    apply Subsingleton.elim
  have hchooseSpec :
      Sym2.mk (boundary (Classical.choose hBackward.2) 0)
          (boundary (Classical.choose hBackward.2) 1) =
        Sym2.mk (boundary j 1) (boundary j 0) := by
    -- The explicit backward witness still chooses the same source edge with swapped endpoints.
    exact Classical.choose_spec hBackward.2
  have hchoose : Classical.choose hBackward.2 = j :=
    boundary_eq_of_sym2_eq_of_isTree boundary (hchooseSpec.trans Sym2.eq_swap)
  have hbackward : ¬ boundary (Classical.choose hBackward.2) 0 = boundary j 1 := by
    intro hEq
    rw [hchoose] at hEq
    exact boundary_ne_endpoints_of_isTree boundary j hEq
  -- Replacing the proof argument by the swapped canonical witness leaves only the reversed edge
  -- parameterization.
  suffices
      boundaryGraphAdjPathDefaultPath boundary hBackward = (graphEdgePath boundary j).symm by
    simpa [hadj] using this
  ext t
  have hEval :
      (boundaryGraphAdjPathDefaultPath boundary hBackward) t =
        graphEdgePoint boundary (Classical.choose hBackward.2) (σ t) := by
    -- The backward explicit witness forces the reversed-parameter branch.
    simp only [boundaryGraphAdjPathDefaultPath, id_eq]
    split_ifs with h0
    · exact (hbackward h0).elim
    · rfl
  calc
    (boundaryGraphAdjPathDefaultPath boundary hBackward) t =
        graphEdgePoint boundary (Classical.choose hBackward.2) (σ t) := hEval
    _ = graphEdgePoint boundary j (σ t) := congrArg (fun k => graphEdgePoint boundary k (σ t)) hchoose

/-- Helper for Lemma 4.2.7: evaluating the forward canonical adjacency path gives the expected
edge point on source edge `j`. -/
theorem boundaryGraphAdjPathDefaultPath_forward_apply
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) (t : I) :
    boundaryGraphAdjPathDefaultPath boundary (boundaryGraphEdgeAdj_forward boundary j) t =
      graphEdgePoint boundary j t := by
  -- The whole-path normalization can be evaluated pointwise.
  simpa using congrArg (fun γ => γ t)
    (boundaryGraphAdjPathDefaultPath_forward_eq_graphEdgePath boundary j)

/-- Helper for Lemma 4.2.7: evaluating the backward canonical adjacency path gives the reversed
edge point on source edge `j`. -/
theorem boundaryGraphAdjPathDefaultPath_backward_apply
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) (t : I) :
    boundaryGraphAdjPathDefaultPath boundary (boundaryGraphEdgeAdj_backward boundary j) t =
      graphEdgePoint boundary j (σ t) := by
  -- The backward path normalization is most useful after evaluating at a parameter.
  simpa [Path.symm] using congrArg (fun γ => γ t)
    (boundaryGraphAdjPathDefaultPath_backward_eq_graphEdgePath_symm boundary j)

/-- Helper for Lemma 4.2.7: from a preferred component root, use the coarse vertex jump only when
that root is not already the basepoint `v₀`. -/
noncomputable def rootToBasepointPath
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ root : X₀) :
    _root_.Path (graphVertex boundary root) (graphVertex boundary v₀) :=
  let _ : DecidableEq X₀ := Classical.decEq _
  dite (root = v₀)
    (fun h ↦ (Path.refl (graphVertex boundary v₀)).cast (by simpa [h]) rfl)
    (fun _ ↦ graphVertexJumpPath boundary root v₀)

/-- Helper for Lemma 4.2.7: the preferred root of the basepoint component has no terminal jump,
so its root-to-basepoint path is just the constant path at `graphVertex boundary v₀`. -/
theorem rootToBasepointPath_basepoint
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    rootToBasepointPath boundary v₀ v₀ = Path.refl (graphVertex boundary v₀) := by
  classical
  -- On the branch `root = v₀`, the defining `dite` returns the reflexive path.
  simp [rootToBasepointPath]

/-- Helper for Lemma 4.2.7: read a walk ending at a chosen root as a realized path from its
starting vertex to the global basepoint `v₀` by following the given walk and then a chosen
source-faithful path from `root` to `v₀`. -/
noncomputable def boundaryGraphWalkPathToBasepoint
    (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary]
    (v₀ root : X₀) :
    {x : X₀} → (boundaryGraph boundary).Walk x root →
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      _root_.Path (graphVertex boundary x) (graphVertex boundary v₀)
  | _, w => by
      let _ : TopologicalSpace (graphRealization boundary) :=
        graphRealizationSourceFaithfulTopologicalSpace boundary
      classical
      let wRoot : (boundaryGraph boundary).Walk root v₀ :=
        Classical.choose ((boundaryGraph_connected boundary).exists_walk_length_eq_dist root v₀)
      exact (boundaryGraphWalkPath boundary w).trans (boundaryGraphWalkPath boundary wRoot)

/-- Helper for Lemma 4.2.7: choose a source-faithful realized path from the vertex `x` to the
chosen basepoint `v₀`. -/
noncomputable def vertexPathToBasepoint
    (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary]
    (v₀ x : X₀) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    _root_.Path (graphVertex boundary x) (graphVertex boundary v₀) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  classical
  let w : (boundaryGraph boundary).Walk x v₀ :=
    Classical.choose ((boundaryGraph_connected boundary).exists_walk_length_eq_dist x v₀)
  exact boundaryGraphWalkPath boundary w

/-- Helper for Lemma 4.2.7: the chosen source-faithful path family is fixed at the basepoint
`v₀`. -/
theorem vertexPathToBasepoint_basepoint
    (boundary : J ↪ Fin 2 → X₀) [SourceFaithfulIsTree boundary]
    (v₀ : X₀) :
    let _ : TopologicalSpace (graphRealization boundary) :=
      graphRealizationSourceFaithfulTopologicalSpace boundary
    vertexPathToBasepoint boundary v₀ v₀ = Path.refl (graphVertex boundary v₀) := by
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  classical
  let w : (boundaryGraph boundary).Walk v₀ v₀ :=
    Classical.choose ((boundaryGraph_connected boundary).exists_walk_length_eq_dist v₀ v₀)
  have hwlen : w.length = 0 := by
    -- The chosen walk from `v₀` to itself has length `dist v₀ v₀ = 0`.
    simpa [w] using
      (Classical.choose_spec
        ((boundaryGraph_connected boundary).exists_walk_length_eq_dist v₀ v₀))
  have hwnil : w.Nil := by
    -- A walk of length zero is the empty walk.
    rwa [SimpleGraph.Walk.nil_iff_length_eq]
  have hw : w = SimpleGraph.Walk.nil := SimpleGraph.Walk.Nil.eq_nil hwnil
  -- After rewriting the chosen walk to `nil`, the source-faithful vertex path is reflexive.
  rw [vertexPathToBasepoint]
  dsimp [w]
  change boundaryGraphWalkPath boundary w = Path.refl (graphVertex boundary v₀)
  rw [hw]
  simp [boundaryGraphWalkPath]

/-- Helper for Lemma 4.2.7: for each source edge, the chosen component root sees exactly one
endpoint one step farther away than the other in the forest metric. -/
theorem boundaryGraphEdge_distStepTowardComponentRoot
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (j : J) :
    let c := (boundaryGraph boundary).connectedComponentMk (boundary j 0)
    let r := boundaryGraphComponentRoot boundary c
    let d₀ := (boundaryGraph boundary).dist r (boundary j 0)
    let d₁ := (boundaryGraph boundary).dist r (boundary j 1)
    d₀ = d₁ + 1 ∨ d₁ = d₀ + 1 := by
  -- The edge endpoints lie in one forest component, so acyclicity forces their distances from the
  -- chosen root to differ by exactly one.
  dsimp
  have hroot :
      (boundaryGraph boundary).Reachable
        (boundaryGraphComponentRoot boundary
          ((boundaryGraph boundary).connectedComponentMk (boundary j 0)))
        (boundary j 0) := by
    exact ConnectedComponent.eq.mp <|
      boundaryGraphComponentRoot_mem boundary
        ((boundaryGraph boundary).connectedComponentMk (boundary j 0))
  exact
    (boundaryGraph_isAcyclicOfIsTree boundary).dist_eq_dist_add_one_of_adj_of_reachable
      _ ⟨boundary_ne_endpoints_of_isTree boundary j, ⟨j, rfl⟩⟩ hroot

/-- Helper for Lemma 4.2.7: reading a walk from its terminal end produces a realized path from the
current vertex to the global basepoint `v₀`, with the final edge peeled off first. -/
noncomputable def boundaryGraphWalkPathToBasepointDefault
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    {u x : X₀} → (boundaryGraph boundary).Walk u x →
      _root_.Path (graphVertex boundary x) (graphVertex boundary v₀)
  | _, _, w =>
      SimpleGraph.Walk.concatRec
        (motive := fun _ x _ ↦ _root_.Path (graphVertex boundary x) (graphVertex boundary v₀))
        (Hnil := fun {u} ↦ rootToBasepointPath boundary v₀ u)
        (Hconcat := fun {u v w} _p h ih ↦
          -- Peel off the terminal edge first so edge-step normal forms are exact.
          (boundaryGraphAdjPathDefaultPath boundary h.symm).trans ih)
        w

/-- Helper for Lemma 4.2.7: the terminal-edge recursion on walks turns a concatenated walk into
the corresponding terminal edge followed by the previously constructed tail path. -/
theorem boundaryGraphWalkPathToBasepointDefault_concat
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) {u v w : X₀} (p : (boundaryGraph boundary).Walk u v)
    (h : (boundaryGraph boundary).Adj v w) :
    boundaryGraphWalkPathToBasepointDefault boundary v₀ (p.concat h) =
      (boundaryGraphAdjPathDefaultPath boundary h.symm).trans
        (boundaryGraphWalkPathToBasepointDefault boundary v₀ p) := by
  -- `concatRec` was chosen precisely so that concatenation exposes the terminal edge definitionally.
  simpa [boundaryGraphWalkPathToBasepointDefault] using
    (SimpleGraph.Walk.concatRec_concat
      (motive := fun _ x _ ↦ _root_.Path (graphVertex boundary x) (graphVertex boundary v₀))
      (Hnil := fun {u} ↦ rootToBasepointPath boundary v₀ u)
      (Hconcat := fun {u v w} _p h ih ↦
        (boundaryGraphAdjPathDefaultPath boundary h.symm).trans ih)
      p h)

/-- Helper for Lemma 4.2.7: the preferred root also sees exactly one endpoint of each source edge
one step farther away than the other. -/
theorem boundaryGraphEdge_distStepTowardPreferredRoot
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary] (v₀ : X₀) (j : J) :
    let c := (boundaryGraph boundary).connectedComponentMk (boundary j 0)
    let r := boundaryGraphPreferredRoot boundary v₀ c
    let d₀ := (boundaryGraph boundary).dist r (boundary j 0)
    let d₁ := (boundaryGraph boundary).dist r (boundary j 1)
    d₀ = d₁ + 1 ∨ d₁ = d₀ + 1 := by
  -- The preferred root lies in the same connected component, so the acyclic distance step lemma
  -- applies exactly as it did for an arbitrary component root.
  dsimp
  have hroot :
      (boundaryGraph boundary).Reachable
        (boundaryGraphPreferredRoot boundary v₀
          ((boundaryGraph boundary).connectedComponentMk (boundary j 0)))
        (boundary j 0) := by
    exact ConnectedComponent.eq.mp <|
      boundaryGraphPreferredRoot_mem boundary v₀
        ((boundaryGraph boundary).connectedComponentMk (boundary j 0))
  exact
    (boundaryGraph_isAcyclicOfIsTree boundary).dist_eq_dist_add_one_of_adj_of_reachable
      _ (boundaryGraphEdgeAdj_forward boundary j) hroot

/-- Helper for Lemma 4.2.7: adjacent vertices lie in the same preferred-root component, so the
preferred roots used for their canonical paths agree. -/
theorem boundaryGraphPreferredRoot_eq_of_adj
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ near far : X₀) (hadj : (boundaryGraph boundary).Adj near far) :
    boundaryGraphPreferredRoot boundary v₀
        ((boundaryGraph boundary).connectedComponentMk near) =
      boundaryGraphPreferredRoot boundary v₀
        ((boundaryGraph boundary).connectedComponentMk far) := by
  rw [ConnectedComponent.connectedComponentMk_eq_of_adj hadj]

/-- Helper for Lemma 4.2.7: when one adjacent endpoint is one step farther from the preferred
root, the nearer endpoint already lies on the farther endpoint's chosen preferred-root path. -/
theorem boundaryGraphShortestWalkFromPreferredRoot_mem_support_of_step
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ near far : X₀) (hadj : (boundaryGraph boundary).Adj near far)
    (hstep :
      let r := boundaryGraphPreferredRoot boundary v₀
        ((boundaryGraph boundary).connectedComponentMk far)
      (boundaryGraph boundary).dist r far =
        (boundaryGraph boundary).dist r near + 1) :
    near ∈ (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ far).support := by
  classical
  let r :=
    boundaryGraphPreferredRoot boundary v₀
      ((boundaryGraph boundary).connectedComponentMk far)
  have hcomp :
      (boundaryGraph boundary).connectedComponentMk near =
        (boundaryGraph boundary).connectedComponentMk far :=
    ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  have hroot :
      boundaryGraphPreferredRoot boundary v₀
          ((boundaryGraph boundary).connectedComponentMk near) = r := by
    -- Adjacent vertices lie in one component, so the preferred root is the same on both sides.
    simpa [r] using boundaryGraphPreferredRoot_eq_of_adj boundary v₀ near far hadj
  let pNear :
      (boundaryGraph boundary).Walk r near :=
    (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ near).copy hroot rfl
  have hpNear : pNear.IsPath := by
    -- Copying only changes endpoint indices, not the underlying path combinatorics.
    simpa [pNear] using
      (boundaryGraphShortestWalkFromPreferredRoot_isPath boundary v₀ near)
  have hpFar :
      (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ far).IsPath :=
    boundaryGraphShortestWalkFromPreferredRoot_isPath boundary v₀ far
  by_contra hnear
  have hfar_mem : far ∈ pNear.support := by
    -- In an acyclic graph, if the nearer endpoint were absent from the farther path, then the
    -- farther endpoint would have to lie on the nearer path instead.
    exact
      (boundaryGraph_isAcyclicOfIsTree boundary).mem_support_of_ne_mem_support_of_adj_of_isPath
        hpNear hpFar hadj hnear
  have hlt :
      (pNear.takeUntil far hfar_mem).length < pNear.length := by
    -- The farther endpoint appears strictly before the nearer endpoint on the nearer path.
    exact pNear.length_takeUntil_lt hfar_mem (fun hEq ↦ hadj.ne' hEq)
  have hdistFar :
      (pNear.takeUntil far hfar_mem).length = (boundaryGraph boundary).dist r far := by
    -- Every subwalk of a shortest path still realizes graph distance between its own endpoints.
    exact SimpleGraph.length_eq_dist_of_subwalk
      (by
        simpa [pNear, r, hroot] using
          (boundaryGraphShortestWalkFromPreferredRoot_length boundary v₀ near))
      (pNear.isSubwalk_takeUntil hfar_mem)
  have hdistNear : pNear.length = (boundaryGraph boundary).dist r near := by
    simpa [pNear, r, hroot] using
      (boundaryGraphShortestWalkFromPreferredRoot_length boundary v₀ near)
  have hdist_lt : (boundaryGraph boundary).dist r far < (boundaryGraph boundary).dist r near := by
    calc
      (boundaryGraph boundary).dist r far = (pNear.takeUntil far hfar_mem).length := by
        symm
        exact hdistFar
      _ < pNear.length := hlt
      _ = (boundaryGraph boundary).dist r near := hdistNear
  have hstep' : (boundaryGraph boundary).dist r far = (boundaryGraph boundary).dist r near + 1 := by
    simpa [r] using hstep
  have : (boundaryGraph boundary).dist r near + 1 < (boundaryGraph boundary).dist r near := by
    simpa [hstep'] using hdist_lt
  omega

/-- Helper for Lemma 4.2.7: when one adjacent endpoint is one preferred-root step farther away,
its chosen preferred-root shortest walk is obtained by concatenating the nearer endpoint walk with
that final edge. -/
theorem boundaryGraphShortestWalkFromPreferredRoot_concat_edge
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ near far : X₀) (hadj : (boundaryGraph boundary).Adj near far)
    (hstep :
      let r := boundaryGraphPreferredRoot boundary v₀
        ((boundaryGraph boundary).connectedComponentMk far)
      (boundaryGraph boundary).dist r far =
        (boundaryGraph boundary).dist r near + 1) :
    boundaryGraphShortestWalkFromPreferredRoot boundary v₀ far =
      ((boundaryGraphShortestWalkFromPreferredRoot boundary v₀ near).copy
        (boundaryGraphPreferredRoot_eq_of_adj boundary v₀ near far hadj) rfl).concat hadj := by
  classical
  have hroot :
      boundaryGraphPreferredRoot boundary v₀
          ((boundaryGraph boundary).connectedComponentMk near) =
        boundaryGraphPreferredRoot boundary v₀
          ((boundaryGraph boundary).connectedComponentMk far) :=
    boundaryGraphPreferredRoot_eq_of_adj boundary v₀ near far hadj
  let pNear :
      (boundaryGraph boundary).Walk
        (boundaryGraphPreferredRoot boundary v₀
          ((boundaryGraph boundary).connectedComponentMk far)) near :=
    (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ near).copy hroot rfl
  have hpNear : pNear.IsPath := by
    simpa [pNear] using
      (boundaryGraphShortestWalkFromPreferredRoot_isPath boundary v₀ near)
  have hpFar :
      (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ far).IsPath :=
    boundaryGraphShortestWalkFromPreferredRoot_isPath boundary v₀ far
  have hnear_mem :
      near ∈ (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ far).support :=
    boundaryGraphShortestWalkFromPreferredRoot_mem_support_of_step
      boundary v₀ near far hadj hstep
  -- Acyclicity gives uniqueness of preferred-root shortest paths once the nearer endpoint is known
  -- to lie on the farther path.
  have hconcat :
      boundaryGraphShortestWalkFromPreferredRoot boundary v₀ far = pNear.concat hadj := by
    exact
      (boundaryGraph_isAcyclicOfIsTree boundary).path_concat
        hpNear hpFar hadj hnear_mem
  simpa [pNear] using hconcat

/-- Helper for Lemma 4.2.7: the preferred-root shortest walk, read from the terminal end and
finished by the preferred-root-to-basepoint jump, gives the canonical default-topology path from
`x` to `v₀`. -/
noncomputable def vertexPathToBasepointDefault
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ x : X₀) :
    _root_.Path (graphVertex boundary x) (graphVertex boundary v₀) :=
  boundaryGraphWalkPathToBasepointDefault boundary v₀
    (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ x)

/-- Helper for Lemma 4.2.7: copying the starting vertex index of a walk does not change the
terminal-edge-recursive realized path produced by `boundaryGraphWalkPathToBasepointDefault`. -/
theorem boundaryGraphWalkPathToBasepointDefault_copy
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) {u u' x : X₀} (p : (boundaryGraph boundary).Walk u x)
    (hu : u = u') :
    boundaryGraphWalkPathToBasepointDefault boundary v₀ (p.copy hu rfl) =
      boundaryGraphWalkPathToBasepointDefault boundary v₀ p := by
  subst hu
  rfl

/-- Helper for Lemma 4.2.7: the preferred-root default path is already constant when started at
the chosen basepoint `v₀`. -/
theorem vertexPathToBasepointDefault_basepoint
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    vertexPathToBasepointDefault boundary v₀ v₀ = Path.refl (graphVertex boundary v₀) := by
  let w : (boundaryGraph boundary).Walk v₀ v₀ :=
    (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ v₀).copy
      (boundaryGraphPreferredRoot_basepoint boundary v₀) rfl
  have hwlen :
      w.length = 0 := by
    -- The preferred root of the basepoint component is literally `v₀`, so the chosen shortest walk
    -- back to `v₀` has length `dist v₀ v₀ = 0`.
    simpa [w, boundaryGraphPreferredRoot_basepoint] using
      (boundaryGraphShortestWalkFromPreferredRoot_length boundary v₀ v₀)
  have hwnil : w = (SimpleGraph.Walk.nil : (boundaryGraph boundary).Walk v₀ v₀) := by
    apply SimpleGraph.Walk.Nil.eq_nil
    rwa [SimpleGraph.Walk.nil_iff_length_eq]
  -- Replace the preferred-root walk by the copied walk with start vertex literally `v₀`, then
  -- collapse that copied walk to `nil`.
  rw [vertexPathToBasepointDefault]
  rw [← boundaryGraphWalkPathToBasepointDefault_copy boundary v₀
    (boundaryGraphShortestWalkFromPreferredRoot boundary v₀ v₀)
    (boundaryGraphPreferredRoot_basepoint boundary v₀)]
  change boundaryGraphWalkPathToBasepointDefault boundary v₀ w = Path.refl (graphVertex boundary v₀)
  rw [hwnil]
  simpa [boundaryGraphWalkPathToBasepointDefault, rootToBasepointPath_basepoint]

/-- Helper for Lemma 4.2.7: a one-step preferred-root distance drop along an adjacent edge turns
the farther endpoint's canonical default path into that edge followed by the nearer endpoint's
canonical default path. -/
theorem vertexPathToBasepointDefault_edgeStep
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ near far : X₀) (hadj : (boundaryGraph boundary).Adj near far)
    (hstep :
      let r := boundaryGraphPreferredRoot boundary v₀
        ((boundaryGraph boundary).connectedComponentMk far)
      (boundaryGraph boundary).dist r far =
        (boundaryGraph boundary).dist r near + 1) :
    vertexPathToBasepointDefault boundary v₀ far =
      (boundaryGraphAdjPathDefaultPath boundary hadj.symm).trans
        (vertexPathToBasepointDefault boundary v₀ near) := by
  -- The walk-level normal form from the previous lemma is designed to feed directly into the
  -- terminal-edge recursion used by `boundaryGraphWalkPathToBasepointDefault`.
  rw [vertexPathToBasepointDefault,
    boundaryGraphShortestWalkFromPreferredRoot_concat_edge boundary v₀ near far hadj hstep]
  simpa [vertexPathToBasepointDefault, boundaryGraphWalkPathToBasepointDefault_copy] using
    (boundaryGraphWalkPathToBasepointDefault_concat boundary v₀
      ((boundaryGraphShortestWalkFromPreferredRoot boundary v₀ near).copy
        (boundaryGraphPreferredRoot_eq_of_adj boundary v₀ near far hadj) rfl) hadj)

/-- Helper for Lemma 4.2.7: following the terminal segment of a path from the parameter `a`
compresses the tail `[a, 1]` linearly back onto the full unit interval. -/
noncomputable def pathTail {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : _root_.Path x y) (a : I) :
    _root_.Path (γ a) y where
  toFun := fun t ↦ γ.extend ((a : ℝ) + (1 - a) * t)
  continuous_toFun := by
    -- The tail is just the path extension precomposed with an affine map of the interval.
    exact γ.continuous_extend.comp (by fun_prop)
  source' := by
    simpa using (γ.extend_apply (t := (a : ℝ)) a)
  target' := by
    simp

/-- Helper for Lemma 4.2.7: the tail construction varies continuously with the chosen starting
parameter. -/
theorem pathTail_continuous_family {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : _root_.Path x y) :
    Continuous ↿fun a : I ↦ pathTail γ a := by
  -- The uncurried formula is the affine tail parameter fed into the path extension.
  change Continuous (fun p : I × I ↦ γ.extend (((p.1 : ℝ) + (1 - p.1) * p.2)))
  have hparam :
      Continuous (fun p : I × I ↦ ((p.1 : ℝ) + (((1 : ℝ) + -(p.1 : ℝ)) * p.2))) := by
    fun_prop
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using γ.continuous_extend.comp hparam

/-- Helper for Lemma 4.2.7: the tail of a concatenated path taken from the midpoint is exactly the
second path, up to the canonical source cast. -/
theorem pathTail_trans_midpoint {X : Type*} [TopologicalSpace X] {x y z : X}
    (γ : _root_.Path x y) (δ : _root_.Path y z) :
    pathTail (γ.trans δ) (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ : I) =
      δ.cast (by simp [Path.trans_apply]) rfl := by
  -- Starting the tail at `1/2` discards the first half of `γ.trans δ`, leaving exactly `δ`.
  ext t
  change (γ.trans δ).extend (((1 : ℝ) / 2) + (1 - (1 : ℝ) / 2) * (t : ℝ)) = δ t
  have hhalf :
      (1 : ℝ) / 2 ≤ ((1 : ℝ) / 2) + (1 - (1 : ℝ) / 2) * (t : ℝ) := by
    nlinarith [t.2.1]
  rw [Path.extend_trans_of_half_le γ δ hhalf]
  have hparam :
      2 * (((1 : ℝ) / 2) + (1 - (1 : ℝ) / 2) * (t : ℝ)) - 1 = (t : ℝ) := by
    ring
  rw [hparam]
  simpa using (Path.extend_extends' δ t)

/-- Helper for Lemma 4.2.7: halving a point of `I` stays inside `I`. -/
theorem halfUnitInterval_mem (t : I) : ((t : ℝ) / 2 : ℝ) ∈ (I : Set ℝ) := by
  -- Halving preserves the interval bounds `0 ≤ t ≤ 1`.
  constructor
  · nlinarith [t.2.1]
  · nlinarith [t.2.2]

/-- Helper for Lemma 4.2.7: the affine parameter `t / 2` viewed back in `I`. -/
noncomputable def halfUnitInterval (t : I) : I :=
  ⟨(t : ℝ) / 2, halfUnitInterval_mem t⟩

/-- Helper for Lemma 4.2.7: halving any unit-interval parameter lands in the first half `[0, 1/2]`. -/
theorem halfUnitInterval_le_midpoint (t : I) : ((halfUnitInterval t : I) : ℝ) ≤ (1 : ℝ) / 2 := by
  -- This is the direct inequality `t / 2 ≤ 1 / 2` coming from `t ≤ 1`.
  have ht : ((halfUnitInterval t : I) : ℝ) = (t : ℝ) / 2 := by
    rfl
  rw [ht]
  nlinarith [t.2.2]

/-- Helper for Lemma 4.2.7: halving the left endpoint gives the left endpoint back. -/
@[simp]
theorem halfUnitInterval_zero : halfUnitInterval 0 = 0 := by
  -- The subtype equality is determined by the real coordinate.
  ext
  simp [halfUnitInterval]

/-- Helper for Lemma 4.2.7: the midpoint `1 / 2` belongs to `I`. -/
theorem midpoint_mem_unitInterval : ((1 / 2 : ℝ) ∈ (I : Set ℝ)) := by
  -- The midpoint lies between `0` and `1`.
  constructor <;> norm_num

/-- Helper for Lemma 4.2.7: the canonical midpoint of the unit interval. -/
noncomputable def unitIntervalMidpoint : I :=
  ⟨(1 / 2 : ℝ), midpoint_mem_unitInterval⟩

/-- Helper for Lemma 4.2.7: halving the right endpoint gives the midpoint `1 / 2`. -/
@[simp]
theorem halfUnitInterval_one : halfUnitInterval 1 = unitIntervalMidpoint := by
  -- Both sides are the same midpoint of the unit interval.
  ext
  simp [halfUnitInterval, unitIntervalMidpoint]

/-- Helper for Lemma 4.2.7: evaluating `pathTail γ a` at time `0` recovers the original path value
at `a`. -/
@[simp]
theorem pathTail_apply_zero {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : _root_.Path x y) (a : I) :
    pathTail γ a 0 = γ a := by
  -- The tail begins exactly at the chosen starting parameter.
  simpa [pathTail] using (γ.extend_apply (t := (a : ℝ)) a)

/-- Helper for Lemma 4.2.7: starting the tail at `0` leaves the original path unchanged. -/
theorem pathTail_zero {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : _root_.Path x y) :
    pathTail γ 0 = γ.cast γ.source rfl := by
  -- Both paths evaluate to the same original path point at every time.
  ext t
  simp [pathTail]

/-- Helper for Lemma 4.2.7: every tail path still ends at the original terminal point. -/
@[simp]
theorem pathTail_apply_one {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : _root_.Path x y) (a : I) :
    pathTail γ a 1 = y := by
  -- The affine tail parameter sends `1` to the endpoint of `γ`.
  simp [pathTail]

/-- Helper for Lemma 4.2.7: endpoint `0` of source edge `j` is the farther preferred-root step. -/
def endpointZeroFarther
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (j : J) : Prop :=
  let c := (boundaryGraph boundary).connectedComponentMk (boundary j 0)
  let r := boundaryGraphPreferredRoot boundary v₀ c
  let d₀ := (boundaryGraph boundary).dist r (boundary j 0)
  let d₁ := (boundaryGraph boundary).dist r (boundary j 1)
  d₀ = d₁ + 1

/-- Helper for Lemma 4.2.7: if endpoint `0` is not farther, then endpoint `1` is farther. -/
theorem endpointOneFarther_of_not_endpointZeroFarther
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (j : J) (hZero : ¬ endpointZeroFarther boundary v₀ j) :
    let r := boundaryGraphPreferredRoot boundary v₀
      ((boundaryGraph boundary).connectedComponentMk (boundary j 1))
    (boundaryGraph boundary).dist r (boundary j 1) =
      (boundaryGraph boundary).dist r (boundary j 0) + 1 := by
  -- The distance-step dichotomy leaves only the endpoint-`1` case once endpoint `0` is excluded.
  rcases boundaryGraphEdge_distStepTowardPreferredRoot boundary v₀ j with hstep | hstep
  · exact False.elim (hZero hstep)
  · simpa [boundaryGraphPreferredRoot_eq_of_adj boundary v₀
      (boundary j 0) (boundary j 1) (boundaryGraphEdgeAdj_forward boundary j)] using hstep

/-- Helper for Lemma 4.2.7: use classical decidability for the preferred-root edge orientation
predicate. -/
noncomputable def endpointZeroFartherDecidablePred
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    DecidablePred (endpointZeroFarther boundary v₀) :=
  Classical.decPred (endpointZeroFarther boundary v₀)

/-- Helper for Lemma 4.2.7: the preferred-root source family sends each source representative to
its canonical path toward `graphVertex boundary v₀`. -/
noncomputable def sourceCollapsePathFamily
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    X₀ ⊕ (J × I) → C(I, graphRealization boundary) :=
  let _ : DecidablePred (endpointZeroFarther boundary v₀) :=
    endpointZeroFartherDecidablePred boundary v₀
  fun
    | .inl x =>
        vertexPathToBasepointDefault boundary v₀ x
    | .inr (j, t) =>
        if hZero : endpointZeroFarther boundary v₀ j then
            pathTail
              (vertexPathToBasepointDefault boundary v₀ (boundary j 0))
              (halfUnitInterval t)
        else
            pathTail
              (vertexPathToBasepointDefault boundary v₀ (boundary j 1))
              (halfUnitInterval (σ t))

/-- Helper for Lemma 4.2.7: the source family starts at the represented source point in the
quotient realization. -/
theorem sourceCollapsePathFamily_apply_zero
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (z : X₀ ⊕ (J × I)) :
    sourceCollapsePathFamily boundary v₀ z 0 = graphRealizationPoint boundary z := by
  cases z with
  | inl x =>
      -- The vertex branch starts at the source vertex because each chosen path starts at `x`.
      simpa [sourceCollapsePathFamily, graphVertex] using
        (vertexPathToBasepointDefault boundary v₀ x).source
  | inr jt =>
      rcases jt with ⟨j, t⟩
      by_cases hZero : endpointZeroFarther boundary v₀ j
      · -- If endpoint `0` is farther from the preferred root, the source tail begins on the
        -- forward half of the edge from `boundary j 0` to `boundary j 1`.
        simp [sourceCollapsePathFamily, hZero]
        rw [vertexPathToBasepointDefault_edgeStep boundary v₀
          (boundary j 1) (boundary j 0) (boundaryGraphEdgeAdj_backward boundary j) hZero]
        rw [Path.trans_apply]
        split_ifs with hmid
        · rw [boundaryGraphAdjPathDefaultPath_forward_apply]
          congr 1
          ext
          simp [halfUnitInterval]
          ring
        · exact (hmid.elim (halfUnitInterval_le_midpoint t))
      · -- Otherwise endpoint `1` is farther, so the path starts on the backward edge segment.
        simp [sourceCollapsePathFamily, hZero]
        rw [vertexPathToBasepointDefault_edgeStep boundary v₀
          (boundary j 0) (boundary j 1) (boundaryGraphEdgeAdj_forward boundary j)
          (endpointOneFarther_of_not_endpointZeroFarther boundary v₀ j hZero)]
        rw [Path.trans_apply]
        split_ifs with hmid
        · rw [boundaryGraphAdjPathDefaultPath_backward_apply]
          congr 1
          ext
          simp [halfUnitInterval, unitInterval.coe_symm_eq]
          ring
        · exact (hmid.elim (halfUnitInterval_le_midpoint (σ t)))

/-- Helper for Lemma 4.2.7: every source-family path ends at the chosen basepoint vertex. -/
theorem sourceCollapsePathFamily_apply_one
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (z : X₀ ⊕ (J × I)) :
    sourceCollapsePathFamily boundary v₀ z 1 = graphVertex boundary v₀ := by
  cases z with
  | inl x =>
      -- The vertex path family already ends at the chosen basepoint.
      simpa [sourceCollapsePathFamily] using
        (vertexPathToBasepointDefault boundary v₀ x).target
  | inr jt =>
      rcases jt with ⟨j, t⟩
      by_cases hZero : endpointZeroFarther boundary v₀ j
      · -- The forward tail keeps the terminal endpoint of the original preferred-root path.
        simpa [sourceCollapsePathFamily, hZero] using
          pathTail_apply_one
            (vertexPathToBasepointDefault boundary v₀ (boundary j 0))
            (halfUnitInterval t)
      · -- The backward tail has the same terminal endpoint for the same reason.
        simpa [sourceCollapsePathFamily, hZero] using
          pathTail_apply_one
            (vertexPathToBasepointDefault boundary v₀ (boundary j 1))
            (halfUnitInterval (σ t))

/-- Helper for Lemma 4.2.7: on the source endpoint `(j, 0)`, the preferred-root edge family
agrees with the vertex family at `boundary j 0`. -/
theorem sourceCollapsePathFamily_edge_zero
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (j : J) :
    sourceCollapsePathFamily boundary v₀ (Sum.inr (j, 0)) =
      sourceCollapsePathFamily boundary v₀ (Sum.inl (boundary j 0)) := by
  ext t
  by_cases hZero : endpointZeroFarther boundary v₀ j
  · -- When endpoint `0` is farther, the left endpoint is already the start of that preferred-root
    -- path, so taking the tail from `0` does nothing.
    calc
      (sourceCollapsePathFamily boundary v₀ (Sum.inr (j, 0))) t
          = pathTail
              (vertexPathToBasepointDefault boundary v₀ (boundary j 0))
              (halfUnitInterval 0) t := by
                simp [sourceCollapsePathFamily, hZero]
      _ = (vertexPathToBasepointDefault boundary v₀ (boundary j 0)) t := by
            rw [halfUnitInterval_zero]
            simpa using congrArg (fun γ => γ t)
              (pathTail_zero (vertexPathToBasepointDefault boundary v₀ (boundary j 0)))
      _ = (sourceCollapsePathFamily boundary v₀ (Sum.inl (boundary j 0))) t := by
            simp [sourceCollapsePathFamily]
  · -- Otherwise endpoint `1` is farther, so the midpoint tail discards the initial backward edge
    -- and leaves the endpoint-`0` preferred-root path.
    calc
      (sourceCollapsePathFamily boundary v₀ (Sum.inr (j, 0))) t
          = pathTail
              (vertexPathToBasepointDefault boundary v₀ (boundary j 1))
              (halfUnitInterval (σ 0)) t := by
                simp [sourceCollapsePathFamily, hZero]
      _ = pathTail
            ((boundaryGraphAdjPathDefaultPath boundary
                (boundaryGraphEdgeAdj_forward boundary j).symm).trans
              (vertexPathToBasepointDefault boundary v₀ (boundary j 0)))
            unitIntervalMidpoint t := by
              rw [unitInterval.symm_zero, halfUnitInterval_one]
              rw [vertexPathToBasepointDefault_edgeStep boundary v₀
                (boundary j 0) (boundary j 1) (boundaryGraphEdgeAdj_forward boundary j)
                (endpointOneFarther_of_not_endpointZeroFarther boundary v₀ j hZero)]
      _ = (vertexPathToBasepointDefault boundary v₀ (boundary j 0)) t := by
            simpa using congrArg (fun γ => γ t)
              (pathTail_trans_midpoint
                (boundaryGraphAdjPathDefaultPath boundary
                  (boundaryGraphEdgeAdj_forward boundary j).symm)
                (vertexPathToBasepointDefault boundary v₀ (boundary j 0)))
      _ = (sourceCollapsePathFamily boundary v₀ (Sum.inl (boundary j 0))) t := by
            simp [sourceCollapsePathFamily]

/-- Helper for Lemma 4.2.7: on the source endpoint `(j, 1)`, the preferred-root edge family
agrees with the vertex family at `boundary j 1`. -/
theorem sourceCollapsePathFamily_edge_one
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (j : J) :
    sourceCollapsePathFamily boundary v₀ (Sum.inr (j, 1)) =
      sourceCollapsePathFamily boundary v₀ (Sum.inl (boundary j 1)) := by
  ext t
  by_cases hZero : endpointZeroFarther boundary v₀ j
  · -- If endpoint `0` is farther, the midpoint tail now drops the initial forward edge and leaves
    -- the endpoint-`1` preferred-root path.
    calc
      (sourceCollapsePathFamily boundary v₀ (Sum.inr (j, 1))) t
          = pathTail
              (vertexPathToBasepointDefault boundary v₀ (boundary j 0))
              (halfUnitInterval 1) t := by
                simp [sourceCollapsePathFamily, hZero]
      _ = pathTail
            ((boundaryGraphAdjPathDefaultPath boundary
                (boundaryGraphEdgeAdj_backward boundary j).symm).trans
              (vertexPathToBasepointDefault boundary v₀ (boundary j 1)))
            unitIntervalMidpoint t := by
              rw [halfUnitInterval_one]
              rw [vertexPathToBasepointDefault_edgeStep boundary v₀
                (boundary j 1) (boundary j 0) (boundaryGraphEdgeAdj_backward boundary j) hZero]
      _ = (vertexPathToBasepointDefault boundary v₀ (boundary j 1)) t := by
            simpa using congrArg (fun γ => γ t)
              (pathTail_trans_midpoint
                (boundaryGraphAdjPathDefaultPath boundary
                  (boundaryGraphEdgeAdj_backward boundary j).symm)
                (vertexPathToBasepointDefault boundary v₀ (boundary j 1)))
      _ = (sourceCollapsePathFamily boundary v₀ (Sum.inl (boundary j 1))) t := by
            simp [sourceCollapsePathFamily]
  · -- When endpoint `1` is farther, the right endpoint is already the start of that preferred-root
    -- path, so the tail from `0` is the whole path.
    calc
      (sourceCollapsePathFamily boundary v₀ (Sum.inr (j, 1))) t
          = pathTail
              (vertexPathToBasepointDefault boundary v₀ (boundary j 1))
              (halfUnitInterval (σ 1)) t := by
                simp [sourceCollapsePathFamily, hZero]
      _ = (vertexPathToBasepointDefault boundary v₀ (boundary j 1)) t := by
            rw [unitInterval.symm_one, halfUnitInterval_zero]
            simpa using congrArg (fun γ => γ t)
              (pathTail_zero (vertexPathToBasepointDefault boundary v₀ (boundary j 1)))
      _ = (sourceCollapsePathFamily boundary v₀ (Sum.inl (boundary j 1))) t := by
            simp [sourceCollapsePathFamily]

/-- Helper for Lemma 4.2.7: the normalized source family respects each generating endpoint
identification of `graphRealizationRel boundary`. -/
theorem sourceCollapsePathFamily_respectsRel
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) {a b : X₀ ⊕ (J × I)}
    (hab : graphRealizationRel boundary a b) :
    sourceCollapsePathFamily boundary v₀ a = sourceCollapsePathFamily boundary v₀ b := by
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          cases hab
      | inr jt =>
          rcases jt with ⟨j, t⟩
          rcases hab with (⟨hx, ht⟩ | ⟨hx, ht⟩)
          · subst hx
            subst t
            symm
            exact sourceCollapsePathFamily_edge_zero boundary v₀ j
          · subst hx
            subst t
            symm
            exact sourceCollapsePathFamily_edge_one boundary v₀ j
  | inr jt =>
      rcases jt with ⟨j, t⟩
      cases b with
      | inl x =>
          rcases hab with (⟨ht, hx⟩ | ⟨ht, hx⟩)
          · subst hx
            subst t
            exact sourceCollapsePathFamily_edge_zero boundary v₀ j
          · subst hx
            subst t
            exact sourceCollapsePathFamily_edge_one boundary v₀ j
      | inr jt' =>
          cases hab

/-- Helper for Lemma 4.2.7: the normalized source family descends through the full realization
setoid. -/
theorem sourceCollapsePathFamily_respectsSetoid
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) {a b : X₀ ⊕ (J × I)}
    (hab : graphRealizationSetoid boundary a b) :
    sourceCollapsePathFamily boundary v₀ a = sourceCollapsePathFamily boundary v₀ b := by
  -- Extend the generator check to the equivalence closure used in the realization quotient.
  induction hab with
  | rel _ _ hrel =>
      exact sourceCollapsePathFamily_respectsRel boundary v₀ hrel
  | refl a =>
      rfl
  | symm a b hab ih =>
      exact ih.symm
  | trans a b c hab hbc ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Helper for Lemma 4.2.7: after freezing a source edge, uncurrying the normalized edge branch
recovers a continuous two-parameter family. -/
theorem sourceCollapsePathFamily_edgeBranch_uncurry_continuous
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) (j : J) :
    Continuous (fun p : I × I ↦ sourceCollapsePathFamily boundary v₀ (Sum.inr (j, p.1)) p.2) := by
  -- Once the source edge `j` is fixed, only the interval coordinates vary, so the branch reduces
  -- to one explicit affine reparameterization of `pathTail`.
  by_cases hZero : endpointZeroFarther boundary v₀ j
  · have hFst :
        Continuous (fun p : I × I ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hHalf :
        Continuous (fun p : I × I ↦ (p.1 : ℝ) / 2) := by
      simpa using hFst.div_const (2 : ℝ)
    have hSnd :
        Continuous (fun p : I × I ↦ (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hWeight :
        Continuous (fun p : I × I ↦ (1 : ℝ) + -((p.1 : ℝ) / 2)) := by
      exact continuous_const.add (continuous_neg.comp hHalf)
    have hParam :
        Continuous
          (fun p : I × I ↦ (p.1 : ℝ) / 2 + ((1 : ℝ) + -((p.1 : ℝ) / 2)) * (p.2 : ℝ)) := by
      exact hHalf.add (hWeight.mul hSnd)
    -- The `hZero` branch is exactly the tail family on endpoint `0` with the halved first
    -- interval coordinate.
    simpa [sourceCollapsePathFamily, hZero, pathTail, halfUnitInterval, sub_eq_add_neg] using
      (vertexPathToBasepointDefault boundary v₀ (boundary j 0)).continuous_extend.comp hParam
  · have hSymm :
        Continuous (fun p : I × I ↦ (σ p.1 : I)) :=
      unitInterval.continuous_symm.comp continuous_fst
    have hFst :
        Continuous (fun p : I × I ↦ ((σ p.1 : I) : ℝ)) :=
      continuous_subtype_val.comp hSymm
    have hHalf :
        Continuous (fun p : I × I ↦ ((σ p.1 : I) : ℝ) / 2) := by
      simpa using hFst.div_const (2 : ℝ)
    have hSnd :
        Continuous (fun p : I × I ↦ (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hWeight :
        Continuous (fun p : I × I ↦ (1 : ℝ) + -(((σ p.1 : I) : ℝ) / 2)) := by
      exact continuous_const.add (continuous_neg.comp hHalf)
    have hParam :
        Continuous
          (fun p : I × I ↦
            ((σ p.1 : I) : ℝ) / 2 + ((1 : ℝ) + -(((σ p.1 : I) : ℝ) / 2)) * (p.2 : ℝ)) := by
      exact hHalf.add (hWeight.mul hSnd)
    -- The complementary branch is the same tail construction after reversing the first interval
    -- coordinate.
    simpa [sourceCollapsePathFamily, hZero, pathTail, halfUnitInterval, sub_eq_add_neg] using
      (vertexPathToBasepointDefault boundary v₀ (boundary j 1)).continuous_extend.comp hParam

/-- Helper for Lemma 4.2.7: on the vertex summand, the uncurried preferred-root family is
continuous because the vertex coordinate is discrete and each fiber is exactly the chosen path to
the basepoint. -/
theorem sourceCollapsePathFamily_vertexBranch_uncurry_continuous_discrete
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    let _ : TopologicalSpace X₀ := ⊥
    Continuous (fun p : X₀ × I ↦ sourceCollapsePathFamily boundary v₀ (Sum.inl p.1) p.2) := by
  let _ : TopologicalSpace X₀ := ⊥
  let _ : DiscreteTopology X₀ := discreteTopology_bot X₀
  -- Route correction: the left summand is best handled fiberwise on `X₀ × I`, not as a global
  -- map into the path space.
  rw [continuous_prod_of_discrete_left]
  intro x
  -- After fixing `x`, this branch is exactly the chosen preferred-root path from `x` to `v₀`.
  simpa [sourceCollapsePathFamily] using (vertexPathToBasepointDefault boundary v₀ x).continuous

/-- Helper for Lemma 4.2.7: after reassociating the right summand to `J × (I × I)`, continuity
reduces to the already proved fixed-edge two-parameter family. -/
theorem sourceCollapsePathFamily_rightSummand_uncurry_continuous_discrete
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    let _ : TopologicalSpace J := ⊥
    Continuous
      (fun p : J × I × I ↦ sourceCollapsePathFamily boundary v₀ (Sum.inr (p.1, p.2.1)) p.2.2) := by
  let _ : TopologicalSpace J := ⊥
  let _ : DiscreteTopology J := discreteTopology_bot J
  -- Once the edge index is frozen, the remaining two interval coordinates are handled by the
  -- fixed-edge continuity theorem proved above.
  rw [continuous_prod_of_discrete_left]
  intro j
  simpa using sourceCollapsePathFamily_edgeBranch_uncurry_continuous boundary v₀ j

/-- Helper for Lemma 4.2.7: continuity of the normalized source family should be proved on the
source quotient before descending to `graphRealization boundary`. -/
theorem sourceCollapsePathFamily_uncurry_continuous
    (boundary : J ↪ Fin 2 → X₀) [IsTree boundary]
    (v₀ : X₀) :
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceTopologicalSpace
    Continuous (Function.uncurry fun z s => sourceCollapsePathFamily boundary v₀ z s) := by
  let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceTopologicalSpace
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  let e : (X₀ ⊕ (J × I)) × I ≃ₜ (X₀ × I) ⊕ ((J × I) × I) :=
    Homeomorph.sumProdDistrib
  have hLeft :
      Continuous
        (fun p : X₀ × I ↦ sourceCollapsePathFamily boundary v₀ (Sum.inl p.1) p.2) := by
    simpa [graphRealizationSourceTopologicalSpace] using
      sourceCollapsePathFamily_vertexBranch_uncurry_continuous_discrete boundary v₀
  have hRightAssoc :
      Continuous
        (fun p : J × (I × I) ↦
          sourceCollapsePathFamily boundary v₀ (Sum.inr (p.1, p.2.1)) p.2.2) := by
    simpa [graphRealizationSourceTopologicalSpace] using
      sourceCollapsePathFamily_rightSummand_uncurry_continuous_discrete boundary v₀
  have hRight :
      Continuous
        (fun p : (J × I) × I ↦
          sourceCollapsePathFamily boundary v₀ (Sum.inr p.1) p.2) := by
    let eAssoc : ((J × I) × I) ≃ₜ J × (I × I) := Homeomorph.prodAssoc J I I
    simpa [eAssoc, Homeomorph.prodAssoc, Equiv.prodAssoc] using
      hRightAssoc.comp eAssoc.continuous
  have hOnSum :
      Continuous
        ((Function.uncurry fun z s => sourceCollapsePathFamily boundary v₀ z s) ∘
          e.symm) := by
    rw [continuous_sum_dom]
    constructor
    · simpa [Function.comp_def] using hLeft
    · simpa [Function.comp_def] using hRight
  simpa [Function.comp_def] using
    hOnSum.comp e.continuous

/-- Helper for Lemma 4.2.7: the constant map at a chosen point lands in the corresponding
singleton subset. -/
theorem range_const_subset_singleton {X : Type*} [TopologicalSpace X] (x : X) :
    Set.range (ContinuousMap.const X x) ⊆ ({x} : Set X) := by
  -- Any value in the range of a constant map is definitionally the chosen point.
  rintro y ⟨z, rfl⟩
  simp

/-- Helper for Lemma 4.2.7: a continuous family of paths from each point of `X` to `x` packages
into a homotopy from `ContinuousMap.id X` to the constant map at `x`, fixed on `{x}`. -/
theorem pathFamilyHomotopyRelSingleton {X : Type*} [TopologicalSpace X]
    (d : C(X, C(I, X))) (x : X)
    (hStart : ∀ y, d y 0 = y)
    (hEnd : ∀ y, d y 1 = x)
    (hRoot : ∀ t, d x t = x) :
    (ContinuousMap.id X).HomotopicRel (ContinuousMap.const X x) ({x} : Set X) := by
  -- Uncurrying the path family gives the required time-dependent map `I × X → X`.
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · refine
      { toFun := fun p ↦ d p.2 p.1
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }
    · have huncurry : Continuous fun p : X × I ↦ d p.1 p.2 :=
        ContinuousMap.continuous_uncurry_of_continuous d
      simpa using huncurry.comp continuous_swap
    · intro y
      exact hStart y
    · intro y
      exact hEnd y
  · intro t y hy
    -- On the singleton `{x}`, every intermediate map is the constant value `x`.
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simpa using hRoot t

/-- Helper for Lemma 4.2.7: once a singleton-relative homotopy to the constant map is available,
the singleton is a deformation retract. -/
theorem isDeformationRetract_singleton_of_homotopyRelConst {X : Type*} [TopologicalSpace X]
    (x : X)
    (hHom :
      (ContinuousMap.id X).HomotopicRel (ContinuousMap.const X x) ({x} : Set X)) :
    IsDeformationRetract ({x} : Set X) := by
  -- Package the constant endpoint map and the relative homotopy with the standard constructor.
  exact ⟨ContinuousMap.const X x, hHom, range_const_subset_singleton x⟩

/-- Lemma 4.2.7. Any vertex `v₀` of a tree `graphRealization boundary` is a deformation retract of
the whole tree. -/
theorem isDeformationRetract_singleton_graphVertex
    (boundary : J ↪ Fin 2 → X₀)
    [IsTree boundary]
    (v₀ : X₀) :
    -- Route correction: the old `source → C(I, X)` attempt failed because the terminal edge was
    -- not normalized exactly. The new helpers above produce an exact preferred-root edge-step
    -- normal form; the remaining work is to package the edge-interior tail family and descend it
    -- through the realization quotient.
    IsDeformationRetract ({graphVertex boundary v₀} : Set (graphRealization boundary)) := by
  classical
  let rawFamily : graphRealization boundary → C(I, graphRealization boundary) :=
    Quotient.lift
      (sourceCollapsePathFamily boundary v₀)
      (fun _ _ hab ↦ sourceCollapsePathFamily_respectsSetoid boundary v₀ hab)
  have hStart : ∀ y : graphRealization boundary, rawFamily y 0 = y := by
    intro y
    refine Quotient.inductionOn y ?_
    intro z
    -- The descended family starts at the represented source point.
    simpa [rawFamily] using sourceCollapsePathFamily_apply_zero boundary v₀ z
  have hEnd : ∀ y : graphRealization boundary, rawFamily y 1 = graphVertex boundary v₀ := by
    intro y
    refine Quotient.inductionOn y ?_
    intro z
    -- Every descended path ends at the chosen basepoint vertex.
    simpa [rawFamily] using sourceCollapsePathFamily_apply_one boundary v₀ z
  have hRoot : ∀ t : I, rawFamily (graphVertex boundary v₀) t = graphVertex boundary v₀ := by
    intro t
    -- At the basepoint vertex the canonical path is already constant.
    change sourceCollapsePathFamily boundary v₀ (Sum.inl v₀) t = graphVertex boundary v₀
    simpa [sourceCollapsePathFamily] using congrArg
      (fun γ : _root_.Path (graphVertex boundary v₀) (graphVertex boundary v₀) => γ t)
      (vertexPathToBasepointDefault_basepoint boundary v₀)
  have hSource :
      let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceTopologicalSpace
      Continuous (sourceCollapsePathFamily boundary v₀) := by
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceTopologicalSpace
    -- First prove continuity of the uncurried source family, then curry it into the path space.
    exact ContinuousMap.continuous_of_continuous_uncurry
      (sourceCollapsePathFamily boundary v₀)
      (sourceCollapsePathFamily_uncurry_continuous boundary v₀)
  have hContinuous : Continuous rawFamily := by
    let _ : TopologicalSpace (X₀ ⊕ (J × I)) := graphRealizationSourceTopologicalSpace
    -- Descend continuity through the quotient only after the source family has been normalized.
    exact hSource.quotient_lift
      (fun _ _ hab ↦ sourceCollapsePathFamily_respectsSetoid boundary v₀ hab)
  let pathFamily : C(graphRealization boundary, C(I, graphRealization boundary)) :=
    ⟨rawFamily, hContinuous⟩
  -- Once continuity is supplied, the generic singleton-relative path-family package finishes.
  exact
    isDeformationRetract_singleton_of_homotopyRelConst
      (graphVertex boundary v₀)
      (pathFamilyHomotopyRelSingleton pathFamily (graphVertex boundary v₀) hStart hEnd hRoot)
