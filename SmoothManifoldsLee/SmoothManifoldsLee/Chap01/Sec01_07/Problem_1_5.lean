import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Helper for Problem 1-5: if every connected component is `σ`-compact and the quotient of
components is countable, then the whole space is `σ`-compact. -/
theorem sigmaCompactSpace_of_countable_sigmaCompact_connectedComponents
    {M : Type u} [TopologicalSpace M]
    (hcount : Countable (ConnectedComponents M))
    (hcomponent : ∀ x : M, IsSigmaCompact (connectedComponent x : Set M)) :
    SigmaCompactSpace M := by
  -- Assemble the space as a countable union of the fibers of the quotient to connected components.
  rw [← isSigmaCompact_univ_iff]
  letI : Countable (ConnectedComponents M) := hcount
  have hunion :
      IsSigmaCompact
        (⋃ c : ConnectedComponents M, ((↑) ⁻¹' ({c} : Set (ConnectedComponents M)) : Set M)) := by
    -- Each fiber is one connected component, so the countable union is `σ`-compact.
    refine isSigmaCompact_iUnion
      (fun c : ConnectedComponents M ↦
        ((↑) ⁻¹' ({c} : Set (ConnectedComponents M)) : Set M))
      ?_
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simpa [connectedComponents_preimage_singleton] using hcomponent x
  have huniv :
      (⋃ c : ConnectedComponents M, ((↑) ⁻¹' ({c} : Set (ConnectedComponents M)) : Set M)) =
        (univ : Set M) := by
    -- Every point lies in the fiber of its own connected component.
    ext x
    simp
  simpa [huniv] using hunion

/-- Helper for Problem 1-5: in a relation with finitely many outgoing neighbors from each vertex,
the vertices reachable from a fixed root form a countable set. -/
theorem countable_reachable_of_finite_neighbors
    {ι : Type*} (R : ι → ι → Prop) (i₀ : ι)
    (hfinite : ∀ i, {j | R i j}.Finite) :
    {j | Relation.ReflTransGen R i₀ j}.Countable := by
  classical
  let layer : ℕ → Set ι :=
    Nat.rec ({i₀} : Set ι) fun _ s ↦ ⋃ i ∈ s, {j | R i j}
  have hlayer_finite : ∀ n, (layer n).Finite := by
    intro n
    induction n with
    | zero =>
        -- The zeroth layer contains only the root.
        simp [layer]
    | succ n ih =>
        -- The next layer is a finite union of finite neighbor sets.
        simpa [layer] using
          Set.Finite.biUnion ih fun i _ ↦ hfinite i
  have hsubset :
      {j | Relation.ReflTransGen R i₀ j} ⊆ ⋃ n, layer n := by
    intro j hj
    -- Any reachability proof has a finite length, so `j` lies in some layer.
    induction hj with
    | refl =>
        exact mem_iUnion.2 ⟨0, by simp [layer]⟩
    | @tail b c hbc hR ih =>
        rcases mem_iUnion.1 ih with ⟨n, hn⟩
        exact mem_iUnion.2 ⟨n + 1, mem_iUnion₂.2 ⟨b, hn, hR⟩⟩
  -- Countable union of finite layers gives the countability of the reachable set.
  exact (Set.countable_iUnion fun n ↦ (hlayer_finite n).countable).mono hsubset

/-- Helper for Problem 1-5: a connected space with a locally finite open cover by sets with
compact closure admits a countable subcover. -/
theorem countable_subcover_of_connected_from_locallyFinite_precompact_cover
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {ι : Type*} (U : ι → Set X) (hU_open : ∀ i, IsOpen (U i))
    (hU_cover : ⋃ i, U i = univ) (hU_locallyFinite : LocallyFinite U)
    (hU_compactClosure : ∀ i, IsCompact (closure (U i))) :
    ∃ s : Set ι, s.Countable ∧ ⋃ i ∈ s, U i = univ := by
  classical
  let R : ι → ι → Prop := fun i j ↦ (U i ∩ U j).Nonempty
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨i₀, hx₀⟩ : ∃ i : ι, x₀ ∈ U i := by
    exact iUnion_eq_univ_iff.mp hU_cover x₀
  have hfinite_neighbors : ∀ i, {j | R i j}.Finite := by
    intro i
    -- Local finiteness around the compact closure of `U i` leaves only finitely many overlaps.
    refine (hU_locallyFinite.finite_nonempty_inter_compact (hU_compactClosure i)).subset ?_
    intro j hj
    rcases hj with ⟨x, hxUi, hxUj⟩
    exact ⟨x, hxUj, subset_closure hxUi⟩
  let s : Set ι := {j | Relation.ReflTransGen R i₀ j}
  have hs_countable : s.Countable :=
    countable_reachable_of_finite_neighbors R i₀ hfinite_neighbors
  have hi₀ : i₀ ∈ s := Relation.ReflTransGen.refl
  have hsubcover : ⋃ i ∈ s, U i = univ := by
    let A : Set X := ⋃ i ∈ s, U i
    have hA_open : IsOpen A := by
      -- The union over the reachable indices is open because each cover member is open.
      simpa [A] using isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hU_open i
    have hA_nonempty : A.Nonempty := by
      -- The root cover element lies in the reachable union.
      refine ⟨x₀, ?_⟩
      exact mem_iUnion₂.2 ⟨i₀, hi₀, hx₀⟩
    have hA_compl_open : IsOpen Aᶜ := by
      -- Any cover set meeting the reachable union is itself reachable, so the complement is open.
      rw [isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨j, hyj⟩ : ∃ j : ι, y ∈ U j := by
        exact iUnion_eq_univ_iff.mp hU_cover y
      refine Filter.mem_of_superset ((hU_open j).mem_nhds hyj) ?_
      intro z hzj
      rw [mem_compl_iff]
      intro hzA
      rcases mem_iUnion₂.1 hzA with ⟨k, hk, hzk⟩
      have hj_reachable : Relation.ReflTransGen R i₀ j :=
        Relation.ReflTransGen.tail hk ⟨z, hzk, hzj⟩
      exact hy <| mem_iUnion₂.2 ⟨j, hj_reachable, hyj⟩
    have hA_clopen : IsClopen A := ⟨isOpen_compl_iff.mp hA_compl_open, hA_open⟩
    -- A nonempty clopen set in a connected space must be all of `X`.
    exact IsClopen.eq_univ hA_clopen hA_nonempty
  exact ⟨s, hs_countable, hsubcover⟩

/-- Helper for Problem 1-5: every connected paracompact locally compact Hausdorff space is
`σ`-compact. -/
theorem sigmaCompactSpace_of_connected_paracompact_locallyCompact_t2
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ParacompactSpace X] [LocallyCompactSpace X] :
    SigmaCompactSpace X := by
  classical
  choose W hW_open hxW hW_compact using
    fun x : X ↦ exists_isOpen_mem_isCompact_closure x
  -- Refine the pointwise precompact neighborhood cover to a locally finite one.
  obtain ⟨V, hV_open, hV_cover, hV_locallyFinite, hV_subset⟩ :=
    precise_refinement W hW_open (iUnion_eq_univ_iff.2 fun x ↦ ⟨x, hxW x⟩)
  have hV_compact : ∀ x, IsCompact (closure (V x)) := by
    intro x
    -- Compactness is preserved because `closure (V x)` sits inside `closure (W x)`.
    exact (hW_compact x).of_isClosed_subset isClosed_closure (closure_mono (hV_subset x))
  obtain ⟨s, hs_countable, hs_cover⟩ :=
    countable_subcover_of_connected_from_locallyFinite_precompact_cover
      V hV_open hV_cover hV_locallyFinite hV_compact
  -- The compact closures of the countable subcover cover the whole space.
  refine SigmaCompactSpace.of_countable ((fun i ↦ closure (V i)) '' s) (hs_countable.image _) ?_ ?_
  · intro K hK
    rcases hK with ⟨i, hi, rfl⟩
    exact hV_compact i
  · ext x
    constructor
    · intro _
      simp
    · intro _
      have hxcover : x ∈ ⋃ i ∈ s, V i := by
        simp [hs_cover]
      rcases mem_iUnion.1 hxcover with ⟨i, hxi⟩
      rcases mem_iUnion.1 hxi with ⟨hi, hxVi⟩
      exact mem_sUnion.2 ⟨closure (V i), mem_image_of_mem _ hi, subset_closure hxVi⟩

/-- Helper for Problem 1-5: in a paracompact Hausdorff space locally modelled on `ℝ^n`, each
connected component is `σ`-compact. -/
theorem isSigmaCompact_connectedComponent_of_paracompact_t2_euclidean
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ParacompactSpace M] [LocallyCompactSpace M] [LocallyConnectedSpace M] (x : M) :
    IsSigmaCompact (connectedComponent x : Set M) := by
  -- Route correction: work on the subtype `connectedComponent x`, where connectedness is built in,
  -- and apply the general connected-paracompact-locally-compact `σ`-compactness theorem.
  rw [isSigmaCompact_iff_sigmaCompactSpace]
  letI : ConnectedSpace (connectedComponent x) :=
    Subtype.connectedSpace isConnected_connectedComponent
  letI : ParacompactSpace (connectedComponent x) :=
    (isClosed_connectedComponent (x := x)).isClosedEmbedding_subtypeVal.paracompactSpace
  letI : LocallyCompactSpace (connectedComponent x) :=
    (isClosed_connectedComponent (x := x)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact sigmaCompactSpace_of_connected_paracompact_locallyCompact_t2

/-- Problem 1-5: a Hausdorff space locally modelled on `ℝ^n` is second-countable if and only if it
is paracompact and has countably many connected components. Under these ambient hypotheses, this is
equivalently the condition for Lee's `TopologicalManifold` owner abstraction. -/
-- Proof sketch: if `M` is a topological manifold, then `Theorem_1_15` gives paracompactness and
-- `Proposition_1_11` gives countably many connected components. Conversely, connected components
-- are open in the locally connected space induced from the Euclidean chart model; under
-- paracompactness each connected component is `σ`-compact, so countably many components make `M`
-- `σ`-compact. Apply `Problem_1_3` to identify `σ`-compactness with `TopologicalManifold n M`.
theorem secondCountableTopology_iff_paracompact_and_countable_components_of_t2_euclidean
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    SecondCountableTopology M ↔ ParacompactSpace M ∧ Countable (ConnectedComponents M) := by
  constructor
  · intro hM
    letI : SecondCountableTopology M := hM
    letI : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    letI : LocallyConnectedSpace M :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
    constructor
    · -- Combine local compactness with second countability to get `σ`-compactness, hence
      -- paracompactness in the Hausdorff setting.
      letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
      infer_instance
    · -- The connected-components quotient is discrete and Lindelöf, hence countable.
      letI : LindelofSpace M := inferInstance
      letI : DiscreteTopology (ConnectedComponents M) := inferInstance
      letI : LindelofSpace (ConnectedComponents M) :=
        LindelofSpace.of_continuous_surjective ConnectedComponents.continuous_coe
          ConnectedComponents.surjective_coe
      exact countable_of_Lindelof_of_discrete
  · rintro ⟨hparacompact, hcount⟩
    letI : ParacompactSpace M := hparacompact
    letI : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    letI : LocallyConnectedSpace M :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
    have hcomponent :
        ∀ x : M, IsSigmaCompact (connectedComponent x : Set M) := by
      -- Reduce the reverse implication to the componentwise `σ`-compactness statement.
      intro x
      exact isSigmaCompact_connectedComponent_of_paracompact_t2_euclidean (n := n) x
    letI : SigmaCompactSpace M :=
      sigmaCompactSpace_of_countable_sigmaCompact_connectedComponents hcount hcomponent
    -- A `σ`-compact Hausdorff Euclidean charted space is second-countable.
    exact ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
