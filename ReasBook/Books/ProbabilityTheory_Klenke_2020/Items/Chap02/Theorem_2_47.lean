import ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_41

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory SimpleGraph
open scoped unitInterval
open unitInterval

universe u

variable {Ω : Type u} {d : ℕ}

private def latticeAdj (d : ℕ) (x y : LatticePoint d) : Prop :=
  ∃ i : Fin d, Int.natAbs (x i - y i) = 1 ∧ ∀ j : Fin d, j ≠ i → x j = y j

private theorem latticeAdj_symm (d : ℕ) : Symmetric (latticeAdj d) := by
  intro x y hxy
  rcases hxy with ⟨i, hi, hxy⟩
  refine ⟨i, ?_, ?_⟩
  · have hneg : y i - x i = -(x i - y i) := by omega
    rw [hneg, Int.natAbs_neg]
    exact hi
  · intro j hj
    exact (hxy j hj).symm

private theorem latticeAdj_irrefl (d : ℕ) : Std.Irrefl (latticeAdj d) := by
  exact ⟨fun x ↦ by
    rintro ⟨i, hi, _⟩
    simp at hi⟩

/-- The nearest-neighbor graph on `ℤ^d`. Two lattice sites are adjacent exactly when they differ
by `1` in one coordinate and agree in all others. -/
def latticeGraph (d : ℕ) : SimpleGraph (LatticePoint d) where
  Adj := latticeAdj d
  symm := latticeAdj_symm d
  loopless := latticeAdj_irrefl d

/-- Adjacency in `latticeGraph d` is the nearest-neighbour relation on `ℤ^d`. -/
theorem latticeGraph_adj_iff (x y : LatticePoint d) :
    (latticeGraph d).Adj x y ↔
      ∃ i : Fin d, Int.natAbs (x i - y i) = 1 ∧ ∀ j : Fin d, j ≠ i → x j = y j :=
  Iff.rfl

/-- The open subgraph determined by a random set of lattice bonds. Intersecting with the edge set
of `latticeGraph d` keeps the construction pointwise faithful to bond percolation on `ℤ^d`. -/
def openBondGraph
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) : Ω → SimpleGraph (LatticePoint d) :=
  fun ω ↦ fromEdgeSet (openEdges ω ∩ (latticeGraph d).edgeSet)

/-- The connection event for bond percolation on `ℤ^d`: two sites are connected exactly when they
lie in the same connected component of the corresponding open subgraph. -/
def bondConnectionEvent
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) :
    LatticePoint d → LatticePoint d → Set Ω :=
  fun x y ↦ {ω | (openBondGraph openEdges ω).Reachable x y}

/-- The bond-percolation connection event is reachability in the open subgraph. -/
theorem bondConnectionEvent_eq_reachable
    (openEdges : Ω → Set (Sym2 (LatticePoint d))) (x y : LatticePoint d) :
    bondConnectionEvent openEdges x y =
      {ω | (openBondGraph openEdges ω).Reachable x y} :=
  rfl

/-- The number of distinct infinite open clusters in a configuration, obtained by counting the
distinct infinite sets that occur among the open clusters of lattice sites. This realizes the
textbook random variable `N`. -/
noncomputable def infiniteOpenClusterCount
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) : Ω → ℕ∞ :=
  fun ω ↦
    {C : Set (LatticePoint d) | ∃ x : LatticePoint d, C = cluster x ω ∧ Set.Infinite C}.encard

/-- The defining formula for `infiniteOpenClusterCount`. -/
theorem infiniteOpenClusterCount_def
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) :
    infiniteOpenClusterCount cluster =
      fun ω ↦
        {C : Set (LatticePoint d) | ∃ x : LatticePoint d, C = cluster x ω ∧ Set.Infinite C}.encard :=
  rfl

/-- The event that a configuration has at most one infinite open cluster, expressed canonically as
`{N ≤ 1}` for the random variable counting distinct infinite open clusters. -/
def atMostOneInfiniteOpenClusterEvent
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) : Set Ω :=
  {ω | infiniteOpenClusterCount cluster ω ≤ 1}

/-- Membership in `atMostOneInfiniteOpenClusterEvent` means that any two infinite open clusters
coincide. -/
theorem mem_atMostOneInfiniteOpenClusterEvent_iff
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) (ω : Ω) :
    ω ∈ atMostOneInfiniteOpenClusterEvent cluster ↔
      ∀ ⦃x y : LatticePoint d⦄,
        Set.Infinite (cluster x ω) →
        Set.Infinite (cluster y ω) →
        cluster x ω = cluster y ω := by
  let s : Set (Set (LatticePoint d)) :=
    {C | ∃ x : LatticePoint d, C = cluster x ω ∧ Set.Infinite C}
  change s.encard ≤ 1 ↔ _
  rw [Set.encard_le_one_iff]
  constructor
  · intro hs x y hx hy
    exact hs _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
  · intro h C D hC hD
    rcases hC with ⟨x, rfl, hx⟩
    rcases hD with ⟨y, rfl, hy⟩
    exact h hx hy

/-- The direct uniqueness event agrees with the textbook event `{N ≤ 1}`. -/
theorem atMostOneInfiniteOpenClusterEvent_eq_setOf_infiniteOpenClusterCount_le_one
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) :
    atMostOneInfiniteOpenClusterEvent cluster =
      {ω | infiniteOpenClusterCount cluster ω ≤ 1} :=
  rfl

-- Proof sketch: this is the Burton--Keane uniqueness theorem for Bernoulli bond percolation on
-- `ℤ^d`. One shows first that the number of infinite open clusters is almost surely constant,
-- then excludes every finite value `m ≥ 2` by a local modification argument, and finally rules
-- out `∞` using the trifurcation-point counting argument.
/-- Theorem 2.47: for Bernoulli bond percolation on the nearest-neighbor bonds of `ℤ^d`, the
probability that the number `N` of infinite open clusters satisfies `N ≤ 1` is equal to `1`. -/
theorem probability_infiniteOpenClusterCount_le_one
    [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (openEdges : Ω → Set (Sym2 (LatticePoint d)))
    (p : unitInterval)
    (hber : IsSetBernoulli openEdges (latticeGraph d).edgeSet p (μ : Measure Ω)) :
    μ {ω | infiniteOpenClusterCount (openCluster (bondConnectionEvent openEdges)) ω ≤ 1} = 1 := by
  sorry

/-- Uniqueness-form restatement of Theorem 2.47. -/
theorem probability_atMostOneInfiniteOpenCluster_eq_one
    [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (openEdges : Ω → Set (Sym2 (LatticePoint d)))
    (p : unitInterval)
    (hber : IsSetBernoulli openEdges (latticeGraph d).edgeSet p (μ : Measure Ω)) :
    μ (atMostOneInfiniteOpenClusterEvent (openCluster (bondConnectionEvent openEdges))) = 1 := by
  simpa [atMostOneInfiniteOpenClusterEvent_eq_setOf_infiniteOpenClusterCount_le_one] using
    probability_infiniteOpenClusterCount_le_one μ openEdges p hber
