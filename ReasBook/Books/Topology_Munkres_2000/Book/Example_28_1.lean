module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Mathlib.Topology.Instances.PNat
public import Mathlib.Topology.Order

public section

/-- The product of the positive integers with a two-point indiscrete space. -/
abbrev PNatIndiscretePair := ℕ+ × WithTopology Bool ⊤

namespace PNatIndiscretePair

/-- Example 28.1 (1): Every nonempty subset of `PNatIndiscretePair` has an accumulation point. -/
theorem existsAccPtOfNonempty (s : Set PNatIndiscretePair) (hs : s.Nonempty) :
    ∃ x, AccPt x (Filter.principal s) := by
  -- Choose a point of the set and flip its Boolean coordinate inside the same fiber.
  obtain ⟨x, hx⟩ := hs
  let y : PNatIndiscretePair :=
    (x.1, WithTopology.toTopology ⊤ (!WithTopology.ofTopology x.2))
  have hxy : Inseparable x y := by
    refine Inseparable.prod Inseparable.rfl (Inseparable.all _ _)
  have hne : x ≠ y := by
    intro h
    have hsnd := congrArg (fun z : PNatIndiscretePair ↦ WithTopology.ofTopology z.2) h
    simp [y] at hsnd
  -- Inseparability transports each neighborhood of the flipped point back to the chosen point.
  refine ⟨y, accPt_iff_nhds.2 ?_⟩
  intro U hU
  rw [← hxy.nhds_eq] at hU
  exact ⟨x, ⟨mem_of_mem_nhds hU, hx⟩, hne⟩

/-- Example 28.1 (1): The space `PNatIndiscretePair` is limit point compact. -/
instance instLimitPointCompactSpace : LimitPointCompactSpace PNatIndiscretePair := by
  -- The stronger nonempty-set result applies because every infinite set is nonempty.
  refine ⟨fun s hs ↦ existsAccPtOfNonempty s hs.nonempty⟩

/-- The open fiber over a positive integer. -/
def fiber (n : ℕ+) : Set PNatIndiscretePair :=
  {x | x.1 = n}

/-- Every positive-integer fiber is open. -/
theorem isOpen_fiber (n : ℕ+) : IsOpen (fiber n) := by
  -- A fiber is the preimage of an open singleton under the first projection.
  exact (isOpen_discrete ({n} : Set ℕ+)).preimage continuous_fst

/-- The positive-integer fibers cover `PNatIndiscretePair`. -/
theorem iUnion_fiber : ⋃ n : ℕ+, fiber n = Set.univ := by
  -- Every product point belongs to the fiber indexed by its first coordinate.
  ext x
  simp [fiber]

/-- No finite subfamily of the positive-integer fibers covers the space. -/
theorem fiber_noFiniteSubcover (I : Finset ℕ+) :
    ¬ (Set.univ : Set PNatIndiscretePair) ⊆ ⋃ n ∈ I, fiber n := by
  -- Choose a positive integer omitted by the finite index set.
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset I
  intro hcover
  -- A point over that omitted index cannot lie in the alleged finite subcover.
  have hmem := hcover (Set.mem_univ (n, WithTopology.toTopology ⊤ false))
  simp [fiber, hn] at hmem

/-- Example 28.1 (2): The space `PNatIndiscretePair` is not compact. -/
instance instNoncompactSpace : NoncompactSpace PNatIndiscretePair := by
  -- Compactness would extract a finite subcover from the open fiber cover.
  refine ⟨fun hcompact ↦ ?_⟩
  have hcover : (Set.univ : Set PNatIndiscretePair) ⊆ ⋃ n : ℕ+, fiber n := by
    rw [iUnion_fiber]
  obtain ⟨I, hI⟩ := hcompact.elim_finite_subcover fiber isOpen_fiber hcover
  -- The extracted subcover contradicts the missing-fiber argument.
  exact fiber_noFiniteSubcover I hI

end PNatIndiscretePair
