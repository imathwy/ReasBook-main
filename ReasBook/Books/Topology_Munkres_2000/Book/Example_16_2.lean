module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic

public section

open scoped Topology

/-- The subset `[0, 1) ∪ {2}` of the real line. -/
def isolatedEndpointSet : Set ℝ := Set.Ico 0 1 ∪ {2}

/-- The point `2`, regarded as an element of `isolatedEndpointSet`. -/
def isolatedEndpoint : isolatedEndpointSet := ⟨2, by simp [isolatedEndpointSet]⟩

/-- The singleton containing `isolatedEndpoint`. -/
def isolatedPoint : Set isolatedEndpointSet := {isolatedEndpoint}

/-- Membership in `isolatedPoint` is equality of the real coordinate with `2`. -/
@[simp]
theorem mem_isolatedPoint (x : isolatedEndpointSet) :
    x ∈ isolatedPoint ↔ x.1 = 2 := by
  -- Singleton membership reduces to equality of the underlying real coordinates.
  simp only [isolatedPoint, Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [hx]
    rfl
  · intro hx
    apply Subtype.ext
    simpa only [isolatedEndpoint] using hx

/-- The subspace-topology assertion in Example 16.2: the point with coordinate `2`
is open in the topology on `isolatedEndpointSet` induced from the real line. -/
theorem isolatedPointIsOpenSubspace : IsOpen isolatedPoint := by
  -- Realize the singleton as the subtype preimage of the open interval `(3/2, 5/2)`.
  rw [Topology.IsInducing.subtypeVal.isOpen_iff]
  refine ⟨Set.Ioo (3 / 2 : ℝ) (5 / 2), isOpen_Ioo, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_Ioo, mem_isolatedPoint]
  constructor
  · intro hx
    have hxMem : x.1 ∈ Set.Ico (0 : ℝ) 1 ∪ {2} := x.property
    rcases hxMem with hxInterval | hxEndpoint
    · rcases hxInterval with ⟨_, hxOne⟩
      exfalso
      linarith
    · simpa only [Set.mem_singleton_iff] using hxEndpoint
  · intro hx
    rw [hx]
    norm_num

/-- Helper for Example 16.2: the distinguished endpoint has a point strictly below it. -/
lemma isolatedEndpointHasLower : ∃ a : isolatedEndpointSet, a < isolatedEndpoint := by
  -- The real number `0` lies in the interval component of the subtype.
  have hzero : (0 : ℝ) ∈ isolatedEndpointSet := by
    simp only [isolatedEndpointSet, Set.mem_union, Set.mem_Ico,
      Set.mem_singleton_iff]
    norm_num
  let a : isolatedEndpointSet := ⟨0, hzero⟩
  -- Its coordinate is strictly less than the endpoint coordinate `2`.
  refine ⟨a, ?_⟩
  norm_num [a, isolatedEndpoint]

/-- Helper for Example 16.2: averaging a point below the endpoint with `1` gives
a point in the interval component, strictly between that point and the endpoint. -/
lemma midpointToOneSpec (a : isolatedEndpointSet) (ha : a < isolatedEndpoint) :
    (a.1 + 1) / 2 ∈ isolatedEndpointSet ∧
      a.1 < (a.1 + 1) / 2 ∧ (a.1 + 1) / 2 < isolatedEndpoint.1 := by
  -- Membership of `a` splits into the interval component and the isolated endpoint.
  have haMem : a.1 ∈ Set.Ico (0 : ℝ) 1 ∪ {2} := a.property
  rcases haMem with haInterval | haEndpoint
  · rcases haInterval with ⟨haNonneg, haOne⟩
    -- The midpoint remains in `[0, 1)`.
    constructor
    · refine Or.inl ⟨?_, ?_⟩
      · linarith
      · linarith
    -- The same inequalities place it strictly between `a` and the endpoint.
    constructor
    · linarith
    · norm_num [isolatedEndpoint]
      linarith
  · -- The singleton branch would say that `a` is the endpoint, contradicting `ha`.
    simp only [Set.mem_singleton_iff] at haEndpoint
    exfalso
    have haCoord : a.1 < isolatedEndpoint.1 := ha
    rw [haEndpoint] at haCoord
    norm_num [isolatedEndpoint] at haCoord

/-- Helper for Example 16.2: every point below the distinguished endpoint has
another subtype point strictly between it and the endpoint. -/
lemma existsPointBetweenAndIsolatedEndpoint (a : isolatedEndpointSet)
    (ha : a < isolatedEndpoint) :
    ∃ b : isolatedEndpointSet, a < b ∧ b < isolatedEndpoint := by
  -- Package the midpoint only after its subtype membership has been established.
  obtain ⟨hmem, hab, hbEndpoint⟩ := midpointToOneSpec a ha
  let b : isolatedEndpointSet := ⟨(a.1 + 1) / 2, hmem⟩
  refine ⟨b, ?_, ?_⟩
  · exact hab
  · exact hbEndpoint

/-- Example 16.2 (2): The point with coordinate `2` is not open in the intrinsic
order topology on `isolatedEndpointSet`. -/
theorem isolatedPointNotIsOpenOrder :
    ¬ IsOpen[Preorder.topology isolatedEndpointSet] isolatedPoint := by
  -- Work locally with the intrinsic order topology named in the statement.
  letI : TopologicalSpace isolatedEndpointSet := Preorder.topology isolatedEndpointSet
  letI : OrderTopology isolatedEndpointSet := ⟨rfl⟩
  intro hOpen
  have hEndpointMem : isolatedEndpoint ∈ isolatedPoint := by
    simp only [isolatedPoint, Set.mem_singleton_iff]
  have hPointNhds : isolatedPoint ∈ 𝓝 isolatedEndpoint :=
    hOpen.mem_nhds hEndpointMem
  -- Every neighborhood contains a final interval ending at the endpoint.
  obtain ⟨a, ha, hIoc⟩ :=
    exists_Ioc_subset_of_mem_nhds hPointNhds isolatedEndpointHasLower
  obtain ⟨b, hab, hbEndpoint⟩ := existsPointBetweenAndIsolatedEndpoint a ha
  have hbIoc : b ∈ Set.Ioc a isolatedEndpoint := ⟨hab, le_of_lt hbEndpoint⟩
  have hbPoint : b ∈ isolatedPoint := hIoc hbIoc
  -- The interval point must equal the endpoint by singleton membership, a contradiction.
  have hbEq : b = isolatedEndpoint := by
    simpa only [isolatedPoint, Set.mem_singleton_iff] using hbPoint
  rw [hbEq] at hbEndpoint
  exact lt_irrefl isolatedEndpoint hbEndpoint
