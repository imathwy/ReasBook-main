module

public import Topology_Munkres_2000.Book.Corollary_50_3
public import Topology_Munkres_2000.Book.Example_50_2

public section

universe u

/-- Helper for Example 50.6: deleting both endpoints from an embedded arc leaves
a connected set. -/
lemma embeddedArc_range_diff_endpoints_isConnected
    {X : Type u} [TopologicalSpace X] (a : unitInterval → X)
    (ha : Topology.IsEmbedding a) :
    IsConnected (Set.range a \ {a 0, a 1}) := by
  -- Identify the deleted-endpoint range with the image of the open unit interval.
  have hrange : Set.range a \ {a 0, a 1} = a '' Set.Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, ht⟩
      have hatZero : a t ≠ a 0 := by
        intro h
        exact ht (Set.mem_insert_iff.mpr (Or.inl h))
      have hatOne : a t ≠ a 1 := by
        intro h
        exact ht (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h)))
      have htZero : t ≠ 0 := fun h ↦ hatZero (congrArg a h)
      have htOne : t ≠ 1 := fun h ↦ hatOne (congrArg a h)
      exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr htZero,
        unitInterval.lt_one_iff_ne_one.mpr htOne⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨Set.mem_range_self t, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha.injective.ne (ne_of_gt ht.1), ha.injective.ne (ne_of_lt ht.2)⟩
  rw [hrange]
  -- Connectedness of `Ioo` is preserved by the continuous embedded parameterization.
  exact (isConnected_Ioo (show (0 : unitInterval) < 1 from zero_lt_one)).image
    a ha.continuous.continuousOn

/-- Helper for Example 50.6: a point of the controlled set outside a frontier
bound is omitted from the closure of the complementary component. -/
lemma not_mem_closure_connectedComponentIn_of_frontier_subset
    {X : Type u} [TopologicalSpace X] {Y B : Set X} {x y : X}
    (hyY : y ∈ Y) (hyB : y ∉ B)
    (hfrontier : frontier (connectedComponentIn Yᶜ x) ⊆ B) :
    y ∉ closure (connectedComponentIn Yᶜ x) := by
  intro hyClosure
  -- Split closure membership into component membership and frontier membership.
  rw [closure_eq_self_union_frontier] at hyClosure
  rcases hyClosure with hyComponent | hyFrontier
  · exact (connectedComponentIn_subset Yᶜ x hyComponent) hyY
  · exact hyB (hfrontier hyFrontier)

namespace Example50_6

/-- Helper for Example 50.6: in a locally connected space, the frontier of a
component of a closed-set complement lies in the closed set. -/
lemma frontier_connectedComponentIn_compl_subset
    {X : Type u} [TopologicalSpace X] [LocallyConnectedSpace X]
    (Y : Set X) (hY : IsClosed Y) (x : X) :
    frontier (connectedComponentIn Yᶜ x) ⊆ Y := by
  intro z hz
  -- The component is open, so none of its points can lie in its frontier.
  have hcomponentOpen : IsOpen (connectedComponentIn Yᶜ x) :=
    hY.isOpen_compl.connectedComponentIn
  have hzNotMem : z ∉ connectedComponentIn Yᶜ x := by
    intro hzMem
    have hzInterior : z ∈ interior (connectedComponentIn Yᶜ x) :=
      hcomponentOpen.interior_eq.symm ▸ hzMem
    exact (mem_frontier_iff_notMem_interior hzMem).mp hz hzInterior
  -- Outside `Y`, the point belongs to another open complementary component.
  by_contra hzY
  have hzOwnComponent : z ∈ connectedComponentIn Yᶜ z :=
    mem_connectedComponentIn hzY
  have hownOpen : IsOpen (connectedComponentIn Yᶜ z) :=
    hY.isOpen_compl.connectedComponentIn
  have hzClosure : z ∈ closure (connectedComponentIn Yᶜ x) :=
    frontier_subset_closure hz
  obtain ⟨y, hyOwn, hyComponent⟩ :=
    mem_closure_iff.mp hzClosure (connectedComponentIn Yᶜ z) hownOpen hzOwnComponent
  -- Intersecting complementary components coincide, contradicting the first step.
  have heq : connectedComponentIn Yᶜ x = connectedComponentIn Yᶜ z :=
    (connectedComponentIn_eq hyComponent).trans (connectedComponentIn_eq hyOwn).symm
  exact hzNotMem (heq ▸ hzOwnComponent)

end Example50_6
