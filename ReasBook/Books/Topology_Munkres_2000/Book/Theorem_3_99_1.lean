module

public import Mathlib.Topology.Neighborhoods

public section

open Filter Set

universe u

/-- Helper for Theorem 3.99.1: the member sets of a filter, ordered by reverse inclusion,
form a directed order. -/
lemma Filter.orderDualMem_isDirectedOrder {α : Type u} (l : Filter α) :
    IsDirectedOrder (OrderDual {s : Set α // s ∈ l}) := by
  -- Intersections give common upper bounds in the reverse-inclusion order.
  constructor
  intro s t
  let u : {v : Set α // v ∈ l} := ⟨s.1 ∩ t.1, Filter.inter_mem s.2 t.2⟩
  refine ⟨(u : OrderDual {v : Set α // v ∈ l}), ?_, ?_⟩
  · exact inter_subset_left
  · exact inter_subset_right

/-- Helper for Theorem 3.99.1: the reverse-inclusion order on the member sets of a filter is
nonempty. -/
lemma Filter.orderDualMem_nonempty {α : Type u} (l : Filter α) :
    Nonempty (OrderDual {s : Set α // s ∈ l}) := by
  -- The universal set is a member of every filter.
  exact ⟨⟨Set.univ, Filter.univ_mem⟩⟩

/-- Helper for Theorem 3.99.1: every neighborhood of a point in `closure A` meets `A`. -/
lemma inter_nonempty_of_mem_closure_of_mem_nhds {X : Type u} [TopologicalSpace X]
    {A U : Set X} {x : X} (hx : x ∈ closure A) (hU : U ∈ nhds x) :
    (U ∩ A).Nonempty := by
  -- Frequent membership in `A` supplies a point lying in the given neighborhood and in `A`.
  obtain ⟨y, hyU, hyA⟩ := Filter.frequently_iff.1 (mem_closure_iff_frequently.1 hx) hU
  exact ⟨y, hyU, hyA⟩

/-- Helper for Theorem 3.99.1: choosing a point in every neighborhood yields a net converging to
the center point when neighborhoods are ordered by reverse inclusion. -/
lemma neighborhoodChoice_tendsto {X : Type u} [TopologicalSpace X] {x : X}
    (net : OrderDual {U : Set X // U ∈ nhds x} → X)
    (hnet : ∀ U, net U ∈ U.1) :
    Filter.Tendsto net Filter.atTop (nhds x) := by
  letI : Nonempty (OrderDual {U : Set X // U ∈ nhds x}) :=
    Filter.orderDualMem_nonempty (nhds x)
  letI : IsDirectedOrder (OrderDual {U : Set X // U ∈ nhds x}) :=
    Filter.orderDualMem_isDirectedOrder (nhds x)
  -- A neighborhood is eventually reached by using that neighborhood itself as the index.
  refine Filter.tendsto_atTop'.2 ?_
  intro U hU
  let i : OrderDual {V : Set X // V ∈ nhds x} := ⟨U, hU⟩
  refine ⟨i, ?_⟩
  intro j hij
  exact hij (hnet j)

/-- Theorem 3.99.1: A point belongs to the closure of `A` if and only if
there is a directed net of points of `A` converging to it. -/
theorem mem_closure_iff_exists_tendsto_net {X : Type u} [TopologicalSpace X]
    {A : Set X} {x : X} :
    x ∈ closure A ↔
      ∃ J : Type u, ∃ _ : Nonempty J, ∃ _ : PartialOrder J, ∃ _ : IsDirectedOrder J,
        ∃ net : J → X,
          (∀ α, net α ∈ A) ∧ Filter.Tendsto net Filter.atTop (nhds x) := by
  classical
  constructor
  · intro hx
    -- Index the net by neighborhoods and choose a point from each intersection with `A`.
    let J := OrderDual {U : Set X // U ∈ nhds x}
    letI : Nonempty J := Filter.orderDualMem_nonempty (nhds x)
    letI : PartialOrder J := inferInstance
    letI : IsDirectedOrder J := Filter.orderDualMem_isDirectedOrder (nhds x)
    let net : J → X := fun U ↦
      Classical.choose (inter_nonempty_of_mem_closure_of_mem_nhds hx U.2)
    have hnet_inter : ∀ U, net U ∈ U.1 ∩ A := by
      intro U
      exact Classical.choose_spec (inter_nonempty_of_mem_closure_of_mem_nhds hx U.2)
    have hnet_mem_A : ∀ U, net U ∈ A := by
      intro U
      exact (hnet_inter U).2
    have hnet_mem_neighborhood : ∀ U, net U ∈ U.1 := by
      intro U
      exact (hnet_inter U).1
    have hnet_tendsto : Filter.Tendsto net Filter.atTop (nhds x) :=
      neighborhoodChoice_tendsto net hnet_mem_neighborhood
    exact ⟨J, inferInstance, inferInstance, inferInstance, net, hnet_mem_A, hnet_tendsto⟩
  · rintro ⟨J, hNonempty, hPartialOrder, hDirected, net, hnet_mem_A, hnet_tendsto⟩
    letI : Nonempty J := hNonempty
    letI : PartialOrder J := hPartialOrder
    letI : IsDirectedOrder J := hDirected
    -- Eventual membership in `A` and convergence force the limit into its closure.
    exact mem_closure_of_tendsto hnet_tendsto (Filter.Eventually.of_forall hnet_mem_A)
