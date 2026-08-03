module

public import Mathlib.Topology.Continuous

public section

open Filter

universe u v

/-- Helper for Theorem 3.99.2: the reverse inclusion order on the sets of a
filter basis, lifted to a larger universe, is directed. -/
lemma FilterBasis.isDirectedOrderULiftOrderDualSets {α : Type u} (B : FilterBasis α) :
    IsDirectedOrder (ULift.{v} (OrderDual B.sets)) := by
  -- A basis set inside the intersection is an upper bound in reverse inclusion.
  constructor
  intro a b
  obtain ⟨s, hs, hsub⟩ := B.inter_sets a.down.property b.down.property
  refine ⟨ULift.up (OrderDual.toDual ⟨s, hs⟩), ?_, ?_⟩
  · exact fun _ hz ↦ (hsub hz).1
  · exact fun _ hz ↦ (hsub hz).2

/-- Helper for Theorem 3.99.2: every set frequent in a filter contains every
term of some directed net tending to that filter. -/
lemma Filter.Frequently.existsDirectedNet {α : Type u} {l : Filter α} {s : Set α}
    (hs : ∃ᶠ x in l, x ∈ s) :
    ∃ net : ULift.{v} (OrderDual l.asBasis.sets) → α,
      Tendsto net atTop l ∧ ∀ j, net j ∈ s := by
  classical
  -- Choose a point of the frequent set in each member of the canonical basis.
  have hmeet (j : ULift.{v} (OrderDual l.asBasis.sets)) :
      ∃ x ∈ j.down.val, x ∈ s :=
    Filter.frequently_iff.mp hs j.down.property
  choose net hnetBasis hnetFrequent using hmeet
  refine ⟨net, ?_, hnetFrequent⟩
  -- Reverse inclusion makes every sufficiently late chosen point lie in a given filter set.
  rw [Filter.tendsto_iff_forall_eventually_mem]
  intro t ht
  let threshold : ULift.{v} (OrderDual l.asBasis.sets) :=
    ULift.up (OrderDual.toDual ⟨t, ht⟩)
  refine (eventually_ge_atTop threshold).mono ?_
  intro j hj
  exact hj (hnetBasis j)

/-- Helper for Theorem 3.99.2: a map preserving limits of all directed nets is
continuous at each point. -/
lemma continuousAtOfPreservesDirectedNetLimits {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {x : X}
    (hpreserves :
      ∀ {J : Type (max u v)} [Nonempty J] [Preorder J] [IsDirectedOrder J]
        (net : J → X) (x : X) (hnet : Tendsto net atTop (nhds x)),
        Tendsto (f ∘ net) atTop (nhds (f x))) :
    ContinuousAt f x := by
  -- A failure of continuity supplies a target neighborhood missed frequently near `x`.
  by_contra hcontinuous
  obtain ⟨t, ht, hfrequent⟩ :=
    Filter.not_tendsto_iff_exists_frequently_notMem.mp hcontinuous
  obtain ⟨net, hnet, hnetOutside⟩ :=
    Filter.Frequently.existsDirectedNet (α := X) (l := nhds x) hfrequent
  letI : IsDirectedOrder (ULift.{v} (OrderDual (nhds x).asBasis.sets)) :=
    FilterBasis.isDirectedOrderULiftOrderDualSets (nhds x).asBasis
  -- Preservation forces the image net eventually into the neighborhood it always misses.
  have hnetInside : ∀ᶠ j in atTop, f (net j) ∈ t := by
    simpa only [Function.comp_apply] using
      (hpreserves net x hnet).eventually_mem ht
  obtain ⟨j, hj⟩ := hnetInside.exists
  exact hnetOutside j hj

/-- Theorem 3.99.2: A map is continuous if and only if it preserves the limit
of every net indexed by a nonempty directed preordered type. -/
theorem continuous_iff_preserves_net_limits {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔
      ∀ {J : Type (max u v)} [Nonempty J] [Preorder J] [IsDirectedOrder J]
        (net : J → X) (x : X) (hnet : Tendsto net atTop (nhds x)),
        Tendsto (f ∘ net) atTop (nhds (f x)) := by
  constructor
  · intro hf J _ _ _ net x hnet
    -- Continuity at the limit point composes with the convergence of the net.
    exact (hf.tendsto x).comp hnet
  · intro hpreserves
    -- The pointwise counterexample-net argument gives continuity everywhere.
    rw [continuous_iff_continuousAt]
    intro x
    exact continuousAtOfPreservesDirectedNetLimits hpreserves
