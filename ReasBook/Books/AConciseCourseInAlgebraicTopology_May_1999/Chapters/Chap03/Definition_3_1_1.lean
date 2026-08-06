module

public import Mathlib.Topology.Connected.LocPathConnected

public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Definition 3.1.1: local path connectedness means that every neighborhood `U` of a point `x`
contains a smaller neighborhood `V` of `x` whose points can be joined to `x` by a path staying
inside `U`. -/
theorem locPathConnectedSpace_iff_has_smaller_joinedIn_neighborhoods :
    LocPathConnectedSpace X ↔
      ∀ x : X, ∀ U : Set X, U ∈ nhds x →
        ∃ V : Set X, V ∈ nhds x ∧ V ⊆ U ∧ ∀ y : X, y ∈ V → JoinedIn U x y := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  constructor
  · intro h x U hU
    -- Replace the given neighborhood by an open neighborhood inside it.
    rcases mem_nhds_iff.mp hU with ⟨u, huU, huOpen, hxu⟩
    refine ⟨pathComponentIn u x, ?_, pathComponentIn_subset.trans huU, ?_⟩
    · -- The standard path-component neighborhood criterion supplies the smaller neighborhood.
      exact h x u huOpen hxu
    · -- Membership in `pathComponentIn u x` gives a path in `u`, which enlarges to one in `U`.
      intro y hy
      exact JoinedIn.mono hy huU
  · intro h x u huOpen hxu
    -- Apply the textbook neighborhood condition to the open neighborhood `u`.
    rcases h x u (huOpen.mem_nhds hxu) with ⟨V, hVnhds, hVu, hJoined⟩
    -- Every point of `V` lies in the path component of `x` inside `u`.
    refine Filter.mem_of_superset hVnhds ?_
    intro y hy
    exact hJoined y hy
