module

public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Instances.Real.Lemmas

public section

open Set

universe u

/- Exercise 17.19 (1): The boundary of `A` is
`closure A ∩ closure Aᶜ`. -/
#check frontier_eq_closure_inter_closure

/- Exercise 17.19 (2): The interior and boundary of a set are disjoint. -/
#check disjoint_interior_frontier

/- Exercise 17.19 (3): The closure of a set is the union of its interior and
boundary. -/
#check closure_eq_interior_union_frontier

/- Exercise 17.19 (4): A set has empty boundary if and only if it is both open
and closed. -/
#check isClopen_iff_frontier_eq_empty

/-- Exercise 17.19 (5): A set is open if and only if its boundary is the part
of its closure outside the set. -/
theorem isOpen_iff_frontier_eq_closure_sdiff {X : Type u} [TopologicalSpace X]
    (U : Set X) : IsOpen U ↔ frontier U = closure U \ U := by
  constructor
  · -- For an open set, the standard frontier formula gives the equality directly.
    intro hU
    exact hU.frontier_eq
  · -- Rewrite the frontier as a set difference, which is disjoint from the set itself.
    intro hU
    rw [← disjoint_frontier_iff_isOpen, hU]
    exact Set.disjoint_sdiff_left

/- Exercise 17.19 (6): The punctured real line is open. -/
#check isOpen_compl_singleton

/-- Exercise 17.19 (6): The punctured real line is not the interior of its
closure. -/
theorem compl_singleton_zero_ne_interior_closure :
    ({0}ᶜ : Set ℝ) ≠ interior (closure ({0}ᶜ : Set ℝ)) := by
  -- The punctured real line is dense, so the interior of its closure is all of `ℝ`.
  rw [closure_compl_singleton 0, interior_univ]
  -- The point `0` witnesses that the punctured line is not the universal set.
  intro hU
  have h0 : (0 : ℝ) ∈ ({0}ᶜ : Set ℝ) := hU.symm ▸ Set.mem_univ 0
  exact h0 (Set.mem_singleton 0)
