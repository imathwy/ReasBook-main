module

public import Mathlib.Topology.Bases

public section

open Set

universe u

namespace TopologicalSpace

/-- A subbasis on `X` is a collection of subsets whose union is `X`. -/
def IsSubbasis {X : Type u} (S : Set (Set X)) : Prop :=
  ⋃₀ S = univ

/-- Every point belongs to a member of a subbasis. -/
theorem IsSubbasis.exists_mem {X : Type u} {S : Set (Set X)}
    (hS : IsSubbasis S) (x : X) : ∃ U ∈ S, x ∈ U := by
  rw [IsSubbasis, sUnion_eq_univ_iff] at hS
  exact hS x

end TopologicalSpace
