module

public import Mathlib.Data.Setoid.Partition

public section

universe u

open Set.PairwiseDisjoint

/-- Lemma 3.1: Two equivalence classes of a setoid are either disjoint or equal. -/
theorem Setoid.disjoint_or_eq_of_mem_classes {A : Type u} (r : Setoid A)
    {E E' : Set A} (hE : E ∈ r.classes) (hE' : E' ∈ r.classes) :
    Disjoint E E' ∨ E = E' :=
  (eq_or_disjoint r.isPartition_classes.pairwiseDisjoint hE hE').symm

end
