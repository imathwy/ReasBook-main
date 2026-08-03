module

public import Topology_Munkres_2000.Book.Exercise_5_3.CartesianProduct
public import Mathlib.Data.PNat.Basic

public section

universe u

/- Exercise 5.3 (a): Coordinatewise inclusion of families implies inclusion
of their Cartesian products. -/
#check fun {X : Type u} {A B : ℕ+ → Set X} (h : ∀ i, B i ⊆ A i) ↦
  (Set.pi_mono fun i _ ↦ h i : Set.univ.pi B ⊆ Set.univ.pi A)

/- Exercise 5.3 (b): If the Cartesian product of `B` is nonempty, inclusion
of the product of `B` in the product of `A` implies coordinatewise inclusion. -/
#check fun {X : Type u} {A B : ℕ+ → Set X} (hB : (Set.univ.pi B).Nonempty) ↦
  (Set.univ_pi_subset_iff hB :
    Set.univ.pi B ⊆ Set.univ.pi A ↔ ∀ i, B i ⊆ A i)

/- Exercise 5.3 (c): A Cartesian product is nonempty exactly when every
coordinate set is nonempty. -/
#check fun {X : Type u} (A : ℕ+ → Set X) ↦
  (Set.univ_pi_nonempty_iff : (Set.univ.pi A).Nonempty ↔ ∀ i, (A i).Nonempty)

/- Exercise 5.3 (d), union: The union of two Cartesian products is contained
in the Cartesian product of the coordinatewise unions. -/
#check fun {X : Type u} (A B : ℕ+ → Set X) ↦
  (Set.union_univ_pi_subset A B :
    Set.univ.pi A ∪ Set.univ.pi B ⊆ Set.univ.pi (fun i ↦ A i ∪ B i))

/- Exercise 5.3 (d), intersection: The intersection of two Cartesian products
equals the Cartesian product of the coordinatewise intersections. -/
#check fun {X : Type u} (A B : ℕ+ → Set X) ↦
  (Set.pi_inter_distrib.symm :
    Set.univ.pi A ∩ Set.univ.pi B = Set.univ.pi (fun i ↦ A i ∩ B i))
