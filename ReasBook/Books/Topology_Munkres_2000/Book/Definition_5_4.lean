module

import Topology_Munkres_2000.Book.Definition_5_3.CartesianProduct
import Mathlib.Data.PNat.Basic

universe u

open scoped CartesianProduct

/- Definition 5.4 (1): An `ω`-tuple, sequence, or infinite sequence of
elements of `X` is a function `ℕ+ → X`. -/
#check fun (X : Type u) ↦ (ℕ+ → X)

/- Its `i`th coordinate is its value at `i`. -/
#check fun {X : Type u} (x : ℕ+ → X) (i : ℕ+) ↦ x i

/- Definition 5.4 (2): The Cartesian product of a positive-integer-indexed
family `A : ℕ+ → Set X` is `∏ i, A i`. -/
#check fun {X : Type u} (A : ℕ+ → Set X) ↦ ∏ i, A i

/- Its elements are exactly the functions whose value at every index `i`
lies in `A i`. -/
#check fun {X : Type u} (A : ℕ+ → Set X) (x : ℕ+ → X) ↦
  (Set.mem_univ_pi : x ∈ ∏ i, A i ↔ ∀ i, x i ∈ A i)
