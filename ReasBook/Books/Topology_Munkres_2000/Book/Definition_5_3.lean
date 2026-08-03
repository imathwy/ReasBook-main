module

public import Topology_Munkres_2000.Book.Definition_5_3.CartesianProduct
import Mathlib.Data.PNat.Basic

universe u

open scoped CartesianProduct

/- Definition 5.3 (1): For a positive integer `m`, an `m`-tuple of elements
of `X` is a function from the positive interval `Set.Icc 1 m` to `X`. -/
#check fun (m : ℕ+) (X : Type u) ↦ (Set.Icc 1 m → X)

/- Definition 5.3 (2): The `i`th coordinate of an `m`-tuple `x` is the value
`x i`. -/
#check fun {m : ℕ+} {X : Type u} (x : Set.Icc 1 m → X) (i : Set.Icc 1 m) ↦ x i

/- Definition 5.3 (3): The Cartesian product of a family
`A : Set.Icc 1 m → Set X` is `∏ i, A i`. -/
#check fun {m : ℕ+} {X : Type u} (A : Set.Icc 1 m → Set X) ↦ ∏ i, A i

/- Definition 5.3 (4): Membership in the Cartesian product means that every
coordinate `x i` belongs to the corresponding factor `A i`. -/
#check fun {m : ℕ+} {X : Type u} (A : Set.Icc 1 m → Set X)
    (x : Set.Icc 1 m → X) ↦
  (Set.mem_univ_pi : x ∈ ∏ i, A i ↔ ∀ i, x i ∈ A i)
