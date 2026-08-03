module

public import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Nat.SuccPred

public section

/-- Exercise 23.2: A union of a sequence of connected subsets with consecutive
nonempty intersections is connected. -/
theorem isConnected_iUnion_of_consecutive {X : Type u} [TopologicalSpace X]
    (A : ℕ → Set X) (hA : ∀ n, IsConnected (A n))
    (h_inter : ∀ n, (A n ∩ A (n + 1)).Nonempty) :
    IsConnected (⋃ n, A n) := by
  apply IsConnected.iUnion_of_chain hA
  simpa only [Nat.succ_eq_succ, Nat.succ_eq_add_one] using h_inter
