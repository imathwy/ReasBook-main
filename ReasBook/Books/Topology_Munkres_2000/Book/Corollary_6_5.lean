module

public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite

public section

universe u

/-- Corollary 6.5. If a set `A` is equivalent to both `Fin m` and `Fin n`, then
its cardinality indices agree: `m = n`. -/
theorem equivFin_index_eq {α : Type u} {A : Set α} {m n : ℕ}
    (hm : Nonempty (A ≃ Fin m)) (hn : Nonempty (A ≃ Fin n)) : m = n := by
  obtain ⟨em⟩ := hm
  obtain ⟨en⟩ := hn
  exact (Nat.card_eq_of_equiv_fin em).symm.trans (Nat.card_eq_of_equiv_fin en)
