module

public import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv

public section

universe u v

open Equiv

/-- Corollary 69.5. If a group has a free basis indexed by `Fin n`, then every
other free basis has an index type equivalent to `Fin n`. -/
theorem freeGroupBasisIndexEquivFin
    {G : Type u} {ι : Type v} [Group G]
    (n : ℕ) (basis : FreeGroupBasis (Fin n) G) (otherBasis : FreeGroupBasis ι G) :
    Nonempty (ι ≃ Fin n) := by
  exact ⟨ofFreeGroupEquiv (MulEquiv.trans otherBasis.repr.symm basis.repr)⟩
