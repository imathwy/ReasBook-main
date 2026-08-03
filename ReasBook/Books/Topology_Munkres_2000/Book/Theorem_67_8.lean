module

public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

public section

universe u

/-- Theorem 67.8. Any two finite bases of the same free abelian group have the same
number of elements. -/
theorem freeAbelianGroup_basisCard_eq {G : Type u} [AddCommGroup G] {m n : ℕ}
    (a : Module.Basis (Fin m) ℤ G) (b : Module.Basis (Fin n) ℤ G) : m = n := by
  simpa using mk_eq_mk_of_basis a b
