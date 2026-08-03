module

public import Mathlib.LinearAlgebra.Basis.Basic

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.FreeModule.PID

public section

universe u

/-- Theorem 67.2. If `A` is a free abelian group of rank `n`, then any subgroup
`B` of `A` is a free abelian group of rank at most `n`. -/
theorem freeAbelianSubgroup_basis {A : Type u} [AddCommGroup A] {n : ℕ}
    (a : Module.Basis (Fin n) ℤ A) (B : AddSubgroup A) :
    ∃ (m : ℕ) (_ : Module.Basis (Fin m) ℤ B), m ≤ n := by
  obtain ⟨m, normalForm⟩ := Submodule.smithNormalForm a B.toIntSubmodule
  refine ⟨m, normalForm.bN, ?_⟩
  simpa using Fintype.card_le_of_injective normalForm.f normalForm.f.injective
