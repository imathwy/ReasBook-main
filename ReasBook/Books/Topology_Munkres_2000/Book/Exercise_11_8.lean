module

public import Mathlib.LinearAlgebra.Basis.VectorSpace

public section

universe u v

variable (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V] [Module K V]

/- Exercise 11.8 (a): Adjoining a vector outside the span of an independent set
preserves linear independence. -/
#check fun (A : Set V) (x : V) ↦
  (LinearIndepOn.id_insert :
    LinearIndepOn K id A → x ∉ Submodule.span K A → LinearIndepOn K id (insert x A))

/- Exercise 11.8 (b): The independent subsets of a vector space have a maximal
member under inclusion. -/
#check (exists_maximal_linearIndepOn' K (id : V → V) :
  ∃ A : Set V, LinearIndepOn K id A ∧
    ∀ B : Set V, A ⊆ B → LinearIndepOn K id B → A = B)

/- Exercise 11.8 (c): Every vector space has a basis. -/
#check (Module.Basis.exists_basis K V :
  ∃ A : Set V, Nonempty (Module.Basis A K V))
