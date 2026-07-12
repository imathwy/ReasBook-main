import Mathlib
import StacksProject_2024.Chap11.Lemma_11_4_9

open scoped TensorProduct
open Algebra.TensorProduct
open Matrix

universe u v w

namespace CSA

section

variable {k : Type u} [Field k]
variable {K : Type w} [Field K] [Algebra k K]

/-- Helper for Theorem 11.8.2: `Fin 1 × Fin n` reindexes to `Fin n` by discarding the unique left
coordinate. -/
private theorem fin_one_prod_equiv_left_inv (n : ℕ) (ij : Fin 1 × Fin n) :
    (0, ij.2) = ij := by
  -- The left coordinate lies in `Fin 1`, so it is uniquely determined.
  rcases ij with ⟨i, j⟩
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi]

/-- Helper for Theorem 11.8.2: the product index `Fin 1 × Fin n` canonically identifies with
`Fin n`. -/
private def fin_one_prod_equiv (n : ℕ) : Fin 1 × Fin n ≃ Fin n where
  toFun ij := ij.2
  invFun j := (0, j)
  left_inv := fin_one_prod_equiv_left_inv n
  right_inv := fun _ ↦ rfl

variable (A : CSA.{u, v} k)

/-- Helper for Theorem 11.8.2: scalar extension should identify a matrix algebra with the matrix
algebra over the scalar-extended coefficients. -/
noncomputable theorem baseChange_matrix_algEquiv_matrix_baseChange (n : ℕ) :
    K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin n) (Fin n) (A.baseChange K) := by
  -- Route correction: isolate the recurring transport/coercion mismatch here instead of forcing it
  -- back through the Brauer-equivalence proof. The intended proof follows Lemma 11.4.7: replace
  -- `K` by a `1 × 1` matrix algebra, apply `Matrix.kroneckerTMulAlgEquiv`, then reindex.
  -- TODO: build the intermediate `k`-algebra equivalence with the Lemma 11.4.7 pattern and then
  -- upgrade it to a `K`-algebra equivalence by checking compatibility with `includeLeft`.
  sorry

/-- Helper for Theorem 11.8.2: a matrix-stabilization witness over `k` should lift to one after
scalar extension to `K`. -/
noncomputable theorem baseChange_of_matrix_brauer_witness {B : CSA.{u, v} k} {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B) :
    Matrix (Fin n) (Fin n) (A.baseChange K) ≃ₐ[K] Matrix (Fin m) (Fin m) (B.baseChange K) := by
  -- Route correction: once the scalar-extension/matrix comparison is packaged, the lifted witness
  -- is just the same source witness sandwiched between those comparison equivalences.
  -- TODO: compose `baseChange_matrix_algEquiv_matrix_baseChange` on both sides with the scalar
  -- extension of `e`; the remaining work is the same `K`-linearity bridge isolated above.
  sorry

end

end CSA
