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

/-- Chap11 Theorem 11 8 2 BaseChangeMatrix: scalar extension identifies a matrix algebra with the
matrix algebra over the scalar-extended coefficients. -/
noncomputable def baseChange_matrix_algEquiv_matrix_baseChange (n : ℕ) :
    K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin n) (Fin n) (A.baseChange K) :=
  -- Route correction: isolate the recurring transport/coercion mismatch here instead of forcing it
  -- back through the Brauer-equivalence proof. The intended proof follows Lemma 11.4.7: replace
  -- `K` by a `1 × 1` matrix algebra, apply `Matrix.kroneckerTMulAlgEquiv`, then reindex.
  let eK : K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K :=
    ((Matrix.reindexAlgEquiv K K finOneEquiv).trans uniqueAlgEquiv).symm
  let eTensor :
      K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        Matrix (Fin 1) (Fin 1) K ⊗[k] Matrix (Fin n) (Fin n) A :=
    Algebra.TensorProduct.congr eK
      (AlgEquiv.refl : Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin n) (Fin n) A)
  let eKronecker :
      Matrix (Fin 1) (Fin 1) K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        Matrix (Fin 1 × Fin n) (Fin 1 × Fin n) (K ⊗[k] A) :=
    Matrix.kroneckerTMulAlgEquiv (Fin 1) (Fin n) k K K A
  -- Repackage the left scalar factor as a `1 × 1` matrix algebra, apply the Kronecker tensor
  -- equivalence, and then collapse the product index using the dedicated helper equivalence.
  eTensor.trans <|
    eKronecker.trans <|
      Matrix.reindexAlgEquiv K (A.baseChange K) (fin_one_prod_equiv n)

/-- Helper for Theorem 11.8.2: a matrix-stabilization witness over `k` should lift to one after
scalar extension to `K`. -/
noncomputable def baseChange_of_matrix_brauer_witness {B : CSA.{u, v} k} {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) A ≃ₐ[k] Matrix (Fin m) (Fin m) B) :
    Matrix (Fin n) (Fin n) (A.baseChange K) ≃ₐ[K] Matrix (Fin m) (Fin m) (B.baseChange K) :=
  -- Route correction: once the scalar-extension/matrix comparison is packaged, the lifted witness
  -- is just the same source witness sandwiched between those comparison equivalences.
  let eTensor :
      K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        K ⊗[k] Matrix (Fin m) (Fin m) B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
  -- Move scalar extension through both matrix algebras, apply the original witness over `k`,
  -- and transport back to the canonical base-changed coefficient algebras.
  (A.baseChange_matrix_algEquiv_matrix_baseChange (K := K) n).symm.trans <|
    eTensor.trans <|
      B.baseChange_matrix_algEquiv_matrix_baseChange (K := K) m

end

end CSA
