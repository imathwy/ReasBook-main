module

public import Mathlib.LinearAlgebra.Matrix.Kronecker

public section

open scoped Kronecker

/- Definition 5.29. The source's tensor product of matrices is the existing
matrix Kronecker product `Matrix.kronecker`, written `A ⊗ₖ B`. The displayed
block formula is recovered by `Matrix.kronecker_apply`. -/
#check Matrix.kronecker

/- Source-facing notation for the matrix tensor product in Definition 5.29. -/
#check
  fun {l m n p α : Type*} [Mul α] (A : Matrix l m α) (B : Matrix n p α) ↦
    A ⊗ₖ B

/- Entrywise formula for the block-matrix description in Definition 5.29. -/
#check Matrix.kronecker_apply
