module

public import Book.Ch5.Definition_5_1_1
public import Mathlib.LinearAlgebra.Matrix.Diagonal

public section

open scoped Matrix

noncomputable section

namespace Matrix

/-- The Fourier-diagonal projection of `A` obtained by conjugating into the Chapter 5
Fourier basis, discarding off-diagonal entries, and conjugating back. -/
@[expose] def fourierDiagonalProjection {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (fourierMatrix n)ᴴ * diagonal (((fourierMatrix n) * A * (fourierMatrix n)ᴴ).diag) *
    fourierMatrix n

/-- The defining Fourier-diagonal formula for `Matrix.fourierDiagonalProjection`. -/
theorem fourierDiagonalProjection_def {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    fourierDiagonalProjection A =
      (fourierMatrix n)ᴴ * diagonal (((fourierMatrix n) * A * (fourierMatrix n)ᴴ).diag) *
        fourierMatrix n :=
  rfl

end Matrix
