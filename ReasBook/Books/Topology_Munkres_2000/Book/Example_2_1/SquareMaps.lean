module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Restrict

public section

/-- The square function from the real numbers to the real numbers. -/
@[expose]
def realSquare (x : ℝ) : ℝ := x ^ 2

/-- The restriction of `realSquare` to the nonnegative real numbers. -/
@[expose]
def nnrealSquareToReal : NNReal → ℝ := Set.restrict (Set.Ici (0 : ℝ)) realSquare

/-- The square function from the real numbers to the nonnegative real numbers. -/
@[expose]
def realSquareToNNReal : ℝ → NNReal :=
  Set.codRestrict realSquare (Set.Ici (0 : ℝ)) sq_nonneg

/-- Evaluating `nnrealSquareToReal` agrees with squaring the underlying real number. -/
@[simp]
theorem nnrealSquareToReal_apply (x : NNReal) : nnrealSquareToReal x = (x : ℝ) ^ 2 := by
  -- Compute the domain restriction, then expose the original squaring rule.
  rw [nnrealSquareToReal, Set.restrict_apply, realSquare]
  rfl

/-- The underlying real number of `realSquareToNNReal x` is `realSquare x`. -/
@[simp]
theorem realSquareToNNReal_coe (x : ℝ) :
    (realSquareToNNReal x : ℝ) = realSquare x := by
  -- Project the value of the codomain restriction without reopening its proof field.
  exact Set.val_codRestrict_apply realSquare (Set.Ici (0 : ℝ)) sq_nonneg x
