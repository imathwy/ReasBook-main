module

public import Book.Ch3.Algorithm_3_2_1.Iterates
public import Book.Ch3.Theorem_3_5.Error

public section

noncomputable section

open scoped Matrix.Energy

namespace ConjugateGradient

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The `v`th conjugate-gradient error, measured from the exact solution
`QuadraticOptimization.quadraticFunctionalMinimizer b A` of `A x = -b`. -/
@[expose]
def error
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (v : ℕ) :
    EuclideanSpace ℝ n :=
  QuadraticOptimization.error A b (iterates A b f₀ v).solution

/-- The initial conjugate-gradient error from `f₀` to the exact solution
`QuadraticOptimization.quadraticFunctionalMinimizer b A`. -/
@[expose]
def initialError (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  QuadraticOptimization.error A b f₀

/-- The `A`-energy norm of the `v`th conjugate-gradient error. -/
@[expose]
def energyNormError
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ) :
    ℝ :=
  QuadraticOptimization.energyNormError A b hA (iterates A b f₀ v).solution

/-- Unfolding lemma for `ConjugateGradient.energyNormError`. -/
theorem energyNormError_eq
    (A : Matrix n n ℝ) (b f₀ : EuclideanSpace ℝ n) (hA : A.PosDef) (v : ℕ) :
    energyNormError A b f₀ hA v = ‖error A b f₀ v‖_[A, hA] := by
  rfl

end ConjugateGradient
