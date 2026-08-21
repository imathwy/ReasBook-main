import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

noncomputable section

variable {α : Type*} {n m : ℕ}

/-- `isChosenPseudoInverseAt A Aplus x` records that `Aplus x` is the chosen Moore-Penrose
pseudoinverse of `A x`. -/
abbrev isChosenPseudoInverseAt
    (A : α → Matrix (Fin n) (Fin m) ℝ)
    (Aplus : α → Matrix (Fin m) (Fin n) ℝ) (x : α) : Prop :=
  A x * Aplus x * A x = A x ∧
    Aplus x * A x * Aplus x = Aplus x ∧
    (A x * Aplus x).transpose = A x * Aplus x ∧
    (Aplus x * A x).transpose = Aplus x * A x
