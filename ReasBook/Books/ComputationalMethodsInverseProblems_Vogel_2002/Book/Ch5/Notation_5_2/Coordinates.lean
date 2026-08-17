module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Matrix.Basic

public section

namespace Complex.FiniteDimensional

/-- Scoped notation for the textbook finite complex coordinate space `ℂ^n`. -/
scoped notation "ℂ^[" n "]" => EuclideanSpace ℂ (Fin n)

/-- Scoped notation for complex-valued `n_x × n_y` arrays with finite
coordinate sets. -/
scoped notation "ℂ^[" n_x ", " n_y "]" => Matrix (Fin n_x) (Fin n_y) ℂ

end Complex.FiniteDimensional
