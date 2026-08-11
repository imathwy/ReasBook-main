import Mathlib

section Chapters

/-- Canonical Euclidean pairing on `Fin n → ℝ`, implemented by `dotProduct`. -/
noncomputable def finDot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  dotProduct x y

end Chapters
