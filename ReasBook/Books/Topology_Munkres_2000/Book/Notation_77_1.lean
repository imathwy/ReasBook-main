module

universe u

/- Notation 77.1: In the decomposition `w = y₀ ++ [a] ++ y₁ ++ [a] ++ y₂`,
the textbook brackets around each `yᵢ` are visual delimiters only; each `yᵢ`
is a list fragment, not a singleton list. -/
#check fun {α : Type u} (y₀ y₁ y₂ : List (α × Bool)) (a : α × Bool) ↦
  y₀ ++ [a] ++ y₁ ++ [a] ++ y₂
