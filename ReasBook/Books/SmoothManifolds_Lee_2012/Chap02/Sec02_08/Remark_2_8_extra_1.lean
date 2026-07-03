import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Remark 2.8-extra-1: In the terminology of this text, a "function" is a map whose codomain is
`ℝ` or `EuclideanSpace ℝ (Fin k)` for some `k > 1`, while the more general words "map" and
"mapping" may refer to maps between arbitrary manifolds. -/
def is_book_function (M : Type u) {Y : Type} (f : M → Y) : Prop :=
  Y = ℝ ∨ ∃ n : ℕ, Y = EuclideanSpace ℝ (Fin (n + 2))

/-- A map is a book-function exactly when its codomain is `ℝ` or `ℝ^k` with `k > 1`. -/
theorem is_book_function_iff (M : Type u) {Y : Type} (f : M → Y) :
    is_book_function M f ↔ Y = ℝ ∨ ∃ n : ℕ, Y = EuclideanSpace ℝ (Fin (n + 2)) := sorry
