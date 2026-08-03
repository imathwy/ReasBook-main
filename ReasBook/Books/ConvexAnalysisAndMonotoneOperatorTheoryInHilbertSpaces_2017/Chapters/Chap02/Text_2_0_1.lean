import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

/- Text 2.0.1: in a real Hilbert space, the norm induced by the inner product is the canonical
norm satisfying `‖x‖ = Real.sqrt ⟪x, x⟫_ℝ`. -/
recall norm_eq_sqrt_real_inner {F : Type u} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : F) : ‖x‖ = Real.sqrt ⟪x, x⟫_ℝ

/- In the induced metric on a real inner product space, the distance between `x` and `y` is the
norm of their difference. -/
recall dist_eq_norm_sub {E : Type u} [SeminormedAddCommGroup E] (x y : E) :
    dist x y = ‖x - y‖
