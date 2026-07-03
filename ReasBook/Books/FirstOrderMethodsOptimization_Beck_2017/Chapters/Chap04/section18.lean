

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_18 (from Chap04) -/
universe u

noncomputable section

open Metric

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 4.18 is `source-facing` in the chapter norm-conjugacy API. The owner abstractions
already live upstream: Chapter 2 owns the indicator function `extendedIndicator`, and the
continuous-dual Fenchel conjugate on normed spaces is already present upstream in Chapter 4 as
`conjugate_function`. The primitive data here are therefore only the norm objective and the dual
closed unit ball; the proposition itself is the source-facing identification between those owner
objects. -/
recall extendedIndicator
recall conjugate_function
recall conjugate_function_apply

-- Proof sketch: if `‖y‖ ≤ 1`, the dual norm inequality gives `y x ≤ ‖y‖ * ‖x‖ ≤ ‖x‖`, so every
-- term `y x - ‖x‖` is at most `0`, and equality is attained at `x = 0`. If `‖y‖ > 1`, apply
-- Hahn-Banach to choose a unit vector on which `y` is arbitrarily close to its norm, then scale
-- along that direction to make `y x - ‖x‖` diverge to `∞`.
/-- Proposition 4.18: the Fenchel conjugate of the norm `x ↦ ‖x‖` is the extended-real-valued
indicator of the closed unit ball in the dual space. -/
theorem norm_conjugate_eq_extendedIndicator_closedBall
    (y : StrongDual ℝ E) :
    conjugate_function (fun x : E ↦ (‖x‖ : EReal)) y =
      extendedIndicator (closedBall (0 : StrongDual ℝ E) 1) y := sorry

-- Proof sketch: combine `norm_conjugate_eq_extendedIndicator_closedBall` with the defining
-- behavior of `extendedIndicator`, then rewrite membership in the closed ball centered at `0` as
-- the norm inequality `‖y‖ ≤ 1`.
/-- The conjugate of the norm is `0` on the dual closed unit ball and `∞` outside it. -/
theorem norm_conjugate_eq_if_norm_le_one
    (y : StrongDual ℝ E) :
    conjugate_function (fun x : E ↦ (‖x‖ : EReal)) y =
      if ‖y‖ ≤ 1 then (0 : EReal) else ⊤ := sorry

end
