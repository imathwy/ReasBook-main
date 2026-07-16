import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 4.8 is `source-facing` in the Chapter 4 conjugacy API. The chapter owner
abstraction for Fenchel conjugates is already `conjugate_function` from Definition 4.1, so this
file keeps only the negative-log barrier and its conjugacy formulas rather than a parallel local
copy of the owner definition. -/

/-- The negative-log barrier, equal to `-log x` on the positive ray and `∞` on the nonpositive
half-line. -/
def negative_log_barrier : ℝ → EReal :=
  fun x ↦ if 0 < x then ((-Real.log x : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `negative_log_barrier` inside the canonical Fenchel-conjugate definition
-- `conjugate_function`. On the positive ray the barrier contributes `-(-log x) = log x`, while on
-- the nonpositive half-line the term `(x * y : EReal) - ⊤` is `⊥`, so those points do not affect
-- the supremum. Re-express the remaining supremum as the image of `Set.Ioi 0`.
/-- The conjugate of the negative-log barrier is the supremum of `x * y + log x` over the positive
ray. -/
theorem negative_log_barrier_conjugate_eq_sSup_Ioi (y : ℝ) :
    conjugate_function negative_log_barrier (InnerProductSpace.toDualMap ℝ ℝ y) =
      sSup ((fun x : ℝ ↦ ((x * y + Real.log x : ℝ) : EReal)) '' Set.Ioi (0 : ℝ)) := sorry

-- Proof sketch: use `negative_log_barrier_conjugate_eq_sSup_Ioi`. If `y < 0`, differentiate the
-- smooth objective `x ↦ x * y + log x` on `(0, ∞)` to find the unique maximizer `x = -1 / y`, and
-- evaluate the objective there to obtain `-1 - log (-y)`. If `y ≥ 0`, the objective tends to `∞`
-- along `x → ∞`, so the conjugate value is `⊤`.
/-- Proposition 4.8: the conjugate of the negative-log barrier equals `-1 - log (-y)` for `y < 0`
and equals `∞` for `y ≥ 0`. -/
theorem negative_log_barrier_conjugate_eq (y : ℝ) :
    conjugate_function negative_log_barrier (InnerProductSpace.toDualMap ℝ ℝ y) =
      if y < 0 then ((-1 - Real.log (-y) : ℝ) : EReal) else ⊤ := sorry

end
