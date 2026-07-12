import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Interval

section

/- Lemma 5.22 is `source-facing`: it asks for a scalar-valued selection of one-dimensional
subgradients along an interval. The owner abstractions already exist upstream as Chapter 2's
`is_convex_function` and Chapter 3's `subdifferential`; the scalar slope view is only a
`bridge/view`, obtained by identifying `g : ℝ` with the continuous linear functional `g • 1`. -/

/-- A real slope `g` belongs to the one-dimensional subdifferential of `f` at `t` exactly when the
supporting-line inequality with slope `g` holds at every point. This is the scalar bridge to the
chapter owner `strongDualSubdifferential`. -/
theorem real_slope_mem_strongDualSubdifferential_iff
    {f : ℝ → EReal} {t g : ℝ} :
    g • (1 : StrongDual ℝ ℝ) ∈ strongDualSubdifferential f t ↔
      t ∈ effective_domain f ∧ ∀ y : ℝ, f y ≥ f t + ((g * (y - t) : ℝ) : EReal) := sorry

-- Proof sketch: the interval hypothesis places every interior point `t ∈ (a, b)` in the relative
-- interior of `dom(f)`, so the Chapter 3 existence theorem gives a nonempty one-dimensional
-- subdifferential there. Choosing the monotone left-derivative selection `h(t) ∈ ∂ f(t)` and
-- applying the fundamental theorem for monotone functions on `[a, b]` yields the integral formula.
/-- Lemma 5.22: if a closed convex function `f : ℝ → (-∞, ∞]` never takes the value `-∞` and is
finite on `[a, b]` with `a ≤ b`, then there exists a real-valued selection of the one-dimensional
subdifferential on `(a, b)` whose interval integral equals the endpoint difference
`(f b).toReal - (f a).toReal`. -/
theorem exists_subgradient_selection_eq_intervalIntegral
    (f : ℝ → EReal) (hne_bot : ∀ x, f x ≠ ⊥) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) {a b : ℝ} (hab : a ≤ b)
    (hdom : Set.Icc a b ⊆ effective_domain f) :
    ∃ h : ℝ → ℝ,
      IntervalIntegrable h MeasureTheory.volume a b ∧
      (∀ t ∈ Set.Ioo a b,
        h t • (1 : StrongDual ℝ ℝ) ∈ strongDualSubdifferential f t) ∧
      (f b).toReal - (f a).toReal = ∫ t in a..b, h t := sorry

end
