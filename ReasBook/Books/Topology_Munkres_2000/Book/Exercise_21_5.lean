module

public import Mathlib.Topology.Algebra.Ring.Real

public section

/- Exercise 21.5 (1): If real sequences converge to `a` and `b`, then their
pointwise sum converges to `a + b`. -/
#check (Filter.Tendsto.add :
  ∀ {x y : ℕ → ℝ} {a b : ℝ} (_ : Filter.Tendsto x Filter.atTop (nhds a))
    (_ : Filter.Tendsto y Filter.atTop (nhds b)),
    Filter.Tendsto (fun n ↦ x n + y n) Filter.atTop (nhds (a + b)))

/- Exercise 21.5 (2): If real sequences converge to `a` and `b`, then their
pointwise difference converges to `a - b`. -/
#check (Filter.Tendsto.sub :
  ∀ {x y : ℕ → ℝ} {a b : ℝ} (_ : Filter.Tendsto x Filter.atTop (nhds a))
    (_ : Filter.Tendsto y Filter.atTop (nhds b)),
    Filter.Tendsto (fun n ↦ x n - y n) Filter.atTop (nhds (a - b)))

/- Exercise 21.5 (3): If real sequences converge to `a` and `b`, then their
pointwise product converges to `a * b`. -/
#check (Filter.Tendsto.mul :
  ∀ {x y : ℕ → ℝ} {a b : ℝ} (_ : Filter.Tendsto x Filter.atTop (nhds a))
    (_ : Filter.Tendsto y Filter.atTop (nhds b)),
    Filter.Tendsto (fun n ↦ x n * y n) Filter.atTop (nhds (a * b)))

/- Exercise 21.5 (4): If real sequences converge to `a` and `b`, every
denominator term is nonzero, and `b ≠ 0`, then their pointwise quotient
converges to `a / b`. The canonical theorem only needs `b ≠ 0`; the stronger
termwise assumption from the exercise is unnecessary for this conclusion. -/
#check (Filter.Tendsto.div :
  ∀ {x y : ℕ → ℝ} {a b : ℝ} (_ : Filter.Tendsto x Filter.atTop (nhds a))
    (_ : Filter.Tendsto y Filter.atTop (nhds b)) (_ : b ≠ 0),
    Filter.Tendsto (x / y) Filter.atTop (nhds (a / b)))
