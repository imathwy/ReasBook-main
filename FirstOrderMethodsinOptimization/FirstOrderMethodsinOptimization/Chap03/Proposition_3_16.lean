import FirstOrderMethodsinOptimization.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Proposition 3.16 is a `bridge/view` item in the chapter real-valued subdifferential API. The
owner abstraction is `subdifferentialAt`, and the source-facing scalar-slope statement is expressed
through its canonical one-dimensional vector-side bridge `euclideanSubdifferentialAt` from Theorem
3.4 rather than through an ad hoc encoding of real slopes as elements of `StrongDual ℝ ℝ`. -/

recall euclideanSubdifferentialAt

-- Proof sketch: split into the cases `x > 0`, `x < 0`, and `x = 0`. For `x ≠ 0`, the function
-- `t ↦ |t|` is differentiable at `x`, so the supporting-line inequality forces the only possible
-- slope to be `Real.sign x`, and that slope indeed works. At `x = 0`, the inequality becomes
-- `|y| ≥ v * y` for all `y`; testing it on `1` and `-1` gives `-1 ≤ v ≤ 1`, and conversely every
-- `v ∈ [-1, 1]` defines a valid supporting line at the origin.
/-- Proposition 3.16: for the one-dimensional function `g(x) = |x|`, the subdifferential is the
singleton with slope `Real.sign x` away from `0`, and at `0` it is the interval `[-1, 1]`. The
left-hand side is the canonical one-dimensional bridge `euclideanSubdifferentialAt`, so the
result is stated directly as a set of real slopes. -/
theorem euclidean_subdifferentialAt_abs_eq_piecewise (x : ℝ) :
    euclideanSubdifferentialAt (fun y : ℝ ↦ |y|) x =
      if x = 0 then Set.Icc (-1 : ℝ) 1 else {Real.sign x} := sorry

end
