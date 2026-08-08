import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

section

-- Proof sketch: write the constraint as `x 0 ≤ -(x 1 ^ 2) / 2`. If `0 < y 0`, then for each fixed
-- `x 1` the pairing is maximized at the boundary value `x 0 = -(x 1 ^ 2) / 2`, reducing the
-- problem to maximizing a concave quadratic in `x 1`, whose maximum is `y 1 ^ 2 / (2 * y 0)`.
-- If `y 0 < 0`, then sending `x 0 → -∞` makes the pairing tend to `⊤`. If `y 0 = 0` and
-- `y 1 ≠ 0`, evaluating on boundary points gives arbitrarily large values. At `y = 0`, every
-- pairing is `0`, so the support function is `0`.
/-- Proposition 2.5: for the set `C = {(x₁, x₂) | x₁ + x₂^2 / 2 ≤ 0}` in `ℝ²`, the support
function, viewed through the Euclidean-dual identification, equals `y₂^2 / (2 y₁)` when
`y₁ > 0`, equals `0` at the origin, and equals `⊤` otherwise. -/
theorem support_function_parabolic_region (y : EuclideanSpace ℝ (Fin 2)) :
    support_function {x : EuclideanSpace ℝ (Fin 2) | x 0 + x 1 ^ 2 / 2 ≤ 0}
        (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ (Fin 2)) y) =
      if 0 < y 0 then ((((y 1 : ℝ) ^ 2) / (2 * y 0) : ℝ) : EReal)
      else if y = 0 then (0 : EReal)
      else ⊤ := sorry

end
