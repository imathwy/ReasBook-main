import FirstOrderMethodsinOptimization.Chap02.Definition_2_1
import FirstOrderMethodsinOptimization.Chap02.Definition_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The Example 2.3 family takes the value `α` at `0`, agrees with the identity on `(0, 1]`, and
is `∞` elsewhere. -/
def truncated_identity_with_origin_value (α : ℝ) : ℝ → EReal :=
  fun x ↦ extendedIndicator (Set.Icc (0 : ℝ) 1) x + if x = 0 then (α : EReal) else x

-- Proof sketch: unfold `truncated_identity_with_origin_value` and `effective_domain`, then split
-- into the cases `x = 0`, `0 < x ∧ x ≤ 1`, and the complement. The value at `0` is finite because
-- `α : ℝ`, so the finite-value locus is exactly the interval `[0, 1]`.
/-- The effective domain of `truncated_identity_with_origin_value α` is exactly the interval
`[0, 1]`. -/
theorem truncated_identity_with_origin_value_effective_domain_eq (α : ℝ) :
    effective_domain (truncated_identity_with_origin_value α) = Set.Icc (0 : ℝ) 1 := sorry

-- Proof sketch: the function is continuous on each branch away from `0`. At the origin, the only
-- possible failure of lower semicontinuity comes from approaching through positive points in the
-- domain, where the values converge to `0`, so the lower-semicontinuity condition is exactly
-- `α ≤ 0`.
/-- Example 2.3: the function `truncated_identity_with_origin_value α` is closed, equivalently
lower semicontinuous, if and only if `α ≤ 0`. -/
theorem truncated_identity_with_origin_value_lowerSemicontinuous_iff (α : ℝ) :
    LowerSemicontinuous (truncated_identity_with_origin_value α) ↔ α ≤ 0 := sorry

-- Proof sketch: use `truncated_identity_with_origin_value_effective_domain_eq` to identify the
-- effective domain with `[0, 1]`. Relative continuity is automatic away from `0`, and at `0` the
-- right-hand limit along the domain is `0`, so continuity on the effective domain holds exactly
-- when the value assigned at `0` is also `0`.
/-- The Example 2.3 family is continuous on its effective domain exactly when the origin value is
`0`. -/
theorem truncated_identity_with_origin_value_continuousOn_effective_domain_iff (α : ℝ) :
    ContinuousOn (truncated_identity_with_origin_value α)
      (effective_domain (truncated_identity_with_origin_value α)) ↔ α = 0 := sorry

-- Proof sketch: combine
-- `truncated_identity_with_origin_value_lowerSemicontinuous_iff` and
-- `truncated_identity_with_origin_value_continuousOn_effective_domain_iff` at `α = -1 / 10`.
/-- The parameter choice `α = -1 / 10` gives a closed function that is not continuous on its
effective domain. -/
theorem truncated_identity_with_origin_value_neg_tenth_closed_not_continuousOn_effective_domain :
    LowerSemicontinuous (truncated_identity_with_origin_value (-(1 : ℝ) / 10)) ∧
      ¬ ContinuousOn (truncated_identity_with_origin_value (-(1 : ℝ) / 10))
        (effective_domain (truncated_identity_with_origin_value (-(1 : ℝ) / 10))) := sorry

end
