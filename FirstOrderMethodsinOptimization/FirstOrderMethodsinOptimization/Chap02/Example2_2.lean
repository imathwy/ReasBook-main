import FirstOrderMethodsinOptimization.Chap02.Definition_2_1
import FirstOrderMethodsinOptimization.Chap02.Theorem_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The extended-real-valued example that equals `1 / x` on the positive ray and `∞` elsewhere. -/
def positive_reciprocal_barrier : ℝ → EReal :=
  fun x ↦ if 0 < x then ((1 / x : ℝ) : EReal) else ⊤

-- Proof sketch: unfold `positive_reciprocal_barrier`; for `x > 0` the value is the finite real
-- `1 / x`, while for `x ≤ 0` the value is `⊤`, so the finite-value locus is exactly `Set.Ioi 0`.
/-- The finite-value domain of `positive_reciprocal_barrier` is exactly the open ray `(0, ∞)`. -/
theorem positive_reciprocal_barrier_effective_domain_eq :
    effective_domain positive_reciprocal_barrier = Set.Ioi (0 : ℝ) := sorry

-- Proof sketch: rewrite the effective domain using
-- `positive_reciprocal_barrier_effective_domain_eq`, then use that `Set.Ioi (0 : ℝ)` is open and
-- not closed in `ℝ`.
/-- The effective domain of `positive_reciprocal_barrier` is not closed. -/
theorem positive_reciprocal_barrier_effective_domain_not_closed :
    ¬ IsClosed (effective_domain positive_reciprocal_barrier) := sorry

-- Proof sketch: split on the sign of `p.1`. For `p.1 ≤ 0`, the left side is impossible because
-- `positive_reciprocal_barrier p.1 = ⊤` cannot be bounded above by a real number. For `p.1 > 0`,
-- simplify the inequality `1 / p.1 ≤ p.2` by multiplying through by the positive factor `p.1`.
/-- The source-facing real epigraph of `positive_reciprocal_barrier` is the set
`{(x, y) | 0 < x ∧ 1 ≤ x * y}`. -/
theorem positive_reciprocal_barrier_real_epigraph_eq :
    realEpigraph positive_reciprocal_barrier =
      {p : ℝ × ℝ | 0 < p.1 ∧ (1 : ℝ) ≤ p.1 * p.2} := sorry

-- Proof sketch: prove closedness for the canonical owner `realEpigraph positive_reciprocal_barrier`
-- either directly from `positive_reciprocal_barrier_real_epigraph_eq` and continuity of
-- multiplication, or via `lowerSemicontinuous_iff_isClosed_real_epigraph`.
/-- Example2.2: the real epigraph of the positive reciprocal barrier is closed, even though its
effective domain is the open ray `(0, ∞)`. -/
theorem positive_reciprocal_barrier_real_epigraph_is_closed :
    IsClosed (realEpigraph positive_reciprocal_barrier) := sorry

-- Proof sketch: use the canonical equivalence between lower semicontinuity and closedness of the
-- epigraph in `ℝ × EReal`, or add the `⊤`-slice to the real epigraph and check that this enlarged
-- set is closed.
/-- The extended-real epigraph of `positive_reciprocal_barrier` is closed. -/
theorem positive_reciprocal_barrier_epigraph_is_closed :
    IsClosed {p : ℝ × EReal | positive_reciprocal_barrier p.1 ≤ p.2} := sorry

-- Proof sketch: apply `lowerSemicontinuous_iff_isClosed_epigraph` to
-- `positive_reciprocal_barrier_epigraph_is_closed`.
/-- The positive reciprocal barrier is lower semicontinuous, anticipating the later equivalence
between lower semicontinuity and closedness. -/
theorem positive_reciprocal_barrier_lowerSemicontinuous :
    LowerSemicontinuous positive_reciprocal_barrier := sorry

end
