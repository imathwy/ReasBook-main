import Mathlib
import SmoothManifoldsLee.Chap01.Sec01.Example_1_5

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: identify `ℝPⁿ` with a quotient of the unit sphere by the antipodal action, then
-- use that the sphere is Hausdorff and the antipodal action is proper/discontinuous so the
-- quotient is Hausdorff.
/-- Exercise 1.6 (1): real projective space `ℝPⁿ` is Hausdorff. -/
theorem realProjectiveSpace_t2Space (n : ℕ) : T2Space (RealProjectiveSpace n) := sorry

-- Proof sketch: realize `ℝPⁿ` as an open quotient of a second-countable space, for instance the
-- sphere or the nonzero vectors in `ℝ^(n+1)`, and apply the standard quotient theorem for
-- second-countability.
/-- Exercise 1.6 (2): real projective space `ℝPⁿ` is second-countable. -/
theorem realProjectiveSpace_secondCountableTopology (n : ℕ) :
    SecondCountableTopology (RealProjectiveSpace n) := sorry

-- Proof sketch: apply the standard affine chart existence theorem from Example 1.5.
/-- Exercise 1.6 (3): every point of `ℝPⁿ` lies in the source of a standard affine chart,
equivalently in a chart whose coordinate map is a homeomorphism with `ℝⁿ`. -/
theorem realProjectiveSpace_has_euclidean_chart (n : ℕ) (x : RealProjectiveSpace n) :
    ∃ i : Fin (n + 1), x ∈ realProjectiveChartDomain n i := sorry

-- Proof sketch: this is exactly the openness statement for the standard affine chart domains from
-- Example 1.5.
/-- Exercise 1.6 (4): each standard affine chart domain in `ℝPⁿ` is open. Together with
Exercise 1.6 (1), Exercise 1.6 (2), and Exercise 1.6 (3), this yields that `ℝPⁿ` is a
topological `n`-manifold. -/
theorem realProjectiveSpace_chartDomain_isOpen (n : ℕ) (i : Fin (n + 1)) :
    IsOpen (realProjectiveChartDomain n i) := sorry
