import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- A real-valued discrete process is locally bounded if, at each fixed time, it is bounded
uniformly in the sample point. This is the boundedness hypothesis used for the discrete
stochastic integral in Chapter 9. -/
def IsLocallyBoundedProcess (H : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ, ∃ R : ℝ, 0 ≤ R ∧ ∀ ω, |H n ω| ≤ R

/-- Definition 9.37: the discrete stochastic integral of a real process `H` with respect to a
real process `X` is the process whose value at time `n` is the finite sum
`∑_{m=1}^n H_m (X_m - X_{m-1})`. In the `0`-based Lean indexing used here, this is written as a
sum over `k ∈ Finset.range n` with the increment from time `k` to time `k + 1`. When `X` is a
martingale, the same process is also called the martingale transform of `X`. -/
def stochasticIntegral (H X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦ ∑ k ∈ Finset.range n, H (k + 1) ω * (X (k + 1) ω - X k ω)

-- Proof sketch: unfold `stochasticIntegral`; this is exactly its defining finite
-- sum over the increments from times `0, ..., n - 1` to `1, ..., n`.
/-- The discrete stochastic integral evaluates pointwise as the finite sum of the stakes against
the successive increments of the integrator. -/
theorem stochasticIntegral_apply (H X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    stochasticIntegral H X n ω =
      ∑ k ∈ Finset.range n, H (k + 1) ω * (X (k + 1) ω - X k ω) := sorry

end ProbabilityTheory
