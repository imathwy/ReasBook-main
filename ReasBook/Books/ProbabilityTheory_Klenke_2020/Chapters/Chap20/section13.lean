import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_13 (from Items/Chap20) -/
open scoped MeasureTheory
open MeasureTheory

universe u

variable {Ω : Type u}

/-- The maximal orbit partial sum `M_n = max {0, S₁, ..., Sₙ}`, where
`S_k(ω) = birkhoffSum τ X0 k ω`. -/
def max_orbit_partial_sum (τ : Ω → Ω) (X0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | n + 1 => fun ω ↦ max (max_orbit_partial_sum τ X0 n ω) (birkhoffSum τ X0 (n + 1) ω)

/-- The maximal orbit partial sum vanishes at time `0`. -/
theorem max_orbit_partial_sum_zero (τ : Ω → Ω) (X0 : Ω → ℝ) :
    max_orbit_partial_sum τ X0 0 = 0 := rfl

/-- The maximal orbit partial sums satisfy the expected recursion by adjoining the next partial
sum to the running maximum. -/
theorem max_orbit_partial_sum_succ (τ : Ω → Ω) (X0 : Ω → ℝ) (n : ℕ) :
    max_orbit_partial_sum τ X0 (n + 1) =
      fun ω ↦ max (max_orbit_partial_sum τ X0 n ω) (birkhoffSum τ X0 (n + 1) ω) := rfl

variable [MeasurableSpace Ω]

/-- Lemma 20.13: in a measure-preserving dynamical system, if `X0` is integrable and
`M_n = max {0, S₁, ..., Sₙ}` with `S_k = birkhoffSum τ X0 k` is the maximal orbit partial sum of
`X0`, then the integral of
`X0` over the event `{M_n > 0}` is nonnegative. -/
-- Proof sketch: compare `X0` with `max {S_1, ..., S_n} - M_n ∘ τ` using the recursion
-- `S_{k+1} = X0 + S_k ∘ τ`; on `{M_n ≤ 0}` one has `M_n - M_n ∘ τ ≤ 0`, so restricting to
-- `{M_n > 0}` yields a lower bound by `M_n - M_n ∘ τ`, and measure preservation cancels the two
-- integrals of `M_n`.
theorem integral_nonneg_on_max_orbit_partial_sum_pos
    (P : Measure Ω) {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) {X0 : Ω → ℝ} (hX0 : Integrable X0 P)
    (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 < max_orbit_partial_sum τ X0 n ω}, X0 ω ∂P := sorry
