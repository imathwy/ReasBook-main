import Mathlib
import AchimKlenkeLean.Items.Chap22.Corollary_22_7
import AchimKlenkeLean.Items.Chap22.Theorem_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

section HartmanWintner

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)

local notation "S" => partialSum (fun k ↦ X (k + 1))

/- Theorem 22.11 is `source-facing`: its primitive data are the iid textbook-indexed increments
`X₁, X₂, …`, expressed through the chapter owner `partialSum` for the associated random walk. The
`core/canonical` owner on the comparison side is the Brownian-motion law of the iterated logarithm
`IsBrownianMotion.ae_limsup_div_sqrt_two_mul_t_log_log_eq_one`, while Corollary 22.7 supplies the
`bridge/view` from the iid partial-sum process to a stopped Brownian motion. -/

-- Proof sketch: apply Corollary 22.7 to realize the chapter's canonical textbook-indexed
-- partial-sum process `n ↦ partialSum (fun k ↦ X (k + 1)) n` as a stopped Brownian motion with iid
-- time increments of mean `1`, use the Brownian law of the iterated logarithm from Theorem 22.1,
-- and compare the random times with deterministic time via the strong law of large numbers for the
-- stopping-time increments.
/-- Theorem 22.11: Hartman--Wintner's law of the iterated logarithm. If `X₁, X₂, …` are iid real
random variables with mean `0` and variance `1`, then the normalized textbook partial sums
`Sₙ = partialSum (fun k ↦ X (k + 1)) n` satisfy `limsup Sₙ / sqrt(2 n log log n) = 1` almost
surely. -/
theorem ae_limsup_textbookPartialSum_div_sqrt_two_mul_n_log_log_eq_one
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : Var[X 1; P] = 1) :
    ∀ᵐ ω ∂P,
      limsup
        (fun n ↦
          S (n + 1) ω /
            Real.sqrt (2 * (n + 1 : ℝ) * Real.log (Real.log (n + 1 : ℝ))))
        atTop = 1 := sorry

end HartmanWintner

end ProbabilityTheory
