import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω}

-- Proof sketch: use `ProbabilityTheory.condExpKernel` to rewrite conditional expectations as
-- fiberwise integrals, apply `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` on each fiber with
-- the canonical exponent relation `hpq`, and discharge the moment side conditions from `hX` and
-- `hY`. The side case `¬ ℱ ≤ mΩ` is automatic from `condExp_of_not_le`.
/-- Exercise 8.3.2: conditional Hölder's inequality. If `p` and `q` are Hölder-conjugate and
`X ∈ ℒ^p(P)`, `Y ∈ ℒ^q(P)`, then the conditional expectation of `|XY|` is bounded almost surely
by the product of the conditional `L^p` and `L^q` moments. This is the canonical
`Real.HolderConjugate` formulation of the textbook assumptions `p, q ∈ (1, ∞)` and
`1 / p + 1 / q = 1`. -/
theorem condExp_abs_mul_ae_le_of_holderConjugate {ℱ : MeasurableSpace Ω} {p q : ℝ}
    (hpq : p.HolderConjugate q) {X Y : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal p) P) (hY : MemLp Y (ENNReal.ofReal q) P) :
    P[fun ω ↦ |X ω * Y ω| | ℱ] ≤ᵐ[P]
      P[fun ω ↦ |X ω| ^ p | ℱ] ^ (1 / p) * P[fun ω ↦ |Y ω| ^ q | ℱ] ^ (1 / q) := sorry
