import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open Polynomial

section

variable (p d : ℕ)

local notation "K" => Localization.Away (p : ℤ)
local notation "P" => cyclotomic p K
local notation "A" => AdjoinRoot P
local notation "ζ" => (AdjoinRoot.root P : A)

/-- Example 10.147.3: for `d < p`, the first `d` powers of the distinguished root in
`ℤ[1/p][X] / (1 + X + ··· + X^(p - 1))` have unit pairwise-difference product. -/
-- Proof sketch: `Polynomial.cyclotomic_prime` identifies the defining polynomial with
-- `1 + X + ··· + X^(p - 1)`, so the example ring is the canonical adjoin-root quotient
-- `AdjoinRoot (cyclotomic p (Localization.Away (p : ℤ)))`. Take `α_i = ζ^i`, where `ζ` is the
-- distinguished root of this owner polynomial. In the fraction field these are distinct
-- `p`-th roots of unity, so `T^p - 1` factors as `∏ (T - α_i)`. Differentiating and evaluating at
-- each `α_i` identifies the omitted-difference product with `p * α_i^(p - 1)`, which is a unit
-- because `p` is inverted in the base ring and each `α_i` is itself a unit.
theorem cyclotomic_prime_example_unit_pairwise_difference_product
    [Fact p.Prime] (hd : d < p) :
    IsUnit
      (∏ ij ∈ (Finset.univ : Finset (Fin d)).offDiag with ij.1 < ij.2,
        (ζ ^ (ij.1 : ℕ) - ζ ^ (ij.2 : ℕ))) := sorry

end
