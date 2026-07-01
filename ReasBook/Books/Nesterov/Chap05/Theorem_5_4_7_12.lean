import Mathlib
import Nesterov.Chap05.Definition_5_0_10
import Nesterov.Chap05.Definition_5_4_7_16
import Nesterov.Chap05.Definition_5_4_7_17
import Nesterov.Chap05.Definition_5_4_7_18
import Nesterov.Chap05.Definition_5_4_7_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.12 lies in the chapter's simplex-monomial / directional-derivative domain.

Sampled owner declarations:
* `thirdDirectionalDerivative` in `Definition_5_0_10`, the chapter owner for
  `D³f(x)[h,h,h]`;
* `ambientMonomialXi` and `ξ_[a]` in `Definition_5_4_7_17`, the simplex monomial owner and its
  ambient bridge;
* `quantityS2` in `Definition_5_4_7_18`, the weighted centered second moment;
* `quantityS3` in `Definition_5_4_7_19`, the weighted centered third moment.

Source/core/bridge triage:
* source-facing: the explicit formulas for the third directional derivative of `ξ_a`;
* core/canonical: `thirdDirectionalDerivative (ambientMonomialXi a) x h`;
* bridge/view: the expanded cubic polynomial in the weighted mean and its reformulation in terms
  of `S₂` and `S₃`.

This file therefore keeps the theorem content but uses the chapter owner
`thirdDirectionalDerivative` as the public derivative surface, rather than restating the raw
`iteratedFDerivWithin` expression.
-/

section

variable (a : Δ[n]) (x : Xₙ) (h : Eₙ)

local notation "m" => Finset.univ.centerMass a (δ[x](h))

-- Proof sketch: differentiate the second-derivative identity for `ξ_a` along the repeated
-- direction `h`, use `D ξ_a(x)[h] = ξ_a(x) m`, `D m[h] = -⟪a, [δ]^2⟫`, and
-- `D ⟪a, [δ]^2⟫[h] = -2 ⟪a, [δ]^3⟫`, then factor out the common multiplicative term `ξ_a(x)`.
/-- The third directional derivative of the simplex monomial `ξ_a` equals `ξ_a(x)` times the
cubic polynomial in the weighted mean
`m = Finset.univ.centerMass a (δ[x](h)) = ⟪a, δ_x(h)⟫`, the weighted square sum
`⟪a, [δ_x(h)]^2⟫`, and the weighted cube sum `⟪a, [δ_x(h)]^3⟫`. -/
theorem monomialXi_thirdDirectionalDerivative_eq_mul_cubic_relativeDirection_polynomial :
    thirdDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x *
          (m ^ (3 : ℕ) -
            3 * m * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) +
            2 * (a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (3 : ℕ))) := sorry

-- Proof sketch: start from the expanded cubic formula for the third derivative, expand the
-- centered-cube quantity `S₃`, use the definition of `S₂` as the weighted centered square sum,
-- and collect like terms in `m`.
/-- Theorem 5.4.7.12: the third directional derivative of `ξ_a` on the positive orthant equals
`ξ_a(x) (2 S₃ + 3 m S₂)`, where `m = ⟪a, δ_x(h)⟫`,
`S₂ = quantityS2 a x h`, and
`S₃ = quantityS3 a x h`. -/
theorem monomialXi_thirdDirectionalDerivative_eq_mul_two_S3_add_three_mean_S2 :
    thirdDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x * (2 * quantityS3 a x h + 3 * m * quantityS2 a x h) := sorry

end

end
