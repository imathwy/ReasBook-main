import Mathlib
import Nesterov.Chap05.Definition_5_0_10
import Nesterov.Chap05.Definition_5_4_7_17
import Nesterov.Chap05.Definition_5_4_7_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators RelativeDirection MonomialXi StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Theorem 5.4.7.11 lies in the Chapter 5 simplex-monomial / directional-second-derivative
domain.

Sampled owner declarations:
* `secondDirectionalDerivative` in `Definition_5_0_10`, the chapter owner for `D²f(x)[h,h]`;
* `ambientMonomialXi` and `ξ_[a]` in `Definition_5_4_7_17`, the simplex monomial owner and its
  ambient/source-facing bridge;
* `quantityS2` in `Definition_5_4_7_18`, the source-facing weighted centered second moment of the
  relative direction.

Source/core/bridge triage:
* source-facing: Theorem 5.4.7.11's identity `D² ξ_a(x)[h,h] = -ξ_a(x) S₂`;
* core/canonical: `secondDirectionalDerivative (ambientMonomialXi a) x h`;
* bridge/view: the expanded quadratic polynomial in the weighted mean
  `Finset.univ.centerMass a (δ[x](h))` and weighted square sum
  `a ⬝ᵥ fun i ↦ (δ[x](h) i) ^ (2 : ℕ)`.

The file is therefore downstream from the existing owners `secondDirectionalDerivative`,
`ambientMonomialXi`, `ξ_[a]`, and `quantityS2`. It keeps only the derivative theorem and its
explicit bridge formula, rather than restating any local wrapper for the monomial, the relative
direction, or the centered second moment. -/

-- Proof sketch: differentiate the directional slice of the ambient monomial once more along the
-- repeated direction `h`, rewrite the derivative of each relative coordinate `h i / x i` as
-- `-(h i / x i)^2`, and factor the result into `ξ_a(x)` times the weighted mean square minus the
-- weighted square sum.
/-- The second directional derivative of the simplex monomial `ξ_a` admits the expanded formula
`ξ_a(x) (m^2 - ⟪a, [δ]^2⟫)`, where `δ = δ_x(h)` and
`m = Finset.univ.centerMass a (δ[x](h)) = ⟪a, δ⟫`. -/
theorem monomialXi_secondDirectionalDerivative_eq_mul_quadratic_relativeDirection_polynomial
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    secondDirectionalDerivative (ambientMonomialXi a) x h =
        ξ_[a] x *
          (Finset.univ.centerMass a (δ[x](h)) ^ (2 : ℕ) -
            a ⬝ᵥ fun i : Fin n ↦ (δ[x](h) i) ^ (2 : ℕ)) := sorry

-- Proof sketch: combine the expanded second-derivative formula with the identity
-- `quantityS2 a x h = ⟪a, [δ_x(h)]^2⟫ - ⟪a, δ_x(h)⟫^2`, so the bracket equals `-S₂`.
/-- Theorem 5.4.7.11: the second directional derivative of `ξ_a` on the positive orthant equals
`-ξ_a(x) S₂`, where `S₂ = quantityS2 a x h` is the weighted second centered moment of the
relative direction `δ_x(h)`. -/
theorem monomialXi_secondDirectionalDerivative_eq_neg_mul_quantityS2
    (a : Δ[n]) (x : Xₙ) (h : Eₙ) :
    secondDirectionalDerivative (ambientMonomialXi a) x h =
        -(ξ_[a] x * quantityS2 a x h) := sorry

end
