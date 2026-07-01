import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Example 15.9.7:
* primary domain: polynomial factorizations over quotient rings and their étale lifting in Chapter
  15;
* sampled owner declarations:
  `Algebra.exists_etale_factorization_lift_of_isUnit_leadingCoeff`,
  `Algebra.exists_etale_lift_factorization_of_monic_mod_ideal`,
  `Algebra.exists_quotientAlgEquiv_localizationAway_of_isUnit_quotient`;
* best owner abstraction: the chapter owner for the lifting problem is
  `Algebra.exists_etale_factorization_lift_of_isUnit_leadingCoeff`; this example should negate that
  specialized conclusion directly, rather than introduce a parallel local witness package;
* primitive data: the ideal `4ℤ` and the reduced polynomial `2X^2 + 2X + 1`;
* derived API: its square-equals-one relation, the resulting self-coprimeness, the failure of
  unit-leading-coefficient, and the failure of the specialized étale lifting conclusion;
* layer: the explicit ideal, polynomial, and counterexample are `source-facing`, while the Chapter
  15 lifting theorem is the relevant `core/canonical` owner.
-/

open Polynomial

universe u

/-- The ideal `4ℤ` used in the counterexample of Example 15.9.7. -/
def example1597Ideal : Ideal ℤ :=
  Ideal.span ({(4 : ℤ)} : Set ℤ)

/-- The polynomial `2X^2 + 2X + 1` over `ℤ / 4ℤ` used in Example 15.9.7. -/
noncomputable def example1597ReducedFactor : (ℤ ⧸ example1597Ideal)[X] :=
  2 * X ^ 2 + 2 * X + 1

-- Proof sketch: expand the square of `2X^2 + 2X + 1` in `(ℤ / 4ℤ)[X]`. Every cross term carries a
-- factor `4`, so it vanishes in the quotient, and the remaining constant term is `1`.
/-- The polynomial of Example 15.9.7 squares to `1` modulo `4`. -/
theorem example1597_reduction_factorization :
    example1597ReducedFactor ^ 2 = 1 := sorry

-- Proof sketch: since `example1597ReducedFactor ^ 2 = 1`, the polynomial is a unit in
-- `(ℤ / 4ℤ)[X]`; any unit is coprime to itself.
/-- The reduced factor in Example 15.9.7 is coprime to itself. -/
theorem example1597_reducedFactor_isCoprime :
    IsCoprime example1597ReducedFactor example1597ReducedFactor := sorry

-- Proof sketch: the leading coefficient is the image of `2` in `ℤ / 4ℤ`. If it were a unit, then
-- `2` would be invertible modulo `4`, which is impossible because `2` is a zerodivisor in `ℤ / 4ℤ`.
/-- The leading coefficient in Example 15.9.7 is not a unit. -/
theorem example1597_reducedFactor_leadingCoeff_not_isUnit :
    ¬ IsUnit example1597ReducedFactor.leadingCoeff := sorry

-- Proof sketch: argue by contradiction. Such lift data would produce an étale `ℤ`-algebra `A'`
-- with `A' / 4A' ≃ ℤ / 4ℤ` and polynomials `g'`, `h'` lifting `2X^2 + 2X + 1` whose product is
-- `1`. The source example identifies the `2`-adic completion of any such `A'` with `ℤ₂`, where no
-- polynomial congruent to `2X^2 + 2X + 1` modulo `4` is invertible in `ℤ₂[X]`, contradiction.
/-- Example 15.9.7: for `A = ℤ`, `I = 4ℤ`, `f = 1`, and
`ḡ = h̄ = 2X^2 + 2X + 1 ∈ (ℤ / 4ℤ)[X]`, the conclusion of Lemma `15.9.6` fails: there is no
étale lift of this factorization with quotient unchanged modulo `4`. This shows the hypothesis
that the leading coefficient of `ḡ` is a unit cannot be dropped. -/
theorem example1597_no_etale_factorization_lift :
    ¬ ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra ℤ A') (_ : Algebra.Etale ℤ A')
        (quotientAlgEquiv :
          (ℤ ⧸ example1597Ideal) ≃ₐ[ℤ ⧸ example1597Ideal]
            (A' ⧸ Ideal.map (algebraMap ℤ A') example1597Ideal))
        (g' h' : A'[X]),
        (1 : ℤ[X]).map (algebraMap ℤ A') = g' * h' ∧
          example1597ReducedFactor.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap ℤ A') example1597Ideal)) ∧
          example1597ReducedFactor.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap ℤ A') example1597Ideal)) := sorry
