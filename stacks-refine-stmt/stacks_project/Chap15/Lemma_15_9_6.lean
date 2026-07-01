import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

-- Proof sketch: lift the unit leading coefficient of `gbar` to a unit after an étale localization
-- using Lemma `15.9.1`, rescale `gbar` and `hbar` so that both become monic modulo `I`, and then
-- apply the monic lifting statement of Lemma `15.9.5`. Finally rescale the lifted factors back by
-- the lifted unit to recover a lift of the original factorization.
/-- Lemma 15.9.6: if a monic polynomial `f` factors modulo `I` as `gbar * hbar`, with invertible
leading coefficient for `gbar` and with `gbar`, `hbar` generating the unit ideal in
`(A ⧸ I)[X]`, then after an étale base change `A → A'` inducing an isomorphism
`A ⧸ I ≃ A' ⧸ IA'`, the polynomial `f` admits a factorization `g' * h'` lifting the given
factorization over `A ⧸ I`. -/
theorem exists_etale_factorization_lift_of_isUnit_leadingCoeff
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hunit : IsUnit gbar.leadingCoeff) (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
        f.map (algebraMap A A') = g' * h' ∧
          gbar.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
          hbar.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) :=
  sorry

end

end Algebra
