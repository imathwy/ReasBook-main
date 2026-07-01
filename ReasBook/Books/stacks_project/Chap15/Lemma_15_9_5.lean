import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

-- Proof sketch: use the universal coprime factorization algebra for the monic polynomial `f`. The
-- given factorization over `A ⧸ I` yields an `A`-algebra map from this universal algebra to
-- `A ⧸ I`. By Example `10.143.12` the universal algebra is étale at every point over the kernel of
-- that map; Lemma `15.9.4` gives a localization `B_g` that is étale over `A` and still maps onto
-- `A ⧸ I`. Applying Lemmas `10.143.8` and `10.143.9` to the induced quotient map produces an
-- idempotent localization whose reduction modulo `I` is isomorphic to `A ⧸ I`, and the universal
-- factorization descends to the required lifted monic factorization.
/-- Lemma 15.9.5: if a monic polynomial `f ∈ A[X]` has a factorization modulo `I` as a product of
monic coprime factors `ḡ * h̄`, then after an étale base change `A → A'` inducing an isomorphism
`A ⧸ I ≃ A' ⧸ IA'`, the polynomial `f` factors as a product of monic lifts `g' * h'` whose
reductions modulo `IA'` recover the given factorization. -/
theorem exists_etale_lift_factorization_of_monic_mod_ideal
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic) (hgbar : gbar.Monic)
    (hhbar : hbar.Monic) (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
        g'.Monic ∧
          h'.Monic ∧
          f.map (algebraMap A A') = g' * h' ∧
          gbar.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
          hbar.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) :=
  sorry

end

end Algebra
