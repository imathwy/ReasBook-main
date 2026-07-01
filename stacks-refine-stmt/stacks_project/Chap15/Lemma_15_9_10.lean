import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B]

/- Domain-style sampling:
- primary domain: quotient comparison maps for extended ideals under tensor base change;
- sampled owner declarations: `Ideal.le_comap_map`, `Ideal.map_map`, `Ideal.quotientMapₐ`,
  `Algebra.TensorProduct.includeLeft`;
- best owner abstraction: the quotient algebra map induced by tensor base change is the canonical
  owner `Ideal.quotientMapₐ`; the extended-ideal containment is only proof data for that owner;
- primitive data: the ideal `I` and the algebra map `includeLeft : B →ₐ[A] B ⊗[A] A'`;
- derived API: the induced quotient map on `B / I B`.

Layer triage:
- `source-facing`: the idempotent-lifting existence theorem below;
- `core/canonical`: `Ideal.quotientMapₐ`;
- `bridge/view`: the extended-ideal containment used to instantiate that quotient map. -/

omit [Algebra.IsIntegral A B] in
private theorem extendedIdeal_le_comap_extendedIdeal
    (I : Ideal A) {C : Type*} [CommRing C] [Algebra A C] (f : B →ₐ[A] C) :
    I.map (algebraMap A B) ≤
      (Ideal.map (algebraMap A C) I).comap f := by
  simpa [Ideal.map_map] using
    (show Ideal.map (algebraMap A B) I ≤
        Ideal.comap (f : B →+* C)
          (Ideal.map (f : B →+* C) (Ideal.map (algebraMap A B) I)) from
      Ideal.le_comap_map)

-- Proof sketch: choose the polynomial witness for `ebar` from Lemma `15.9.9`, then apply the
-- étale factorization lift of Lemma `15.9.6` to split it modulo `I` into the factors `X^d` and
-- `(X - 1)^d` after an étale base change inducing `A / I ≃ A' / I A'`. Evaluating the lifted
-- factors at a chosen lift of `ebar` in the tensor product gives orthogonal elements whose
-- corresponding clopen decomposition of `Spec (B ⊗[A] A')` yields an idempotent lifting `ebar`.
/-- Lemma 15.9.10: if `A → B` is integral and `ebar` is an idempotent of `B / I B`, then after an
étale base change `A → A'` inducing an isomorphism `A / I ≃ A' / I A'`, there is an idempotent in
`B ⊗[A] A'` whose image in the quotient by the extended ideal `I` is the base-change of `ebar`. -/
theorem exists_etale_baseChange_idempotent_lift_of_isIdempotentElem_mod_map
    (I : Ideal A) (ebar : B ⧸ I.map (algebraMap A B)) (hebar : IsIdempotentElem ebar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (e' : B ⊗[A] A'),
      IsIdempotentElem e' ∧
        (Ideal.quotientMapₐ (Ideal.map (algebraMap A (B ⊗[A] A')) I)
          (includeLeft : B →ₐ[A] B ⊗[A] A')
          (extendedIdeal_le_comap_extendedIdeal I
            (includeLeft : B →ₐ[A] B ⊗[A] A'))) ebar =
          Ideal.Quotient.mk (Ideal.map (algebraMap A (B ⊗[A] A')) I) e' := sorry

end

end Algebra
