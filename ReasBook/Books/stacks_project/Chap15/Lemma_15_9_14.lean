import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain-style sampling:
- primary domain: étale lifting for smooth commutative algebras over a quotient;
- sampled owner declarations:
  `Algebra.Smooth`,
  `Algebra.Etale`,
  `Ideal.Quotient.mkₐ`,
  `exists_etale_finite_projective_lift_of_finite_projective_quotient`;
- best owner abstraction: the source-facing owner here is the smooth lifting existence theorem
  itself, with the comparison to the quotient expressed through the canonical quotient algebra map
  `Ideal.Quotient.mkₐ`; the quotient isomorphism is bridge data, not a separate owner;
- primitive data: the ideal `I`, the smoothness hypothesis on `A → B`, and the quotient map
  `φ : B →ₐ[A] A ⧸ I`;
- derived API: the lifted étale `A`-algebra `A'`, the quotient equivalence `eIso`, and the lifted
  algebra map `φ' : B →ₐ[A] A'` satisfying the canonical quotient-map compatibility equation.

Source/core/bridge triage:
- `source-facing`: the present existence theorem lifting `φ` étale-locally;
- `core/canonical`: the owner predicates `Algebra.Smooth` and `Algebra.Etale`, together with the
  quotient algebra map `Ideal.Quotient.mkₐ`;
- `bridge/view`: the quotient equivalence `eIso`.
-/

-- Proof sketch: use the conormal exact sequence for the surjection `B → A ⧸ I` and smoothness of
-- `A → B` to see that the conormal module is finite projective over `A ⧸ I`. Lift a complement of
-- this module after an étale base change by Lemma `15.9.11`, add the corresponding symmetric
-- algebra factor to make the conormal module free, cut down by generators of the kernel, and then
-- localize at the étale locus as in Lemma `15.9.4` to obtain the desired étale algebra `A'` and
-- lift `B → A'`.
/-- Lemma 15.9.14: if `B` is a smooth `A`-algebra equipped with an `A`-algebra map
`φ : B → A ⧸ I`, then there exists an étale `A`-algebra `A'` whose reduction modulo `I` is
canonically isomorphic to `A ⧸ I`, together with an `A`-algebra map `φ' : B → A'` lifting `φ`
through that quotient isomorphism. -/
theorem exists_etale_lift_to_quotient_of_smooth
    (I : Ideal A) [Algebra.Smooth A B] (φ : B →ₐ[A] A ⧸ I) :
    ∃ (A' : Type (max u v)) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (φ' : B →ₐ[A] A'),
      ((Ideal.Quotient.mkₐ A' (Ideal.map (algebraMap A A') I)).restrictScalars A).comp φ' =
        (eIso.toAlgHom.restrictScalars A).comp φ := sorry

end

end Algebra
