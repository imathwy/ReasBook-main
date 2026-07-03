import stacks_project.Chap15.Lemma_15_9_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
* sampled owner declarations:
  `exists_etale_lift_to_quotient_of_smooth`,
  `IsIdempotentElem`,
  `Ideal.Quotient.mk`;
* `source-facing`: the étale-local lifting statement for one idempotent in `A ⧸ I`;
* `core/canonical`: the smooth lifting owner `exists_etale_lift_to_quotient_of_smooth`;
* `bridge/view`: this theorem is the idempotent-specialized consequence obtained from that owner
  by applying it to the standard smooth algebra carrying a universal idempotent section.

Primitive data: the quotient idempotent `ebar`.
Derived API: the quotient isomorphism `eIso` and the lifted idempotent `e'`.

To match the surrounding Chapter 15 owner surface, the quotient isomorphism is exposed as a primary
binder, not hidden inside a trailing nested existential after `e'`.
-/

-- Proof sketch: apply the smooth lifting owner theorem `exists_etale_lift_to_quotient_of_smooth`
-- to the standard smooth `A`-algebra representing an idempotent section reducing to `ebar`. The
-- resulting étale algebra `A'`, quotient isomorphism `eIso`, and lifted section `e'` give the
-- desired idempotent lift.
/-- Lemma 15.9.2: for an idempotent `ebar` in the quotient ring `A ⧸ I`, there exists an étale
`A`-algebra `A'` whose reduction modulo `I` is canonically isomorphic to `A ⧸ I`, together with an
idempotent `e' ∈ A'` mapping to `ebar` under that isomorphism. -/
theorem exists_etale_idempotent_lift_of_quotient (I : Ideal A) (ebar : A ⧸ I)
    (hebar : IsIdempotentElem ebar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I)) (e' : A'),
      IsIdempotentElem e' ∧
        eIso ebar = Ideal.Quotient.mk (Ideal.map (algebraMap A A') I) e' := by
  sorry

end

end Algebra
