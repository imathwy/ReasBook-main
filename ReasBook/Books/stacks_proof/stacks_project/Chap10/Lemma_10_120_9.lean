import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.9 lies in the ACCP / factorization-theory domain for integral domains.

Domain-style sampling:
- `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt` is the owner bridge turning ACCP on
  principal ideals into the canonical well-founded divisibility abstraction.
- `Polynomial.wfDvdMonoid` is the canonical polynomial-ring instance for that owner abstraction.
- `Ideal.setOf_isPrincipal_wellFoundedOn_gt` transports the owner abstraction back to ACCP on
  principal ideals.

Layer triage:
- `source-facing`: the polynomial-stability statement below.
- `core/canonical`: `WfDvdMonoid`.
- `bridge/view`: the two principal-ideal well-foundedness theorems above.

Primitive data are just the ACCP hypothesis on `R`; the ACCP statement for `R[X]` is derived API
through the owner abstraction, so this file should reuse that owner bridge directly. -/
/-- Lemma 10.120.9: if a domain satisfies the ascending chain condition on principal ideals,
then the same property holds for its polynomial ring. -/
-- Proof sketch: convert the ACCP hypothesis on principal ideals in `R` into the canonical
-- `WfDvdMonoid R` structure using
-- `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt`; then use the polynomial-ring instance
-- `Polynomial.wfDvdMonoid` and translate back to ACCP on principal ideals of `R[X]` via
-- `Ideal.setOf_isPrincipal_wellFoundedOn_gt`.
@[stacks 0BUE]
theorem polynomial_accp_of_accp
    (hacc : {I : Ideal R | I.IsPrincipal}.WellFoundedOn (· > ·)) :
    {I : Ideal R[X] | I.IsPrincipal}.WellFoundedOn (· > ·) := by
  -- Convert the ACCP hypothesis on `R` into the canonical well-founded divisibility structure.
  let hR : WfDvdMonoid R := WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt hacc
  -- Build the polynomial `WfDvdMonoid` instance explicitly to avoid broad typeclass search.
  let hRX : WfDvdMonoid R[X] := @Polynomial.wfDvdMonoid R inferInstance inferInstance hR
  -- Translate the owner abstraction back to ACCP on principal ideals of `R[X]`.
  exact @Ideal.setOf_isPrincipal_wellFoundedOn_gt (R[X]) inferInstance hRX inferInstance

end
