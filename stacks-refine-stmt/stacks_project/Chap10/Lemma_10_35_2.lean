import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/- Domain triage:
* primary domain: commutative algebra of finite type algebras and Jacobson rings;
* source-facing layer: the field-specialized Jacobson statement from the Stacks lemma;
* core/canonical owner: `IsJacobsonRing` with the transfer theorem
  `isJacobsonRing_of_finiteType`;
* bridge/view layer: the only specialization is the instance `Field k → IsJacobsonRing k`;
* primitive data vs. derived API: the `k`-algebra structure on `A` together with
  `[Algebra.FiniteType k A]` are the primitive inputs, while the Jacobson conclusion is exactly the
  derived owner-level theorem, so no parallel local wrapper is needed here.
-/
/- Lemma 10.35.2: any commutative algebra of finite type over a field is a Jacobson ring. This is
the field-specialized case of the canonical theorem `isJacobsonRing_of_finiteType`, with the
Jacobson hypothesis on `k` supplied by the instance `Field k`. -/
recall isJacobsonRing_of_finiteType

end
