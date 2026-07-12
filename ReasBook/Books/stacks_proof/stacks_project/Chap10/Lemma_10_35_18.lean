import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K]
variable [IsJacobsonRing R] [Algebra.FiniteType R K]

/- Domain triage:
* primary domain: Jacobson rings and finite type field-valued algebras;
* source-facing layer: the Stacks lemma asserting that a finite type field over a Jacobson ring is
  module-finite over the base;
* core/canonical owner: mathlib's theorem `finite_of_finite_type_of_isJacobsonRing`;
* bridge/view layer: none is needed here, since the source statement already matches the owner
  theorem exactly;
* primitive data vs. derived API: the primitive inputs are the Jacobson base ring `R`, the
  field-valued `R`-algebra `K`, and the finite type hypothesis; `Module.Finite R K` is derived
  directly from the owner theorem, so there is no local wrapper API to keep.
-/

/- Lemma 10.35.18 (Stacks tag `0CY7`): if `R` is a Jacobson ring and `K` is a field of finite
type over `R`, then `K` is finite as an `R`-module. This is exactly the canonical theorem
`finite_of_finite_type_of_isJacobsonRing`. -/
recall finite_of_finite_type_of_isJacobsonRing

end
