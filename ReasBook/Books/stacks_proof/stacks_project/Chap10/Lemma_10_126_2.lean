import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: faithfully flat descent and base-change stability for finite-presentation of
  commutative algebras;
- sampled canonical declarations of the same kind:
  `Algebra.FinitePresentation.baseChange`,
  `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`,
  `RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`;
- best owner abstraction: the predicate `Algebra.FinitePresentation R S`;
- primitive data: the commutative rings `R`, `S`, `R'`, the algebra structures `R → S` and
  `R → R'`, and the faithfully flat base change `R → R'`;
- derived API: base-change stability and faithfully flat descent for that owner predicate.

Layering:
- this numbered item is `source-facing`: it packages the canonical forward base-change instance and
  reverse descent theorem into the textbook `iff`, without introducing any parallel owner API.
-/

-- Proof sketch: the forward implication is the standard base-change stability of finite
-- presentation. For the reverse implication, apply the canonical faithfully flat descent theorem
-- `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` to the
-- base-changed algebra `R' ⊗[R] S`.
/-- Lemma 10.126.2: for a faithfully flat base change `R → R'`, the `R`-algebra `S` is of finite
presentation over `R` if and only if the base-changed `R'`-algebra `R' ⊗[R] S` is of finite
presentation over `R'`. -/
@[stacks 00QQ]
theorem finitePresentation_iff_finitePresentation_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    Algebra.FinitePresentation R S ↔ Algebra.FinitePresentation R' (R' ⊗[R] S) := by
  letI : Module.FaithfullyFlat R R' :=
    (RingHom.faithfullyFlat_algebraMap_iff : (algebraMap R R').FaithfullyFlat ↔
      Module.FaithfullyFlat R R').mp hff
  constructor
  · intro _
    infer_instance
  · intro _
    simpa using Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat R'

end
