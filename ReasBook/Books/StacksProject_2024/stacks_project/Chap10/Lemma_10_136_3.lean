import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_136_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

namespace RingHom

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling:
- primary domain: syntomic ring maps under tensor-product base change in commutative algebra;
- inspected owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Syntomic.ofLocalizationSpanTarget`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`,
  `Algebra.Smooth.baseChange`;
- best owner abstraction:
  `RingHom.Syntomic` is the owner predicate, while the tensor-product base change
  `R' → R' ⊗[R] S` is the canonical bridge/view on which the stability theorem should live;
- primitive vs. derived:
  flatness, finite presentation, and local-complete-intersection fibers are derived projections of
  `RingHom.Syntomic`, so this file should expose only the owner-namespace base-change theorem
  rather than a parallel freestanding wrapper.
-/

namespace Syntomic

-- Proof sketch: unpack `hf` into flatness, finite presentation, and local complete-intersection
-- fibers. The first two properties are preserved by base change by the canonical base-change
-- results, and each fiber of `R' → R' ⊗[R] S` is a residue-field extension of a fiber of
-- `R → S`, so Lemma `10.135.11` transports the local complete-intersection condition.
/-- Lemma 10.136.3: any base change of a syntomic ring map is syntomic. -/
theorem baseChange (hf : (algebraMap R S).Syntomic) :
    (algebraMap R' (R' ⊗[R] S)).Syntomic := sorry

end Syntomic

end RingHom

end
