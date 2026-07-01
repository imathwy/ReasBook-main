import Mathlib
import stacks_project.Chap10.Definition_10_136_1
import stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: relative complete intersections and syntomic morphisms of commutative rings;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`;
- best owner abstraction:
  `Algebra.IsRelativeGlobalCompleteIntersection R S` is the source-facing owner for the algebra,
  while `(algebraMap R S).Syntomic` is the canonical ring-hom owner on the conclusion side;
- primitive vs. derived:
  the relative global complete intersection witness is primitive data in the source-facing class,
  whereas syntomicity is derived API and should be exposed as a theorem under that owner rather
  than as a parallel standalone theorem name.
-/

namespace IsRelativeGlobalCompleteIntersection

-- Proof sketch: a relative global complete intersection is finitely presented by definition, and
-- each fiber is a global complete intersection, hence a local complete intersection. The only new
-- ingredient is flatness, which is obtained from the localized prefix-quotient flatness statement
-- of Lemma `10.136.12 (2)` after choosing a presentation locally at each prime of `S`.
/-- Lemma 10.136.13: a relative global complete intersection `R`-algebra is syntomic over `R`. -/
theorem syntomic (hS : IsRelativeGlobalCompleteIntersection R S) :
    (algebraMap R S).Syntomic := sorry

end IsRelativeGlobalCompleteIntersection

end

end Algebra
