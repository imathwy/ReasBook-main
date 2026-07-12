import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/- Domain-style sampling:
- primary domain: module duality and reflexivity for modules over a commutative semiring;
- sampled owner declarations:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `Module.bijective_dual_eval`,
  `Module.evalEquiv`;
- best owner abstraction: `Module.IsReflexive` is the canonical owner of the source notion
  "reflexive module", and `Module.Dual.eval` is the canonical realization of the textbook
  evaluation map into the double dual;
- source/core/bridge triage:
  `source-facing`: the textbook definition of a reflexive module via the canonical map to the
    double dual;
  `core/canonical`: `Module.IsReflexive`;
  `bridge/view`: the companion identification of the textbook map with `Module.Dual.eval`.

Primitive data are only the ambient ring `R`, module `M`, and the canonical double-dual evaluation
map. Reflexivity itself is derived API owned by `Module.IsReflexive`, so this file should remain a
direct recall of the owner and the canonical map, with no local wrapper around the double dual or
its evaluation morphism.
-/
/- Definition 15.23.1: an `R`-module `M` is reflexive in the textbook sense exactly when it
is the canonical mathlib class `Module.IsReflexive R M`, saying that the natural evaluation map
from `M` to its double dual is bijective, equivalently an isomorphism of `R`-modules. -/
recall Module.IsReflexive

/- Companion recall: the textbook map
`j : M → Hom_R(Hom_R(M, R), R)` sending `m` to the functional `φ ↦ φ m`
is the canonical linear map `Module.Dual.eval R M`. -/
recall Module.Dual.eval

end
