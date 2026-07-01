import Mathlib.LinearAlgebra.Dual.Defs

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Module

/-
Domain-style sampling:
- primary domain: module duality, double duals, and reflexivity for modules;
- sampled owner declarations:
  `Dual`,
  `Module.Dual.eval`,
  `Module.IsReflexive`,
  `Module.evalEquiv`;
- best owner abstraction: the source term "reflexive hull" is just the canonical double-dual
  owner type `Dual R (Dual R M)`;
- primitive data: the commutative semiring `R`, the additive commutative monoid `M`, and the
  ambient module structure;
- derived API: the surrounding evaluation and reflexivity statements are already owned by
  `Module.Dual.eval` and `Module.IsReflexive`.

Source/core/bridge triage:
- `source-facing`: the textbook phrase "the reflexive hull of `M`";
- `core/canonical`: the double-dual type `Dual R (Dual R M)`;
- `bridge/view`: later lemmas comparing `M` with its double dual through the evaluation map.

This item is therefore a pure canonical recall/check item, not a place for a new public alias.
-/

section ReflexiveHull

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/- Definition 15.23.9: the textbook reflexive hull of `M` is the canonical double-dual
`R`-module `Hom_R(Hom_R(M, R), R)`. The source states this for finite modules over a Noetherian
domain, but the recalled owner type itself already lives over the weaker canonical assumptions
`[CommSemiring R] [AddCommMonoid M] [Module R M]`. -/
#check (Dual R (Dual R M))

end ReflexiveHull
