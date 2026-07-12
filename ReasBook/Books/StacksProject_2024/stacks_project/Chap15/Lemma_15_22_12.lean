import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Domain-style sampling:
- primary domain: torsion-free semimodules and semilinear-map modules;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Function.Injective.moduleIsTorsionFree`,
  `LinearMap.instIsTorsionFree`,
  `Module.IsTorsionFree.of_smul_eq_zero`;
- best owner abstraction: the proposition-level owner `Module.IsTorsionFree`, with the linear-map
  module instance `LinearMap.instIsTorsionFree` as the canonical owner declaration for this item;
- source/core/bridge triage:
  `source-facing`: the textbook assertion that `Hom_R(M, N)` is torsion free when `N` is;
  `core/canonical`: `LinearMap.instIsTorsionFree`;
  `bridge/view`: none needed, since the source statement already coincides with the canonical owner
  instance.

Primitive data are the semiring `R`, the source and target `R`-semimodules, and the
torsion-freeness instance on `N`. The torsion-free structure on `M →ₗ[R] N` is derived API owned
upstream by `LinearMap.instIsTorsionFree`, so this file should recall that instance directly at the
weaker canonical semiring/additive-monoid level instead of using an anonymous `inferInstance`
check.
-/

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.IsTorsionFree R N]

/- Lemma 15.22.12: if `N` is a torsion-free `R`-module over a domain `R`, then the `R`-module
of homomorphisms `M →ₗ[R] N` is torsion free. Mathlib's owner instance is stronger: it already
holds for `R` a semiring and `M`, `N` additive commutative monoids. -/
recall LinearMap.instIsTorsionFree

end
