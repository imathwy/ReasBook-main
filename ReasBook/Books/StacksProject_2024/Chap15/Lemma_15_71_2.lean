import Mathlib
import StacksProject_2024.Chap15.Lemma_15_71_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Domain-style sampling:
* primary domain: factorization of linear maps through finite projective modules;
* sampled owner declarations:
  `LinearMap.FactorsThroughProjective`,
  `Module.Finite`,
  `Module.Projective`,
  `Module.FiniteProjective`;
* best owner abstraction: the canonical owner predicates on the intermediate module are
  `Module.Finite R P` and `Module.Projective R P`; the source-facing public owner in this file is
  the induced predicate on a linear map recording factorization through such an intermediate
  module, since the project-level abbreviation `Module.FiniteProjective` is restricted to the
  commutative-ring/additive-group setting and would strengthen the present semiring semantics;
* layer triage:
  `Module.Finite` and `Module.Projective` are `core/canonical`,
  `FactorsThroughFiniteProjective` is `source-facing`,
  `FactorsThroughFiniteProjective.factorsThroughProjective` is the `bridge/view` that forgets
  finiteness;
* primitive data: an intermediate module `P` together with maps `M →ₗ[R] P →ₗ[R] N`;
* derived API: forgetting finiteness yields a projective factorization, and when `M` is finite a
  projective factorization upgrades to a finite-projective one by shrinking a free factorization
  to a finite free submodule.
-/

namespace LinearMap

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- A linear map factors through a finite projective `R`-module. -/
def FactorsThroughFiniteProjective (φ : M →ₗ[R] N) : Prop :=
  ∃ (P : Type (max u v w)) (_ : AddCommMonoid P) (_ : Module R P)
    (_ : Module.Finite R P) (_ : Module.Projective R P)
    (f : M →ₗ[R] P) (g : P →ₗ[R] N), φ = g.comp f

-- Proof sketch: forget the finiteness assumption on the intermediate module in the defining
-- factorization.
/-- A finite-projective factorization is in particular a projective factorization. -/
theorem FactorsThroughFiniteProjective.factorsThroughProjective {φ : M →ₗ[R] N}
    (hφ : φ.FactorsThroughFiniteProjective) : φ.FactorsThroughProjective := sorry

-- Proof sketch: by Lemma `15.71.1`, first factor `φ` through a free module. Because `M` is finite,
-- finitely many generators of `M` have images supported on only finitely many basis vectors, so
-- the factorization lands in a finite free submodule. A finite free module is finite projective.
/-- Lemma 15.71.2: if an `R`-linear map `φ : M →ₗ[R] N` factors through a projective module and
`M` is a finite `R`-module, then `φ` factors through a finite projective `R`-module. -/
theorem FactorsThroughProjective.factorsThroughFiniteProjective [Module.Finite R M]
    {φ : M →ₗ[R] N} (hφ : φ.FactorsThroughProjective) :
    φ.FactorsThroughFiniteProjective := sorry

end

end LinearMap
