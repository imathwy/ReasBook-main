import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Domain-style sampling:
* primary domain: factorization of linear maps through projective/free modules;
* sampled owner declarations:
  `Module.Projective`,
  `Module.projective_lifting_property`,
  `Module.Projective.iff_split`,
  `Module.Free`,
  `Module.Projective.of_free`,
  `Module.Free.of_subsingleton`;
* best owner abstraction: `Module.Projective R P` and `Module.Free R P` are the canonical owner
  properties on the intermediate module, while the source-facing public owner in this file is the
  induced predicate on a linear map;
* layer triage:
  `Module.Projective` and `Module.Free` are `core/canonical`,
  `FactorsThroughProjective` is `source-facing`,
  `FactorsThroughFree` is a `bridge/view` companion used in Lemma `15.71.1`;
* primitive data: an intermediate module `P` together with maps `M →ₗ[R] P →ₗ[R] N`;
* derived API: the tautological factorization for maps out of a projective domain, the zero-map
  factorization, and the free factorization criterion supplied by
  `factorsThroughProjective_iff_factorsThroughFree`.
-/

namespace LinearMap

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

open Module.Projective
open ULift

/-- A linear map factors through a projective `R`-module. -/
def FactorsThroughProjective (φ : M →ₗ[R] N) : Prop :=
  ∃ (P : Type (max u v w)) (_ : AddCommMonoid P) (_ : Module R P) (_ : Module.Projective R P)
    (f : M →ₗ[R] P) (g : P →ₗ[R] N), φ = g.comp f

/-- A linear map factors through a free `R`-module. -/
def FactorsThroughFree (φ : M →ₗ[R] N) : Prop :=
  ∃ (P : Type (max u v w)) (_ : AddCommMonoid P) (_ : Module R P) (_ : Module.Free R P)
    (f : M →ₗ[R] P) (g : P →ₗ[R] N), φ = g.comp f

/-- Any linear map with projective domain factors through a projective module. -/
theorem factorsThroughProjective_of_projective (φ : M →ₗ[R] N) [Module.Projective R M] :
    φ.FactorsThroughProjective := by
  let e : ULift.{max u w} M ≃ₗ[R] M := moduleEquiv
  let _ : Module.Projective R (ULift.{max u w} M) :=
    of_equiv' e.symm
  exact ⟨ULift.{max u w} M, inferInstance, inferInstance, inferInstance,
    e.symm.toLinearMap, φ.comp e.toLinearMap, by
      ext m
      rfl
  ⟩

/-- A free factorization is in particular a projective factorization. -/
theorem FactorsThroughFree.factorsThroughProjective {φ : M →ₗ[R] N}
    (hφ : φ.FactorsThroughFree) : φ.FactorsThroughProjective := by
  rcases hφ with ⟨F, _, _, _, f, g, rfl⟩
  exact ⟨F, inferInstance, inferInstance, inferInstance, f, g, rfl⟩

/-- The zero map factors through a projective module. -/
lemma factorsThroughProjective_zero :
    (0 : M →ₗ[R] N).FactorsThroughProjective := by
  exact ⟨PUnit, inferInstance, inferInstance, inferInstance, 0, 0, by
    ext m
    simp
  ⟩

/-- Any projective factorization may be refined to a free factorization. -/
theorem FactorsThroughProjective.factorsThroughFree {φ : M →ₗ[R] N}
    (hφ : φ.FactorsThroughProjective) : φ.FactorsThroughFree := by
  rcases hφ with ⟨P, _, _, hP, f, g, rfl⟩
  rcases iff_split.mp hP with ⟨F, _, _, _, i, s, hs⟩
  refine ⟨F, inferInstance, inferInstance, inferInstance, i.comp f, g.comp s, ?_⟩
  ext m
  exact congrArg g (LinearMap.congr_fun hs (f m)).symm

/-- Lemma 15.71.1: an `R`-linear map factors through a projective module if and only if it
factors through a free module. -/
@[stacks 0G90]
theorem factorsThroughProjective_iff_factorsThroughFree (φ : M →ₗ[R] N) :
    φ.FactorsThroughProjective ↔ φ.FactorsThroughFree :=
  ⟨FactorsThroughProjective.factorsThroughFree, FactorsThroughFree.factorsThroughProjective⟩

end

end LinearMap
