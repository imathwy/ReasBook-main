import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.Finiteness.Cardinality

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: finite modules over domains, torsion-freeness, and embeddings into finite free
  modules;
- sampled owner API:
  `Module.IsTorsionFree`,
  `Basis.isTorsionFree`,
  `Function.Injective.moduleIsTorsionFree`,
  `Module.Finite.exists_fin'`,
  `LinearIndependent.iff_fractionRing`;
- best owner abstraction: `Module.IsTorsionFree`, with `Fin n → R` as the canonical finite free
  model used by `Module.Finite.exists_fin'`;
- source-facing layer: the Stacks equivalence between torsion-freeness and embeddability into a
  finite free module;
- core/canonical layer: the torsion-free owner `Module.IsTorsionFree`;
- bridge/view layer: the canonical finite free model `Fin n → R` and injective linear maps
  `M →ₗ[R] (Fin n → R)`.

Primitive data are only the finite `R`-module `M` and the owner predicate
`Module.IsTorsionFree R M`. Mathlib provides the owner abstractions used in the proof, but not this
exact equivalence as a canonical theorem, so the source-facing statement should remain here instead
of being replaced by a less usable existential package around `Module.Free`.
-/

section

open Module

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: if `M` embeds into `Fin n → R`, then it is torsion free because submodules of a
-- torsion-free module are torsion free. Conversely, tensor `M` with the fraction field of `R`,
-- choose a basis of the resulting finite-dimensional vector space, clear denominators on a finite
-- generating set of `M`, and obtain an injective map from `M` into `R^n`.
/-- Lemma 15.22.7: a finite module over a domain is torsion free if and only if it admits an
injective linear map into a finite free module, expressed here in the canonical model
`Fin n → R`. -/
theorem isTorsionFree_iff_exists_injective_to_fin_fun :
    Module.IsTorsionFree R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R), Function.Injective f := sorry

end
