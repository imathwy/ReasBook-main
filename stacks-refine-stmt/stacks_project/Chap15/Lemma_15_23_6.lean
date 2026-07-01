import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: reflexive finite modules over Noetherian domains and their finite-free
  presentations;
- sampled owner declarations:
  `Module.IsReflexive`,
  `isTorsionFree_iff_exists_injective_to_fin_fun`,
  `Module.exists_finite_presentation`,
  `Module.FinitePresentation.iff_exists_exact_free_sequence`,
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`;
- best owner abstraction: the source-facing short exact sequence should be expressed through the
  canonical cokernel `((Fin n → R) ⧸ LinearMap.range f)` of an injective map into a finite free
  module, rather than through an auxiliary witness structure carrying a separate quotient type and
  a surjective map onto it;
- source/core/bridge triage:
  - `source-facing`: this lemma is the textbook characterization of reflexive modules by a short
    exact sequence `0 → M → R^n → N → 0` with torsion-free quotient;
  - `core/canonical`: `Module.IsReflexive`, `LinearMap.range`, and the canonical quotient map
    `Submodule.mkQ`;
  - `bridge/view`: any separate torsion-free quotient `N` is equivalent to the canonical cokernel
    of the embedding, so it should remain derived rather than primitive public data.

Primitive data are an injective map `f : M →ₗ[R] (Fin n → R)` and torsion-freeness of its
canonical cokernel. The exact sequence and quotient object from the source are derived from
`f` via `Submodule.mkQ (LinearMap.range f)`, so the local structure previously packaging these
data was duplicate wheel API.
-/

section

open Function Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: for the forward direction, choose a finite presentation of `Module.Dual R M`,
-- dualize it, and use reflexivity of `M` to identify the resulting kernel with `M`; the quotient
-- is canonically the cokernel of the chosen embedding into `R^n`, and it is torsion free over a
-- domain. For the reverse direction, finite free modules are reflexive, and Lemma `15.23.5`
-- applies to the canonical short exact sequence
-- `0 → M → R^n → (R^n / range f) → 0` once the cokernel is assumed torsion free.
/-- Lemma 15.23.6: a finite module over a Noetherian domain is reflexive if and only if it admits
an injective map into a finite free module `R^n` whose canonical cokernel is torsion free;
equivalently, it fits into a short exact sequence `0 → M → R^n → N → 0` with `N` torsion free. -/
theorem isReflexive_iff_exists_injective_to_fin_fun_with_torsionFree_cokernel :
    IsReflexive R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R),
        Injective f ∧ IsTorsionFree R ((Fin n → R) ⧸ LinearMap.range f) :=
  sorry

end
