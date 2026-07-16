import StacksProject_2024.stacks_project.Chap15.Lemma_15_23_5
import StacksProject_2024.stacks_project.Chap10.Definition_10_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Domain-style sampling:
- primary domain: duality and reflexivity of finitely presented modules over domains, together
  with the exactness behavior of `Hom_R(-, N)`;
- sampled owner declarations:
  `Module.IsReflexive`,
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`,
  `Module.FinitePresentation.iff_exists_exact_free_sequence`,
  `LinearMap.exact_lcomp_of_exact_of_surjective`,
  `LinearMap.instIsTorsionFree`,
  `Prod.instModuleIsReflexive`;
- best owner abstraction: the public owner remains the reflexivity class `Module.IsReflexive`,
  while the chapter-level kernel-closure theorem
  `isReflexive_of_exact_of_isReflexive_of_isTorsionFree` is the right bridge/view API for this
  source-facing item. The finite presentation of `M` should be unpacked through the chapter bridge
  `Module.FinitePresentation.iff_exists_exact_free_sequence`, which exposes the exact free
  sequence actually used in the argument, rather than through a lower-level quotient witness or the
  stronger Noetherian-plus-finite wrapper. Torsion-freeness of the ambient `Hom` modules should
  come from the upstream owner instance `LinearMap.instIsTorsionFree`, and the finite-product
  reflexivity step should be reduced to mathlib's owner instance
  `Prod.instModuleIsReflexive` plus `Module.pi_induction'`, not rebuilt as a separate local API;
- source/core/bridge triage:
  - `source-facing`: the textbook assertion that `Hom_R(M, N)` is reflexive when `M` is finite and
    `N` is finite reflexive over a Noetherian domain, refined to the equivalent weaker statement
    where the primitive input on `M` is a finite presentation;
  - `core/canonical`: `Module.IsReflexive`;
  - `bridge/view`: the exact-sequence closure theorem
    `isReflexive_of_exact_of_isReflexive_of_isTorsionFree` applied to the `Hom` sequence induced by
    a finite presentation of `M`.

Primitive data are the exact free presentation `R^m → R^n → M → 0` attached to
`Module.FinitePresentation R M` and the induced exact sequence
`0 → Hom_R(M, N) → Hom_R(R^n, N) → Hom_R(R^m, N)`. The reflexivity of the middle term and the
torsion-freeness of the quotient are derived from the owner abstractions above; they should not be
repackaged here as new primitive public data.
-/

section

open Function LinearMap Module

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
variable [AddCommGroup N] [Module R N] [Module.Finite R N] [IsReflexive R N]

omit [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [IsReflexive R N] in
variable (R N) in
/-- Helper for Lemma 15.23.8: a finite product of reflexive modules is reflexive. -/
private theorem isReflexive_finFun [CommRing R] [AddCommGroup N] [Module R N] [IsReflexive R N]
    (n : ℕ) :
    IsReflexive R (Fin n → N) := by
  classical
  -- Reduce the finite product to the canonical `pi`-induction principle for module properties.
  refine Module.pi_induction' R
    (fun P _ _ ↦ IsReflexive R P)
    (fun P _ _ ↦ IsReflexive R P)
    (fun e h ↦ by
      letI := h
      exact Module.equiv e)
    (fun e h ↦ by
      letI := h
      exact Module.equiv e)
    (by infer_instance)
    (fun hP hQ ↦ by
      letI := hP
      letI := hQ
      infer_instance)
    (fun _ : Fin n ↦ N)
    fun _ ↦ inferInstance

omit [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [IsReflexive R N] in
variable (R N) in
/-- Helper for Lemma 15.23.8: `Hom_R(R^n, N)` is reflexive by identifying it with `N^n`. -/
private theorem isReflexive_linearMap_finFun [CommRing R] [AddCommGroup N] [Module R N]
    [IsReflexive R N] (n : ℕ) :
    IsReflexive R ((Fin n → R) →ₗ[R] N) := by
  -- Transport reflexivity across the standard equivalence `Hom_R(R^n, N) ≃ N^n`.
  letI : IsReflexive R (Fin n → N) := isReflexive_finFun R N n
  exact Module.equiv (LinearEquiv.piRing R N (Fin n) R).symm

-- Proof sketch: unpack `Module.FinitePresentation R M` via
-- `Module.FinitePresentation.iff_exists_exact_free_sequence` to obtain
-- `R^m → R^n → M → 0`, apply `Hom_R(-, N)` to get an exact sequence
-- `0 → Hom_R(M, N) → N^n → N' → 0`, and note that `N'` is torsion free as a submodule of `N^m`.
-- Since finite products of reflexive modules are reflexive by the owner instance
-- `Prod.instModuleIsReflexive`, `Module.pi_induction'` upgrades this to `N^n`, and
-- `LinearEquiv.piRing` transports it to `Hom_R(R^n, N)`. Lemma `15.23.5` applied to the resulting
-- exact sequence yields reflexivity of `Hom_R(M, N)`.
/-- Lemma 15.23.8: if `M` is finitely presented and `N` is finite reflexive over a domain `R`,
then the `R`-module `Hom_R(M, N)` is reflexive. Over a Noetherian domain, this recovers the
textbook finite-module formulation because finite modules are finitely presented. -/
theorem isReflexive_linearMap :
    IsReflexive R (M →ₗ[R] N) := by
  -- Route correction: keep the proof at the exact-sequence level coming from a free presentation of
  -- `M`, rather than unfolding duals or reconstructing the cokernel by hand.
  -- This source-facing statement should be derived from the chapter owner bridge
  -- `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`, using the exact `Hom` sequence
  -- provided by the chapter bridge `Module.FinitePresentation.iff_exists_exact_free_sequence`
  -- and the canonical torsion-free owner `LinearMap.instIsTorsionFree` on the ambient `Hom`
  -- module.
  rcases (Module.FinitePresentation.iff_exists_exact_free_sequence R M).mp inferInstance with
    ⟨n, m, f, g, hfg, hg⟩
  -- Apply `Hom_R(-, N)` to the presentation to get the exact sequence from the source proof.
  have hExact : Exact (lcomp R N g) (lcomp R N f) :=
    exact_lcomp_of_exact_of_surjective N hfg hg
  have hInj : Injective (lcomp R N g) :=
    lcomp_injective_of_surjective g hg
  -- The middle `Hom` term is a finite product of copies of `N`, hence finite and reflexive.
  letI : Module.Finite R ((Fin n → R) →ₗ[R] N) := Module.Finite.linearMap R R (Fin n → R) N
  letI : IsReflexive R ((Fin n → R) →ₗ[R] N) := isReflexive_linearMap_finFun R N n
  -- Lemma 15.23.5 now identifies `Hom_R(M, N)` as the reflexive kernel of this exact sequence.
  exact isReflexive_of_exact_of_isReflexive_of_isTorsionFree hExact hInj

end
