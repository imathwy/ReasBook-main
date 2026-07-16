import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import stacks_proof.stacks_project.Chap10.Definition_10_5_1
import stacks_proof.stacks_project.Chap15.Lemma_15_23_5
import Mathlib.Tactic.StacksAttribute

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

open Function LinearMap Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 15.23.6: an injective map into a finite free module with torsion-free
canonical cokernel makes the source reflexive via Lemma `15.23.5`. -/
private theorem canonical_quotient_reflexive_implication
    {n : ℕ} (f : M →ₗ[R] (Fin n → R)) (hf : Injective f)
    (hTorsionFree : IsTorsionFree R ((Fin n → R) ⧸ LinearMap.range f)) :
    IsReflexive R M := by
  let g : (Fin n → R) →ₗ[R] ((Fin n → R) ⧸ LinearMap.range f) := (LinearMap.range f).mkQ
  have hExact : Function.Exact f g := LinearMap.exact_map_mkQ_range f
  -- The middle finite free term is reflexive, so Lemma `15.23.5` applies to the canonical
  -- quotient sequence.
  letI : IsTorsionFree R (LinearMap.range g) := by
    infer_instance
  letI : IsReflexive R (Fin n → R) := Module.IsReflexive.of_finite_of_free
    (R := R) (M := Fin n → R)
  exact isReflexive_of_exact_of_isReflexive_of_isTorsionFree hExact hf

/-- Helper for Lemma 15.23.6: dualizing a finite free presentation yields an exact row on the raw
dual modules before any coordinate identifications are applied. -/
private theorem dual_presentation_exact_raw
    {n m : ℕ}
    (a : (Fin m → R) →ₗ[R] (Fin n → R))
    (b : (Fin n → R) →ₗ[R] Dual R M)
    (hab : Function.Exact a b) (hb : Function.Surjective b) :
    Function.Exact (LinearMap.lcomp R R b) (LinearMap.lcomp R R a) ∧
      Injective (LinearMap.lcomp R R b) := by
  constructor
  · -- Exactness is first established on the raw dual row produced by `lcomp`.
    exact LinearMap.exact_lcomp_of_exact_of_surjective R hab hb
  · -- Surjectivity of the presentation map makes precomposition by it injective.
    exact LinearMap.lcomp_injective_of_surjective b hb

/-- Helper for Lemma 15.23.6: the raw dual exact row becomes exact on coordinates after applying
`Module.evalEquiv` on the left and `LinearEquiv.piRing` in the free directions. -/
private theorem dual_presentation_exact_transport
    {n m : ℕ}
    (a : (Fin m → R) →ₗ[R] (Fin n → R))
    (b : (Fin n → R) →ₗ[R] Dual R M)
    [IsReflexive R M]
    (hRaw : Function.Exact (LinearMap.lcomp R R b) (LinearMap.lcomp R R a)) :
    let ι : M →ₗ[R] (Fin n → R) :=
      (LinearEquiv.piRing R R (Fin n) R).toLinearMap.comp
        ((LinearMap.lcomp R R b).comp (Module.evalEquiv R M).toLinearMap)
    let δ : (Fin n → R) →ₗ[R] (Fin m → R) :=
      (LinearEquiv.piRing R R (Fin m) R).toLinearMap.comp
        ((LinearMap.lcomp R R a).comp (LinearEquiv.piRing R R (Fin n) R).symm.toLinearMap)
    Function.Exact ι δ := by
  let eM : M ≃ₗ[R] Dual R (Dual R M) := Module.evalEquiv R M
  let en : Dual R (Fin n → R) ≃ₗ[R] (Fin n → R) := LinearEquiv.piRing R R (Fin n) R
  let em : Dual R (Fin m → R) ≃ₗ[R] (Fin m → R) := LinearEquiv.piRing R R (Fin m) R
  let α : Dual R (Dual R M) →ₗ[R] Dual R (Fin n → R) := LinearMap.lcomp R R b
  let β : Dual R (Fin n → R) →ₗ[R] Dual R (Fin m → R) := LinearMap.lcomp R R a
  dsimp
  intro y
  constructor
  · intro hy
    -- Remove the coordinate equivalence on the codomain, apply exactness on the raw row, and
    -- then repackage the witness back in `M`.
    have hyRaw : β (en.symm y) = 0 := by
      apply em.injective
      simpa only [β, em, en, LinearMap.comp_apply, LinearEquiv.apply_symm_apply] using hy
    obtain ⟨x, hx⟩ := (hRaw (en.symm y)).1 hyRaw
    have hxy : en (α x) = y := by
      simpa only [LinearEquiv.apply_symm_apply] using congrArg en hx
    refine ⟨eM.symm x, ?_⟩
    simpa only [α, eM, en, LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply] using hxy
  · rintro ⟨x, hx⟩
    -- Push the coordinate equality back to the raw middle term and use exactness there.
    have hxRaw : α (eM x) = en.symm y := by
      simpa only [α, eM, en, LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.symm_apply_apply] using
        congrArg en.symm hx
    have hyRaw : β (en.symm y) = 0 := by
      rw [← hxRaw]
      exact (hRaw (α (eM x))).2 ⟨eM x, rfl⟩
    simpa only [β, em, en, LinearMap.comp_apply, hyRaw, map_zero]

/-- Helper for Lemma 15.23.6: the same coordinate transport preserves injectivity of the left map
coming from the raw dual row. -/
private theorem dual_presentation_injective_transport
    {n : ℕ}
    (b : (Fin n → R) →ₗ[R] Dual R M)
    [IsReflexive R M]
    (hRaw : Injective (LinearMap.lcomp R R b)) :
    let ι : M →ₗ[R] (Fin n → R) :=
      (LinearEquiv.piRing R R (Fin n) R).toLinearMap.comp
        ((LinearMap.lcomp R R b).comp (Module.evalEquiv R M).toLinearMap)
    Injective ι := by
  let eM : M ≃ₗ[R] Dual R (Dual R M) := Module.evalEquiv R M
  let en : Dual R (Fin n → R) ≃ₗ[R] (Fin n → R) := LinearEquiv.piRing R R (Fin n) R
  let α : Dual R (Dual R M) →ₗ[R] Dual R (Fin n → R) := LinearMap.lcomp R R b
  dsimp
  intro x y hxy
  -- Both coordinate changes are equivalences, so injectivity reduces to the raw dual map.
  refine eM.injective ?_
  apply hRaw
  apply en.injective
  simpa only [α, eM, en, LinearMap.comp_apply] using hxy

/-- Helper for Lemma 15.23.6: dualizing a finite free presentation of `Dual R M` and transporting
the result along `Module.evalEquiv` and `LinearEquiv.piRing` yields the textbook exact row
`0 → M → R^n → R^m`. -/
private theorem dual_presentation_exact_in_coordinates
    {n m : ℕ}
    (a : (Fin m → R) →ₗ[R] (Fin n → R))
    (b : (Fin n → R) →ₗ[R] Dual R M)
    (hab : Function.Exact a b) (hb : Function.Surjective b)
    [IsReflexive R M] :
    let ι : M →ₗ[R] (Fin n → R) :=
      (LinearEquiv.piRing R R (Fin n) R).toLinearMap.comp
        ((LinearMap.lcomp R R b).comp (Module.evalEquiv R M).toLinearMap)
    let δ : (Fin n → R) →ₗ[R] (Fin m → R) :=
      (LinearEquiv.piRing R R (Fin m) R).toLinearMap.comp
        ((LinearMap.lcomp R R a).comp (LinearEquiv.piRing R R (Fin n) R).symm.toLinearMap)
    Function.Exact ι δ ∧ Injective ι := by
  let eM : M ≃ₗ[R] Dual R (Dual R M) := Module.evalEquiv R M
  let en : Dual R (Fin n → R) ≃ₗ[R] (Fin n → R) := LinearEquiv.piRing R R (Fin n) R
  let em : Dual R (Fin m → R) ≃ₗ[R] (Fin m → R) := LinearEquiv.piRing R R (Fin m) R
  let α : Dual R (Dual R M) →ₗ[R] Dual R (Fin n → R) := LinearMap.lcomp R R b
  let β : Dual R (Fin n → R) →ₗ[R] Dual R (Fin m → R) := LinearMap.lcomp R R a
  -- Route correction: instead of one large transported `simpa`, first solve exactness and
  -- injectivity on the raw dual row and only then move through the coordinate equivalences.
  obtain ⟨hExactRaw, hInjRaw⟩ :=
    dual_presentation_exact_raw (R := R) (M := M) a b hab hb
  constructor
  · -- Transport exactness from the raw dual row to the coordinate row `M → R^n → R^m`.
    exact dual_presentation_exact_transport (R := R) (M := M) a b hExactRaw
  · -- The same coordinate transport preserves injectivity of the left map.
    exact dual_presentation_injective_transport (R := R) (M := M) b hInjRaw

/-- Helper for Lemma 15.23.6: the canonical cokernel of the transported embedding `M → R^n` is
torsion free because exactness identifies it with the range of the next map into `R^m`. -/
private theorem dual_presentation_cokernel_isTorsionFree
    {n m : ℕ} (ι : M →ₗ[R] (Fin n → R)) (δ : (Fin n → R) →ₗ[R] (Fin m → R))
    (hExact : Function.Exact ι δ) :
    IsTorsionFree R ((Fin n → R) ⧸ LinearMap.range ι) := by
  have hker : LinearMap.ker δ = LinearMap.range ι := (LinearMap.exact_iff).mp hExact
  let eQ : ((Fin n → R) ⧸ LinearMap.range ι) ≃ₗ[R] ((Fin n → R) ⧸ LinearMap.ker δ) :=
    Submodule.quotEquivOfEq (LinearMap.range ι) (LinearMap.ker δ) hker.symm
  let e : ((Fin n → R) ⧸ LinearMap.range ι) ≃ₗ[R] LinearMap.range δ :=
    eQ.trans δ.quotKerEquivRange
  -- The image of `δ` is a submodule of a finite free module, hence torsion free.
  letI : IsTorsionFree R (LinearMap.range δ) := by
    infer_instance
  exact Function.Injective.moduleIsTorsionFree e e.injective fun r x ↦ by
    simp

-- Proof sketch: for the forward direction, choose a finite presentation of `Module.Dual R M`,
-- dualize it, and use reflexivity of `M` to identify the resulting kernel with `M`; the quotient
-- is canonically the cokernel of the chosen embedding into `R^n`, and it is torsion free over a
-- domain. For the reverse direction, finite free modules are reflexive, and Lemma `15.23.5`
-- applies to the canonical short exact sequence
-- `0 → M → R^n → (R^n / range f) → 0` once the cokernel is assumed torsion free.
/-- Lemma 15.23.6: a finite module over a Noetherian domain is reflexive if and only if it admits
an injective map into a finite free module `R^n` whose canonical cokernel is torsion free;
equivalently, it fits into a short exact sequence `0 → M → R^n → N → 0` with `N` torsion free. -/
@[stacks 0AV2]
theorem isReflexive_iff_exists_injective_to_fin_fun_with_torsionFree_cokernel :
    IsReflexive R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R),
        Injective f ∧ IsTorsionFree R ((Fin n → R) ⧸ LinearMap.range f) :=
  by
    constructor
    · intro hM
      letI : IsReflexive R M := hM
      letI : Module.FinitePresentation R (Dual R M) :=
        Module.finitePresentation_of_finite R (Dual R M)
      -- Present `Dual R M` by finite free modules exactly as in the source proof.
      rcases (Module.FinitePresentation.iff_exists_exact_free_sequence R (Dual R M)).mp
          inferInstance with
        ⟨n, m, a, b, hab, hb⟩
      let ι : M →ₗ[R] (Fin n → R) :=
        (LinearEquiv.piRing R R (Fin n) R).toLinearMap.comp
          ((LinearMap.lcomp R R b).comp (Module.evalEquiv R M).toLinearMap)
      let δ : (Fin n → R) →ₗ[R] (Fin m → R) :=
        (LinearEquiv.piRing R R (Fin m) R).toLinearMap.comp
          ((LinearMap.lcomp R R a).comp (LinearEquiv.piRing R R (Fin n) R).symm.toLinearMap)
      -- Route correction: the forward direction now follows the source proof through the raw dual
      -- presentation, then transports only the finished exact row to coordinates.
      have hCoord :
          Function.Exact ι δ ∧ Injective ι :=
        dual_presentation_exact_in_coordinates (R := R) (M := M) a b hab hb
      have hTorsionFree : IsTorsionFree R ((Fin n → R) ⧸ LinearMap.range ι) :=
        dual_presentation_cokernel_isTorsionFree (R := R) (M := M) ι δ hCoord.1
      exact ⟨n, ι, hCoord.2, hTorsionFree⟩
    · rintro ⟨n, f, hf, hTorsionFree⟩
      -- The converse is the direct application of Lemma `15.23.5` to the canonical cokernel.
      exact canonical_quotient_reflexive_implication (R := R) (M := M) f hf hTorsionFree

end
