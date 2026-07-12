import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u v u'

/- Domain-style sampling for Lemma 17.11.4:
- primary domain: finitely presented sheaves of modules over a sheaf of rings on a site, and
  finite-type control of kernels of epimorphisms;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.free`;
- best owner abstraction:
  the ambient owner category `SheafOfModules R`, with finite type / finite presentation as the
  canonical owner predicates and `kernel` as derived abelian-category data, so the generic
  epimorphism theorem is the owner result and the finite-free case is a source-facing
  specialization;
- primitive data:
  the ambient sheaf of rings `R`, a finitely presented target sheaf, and either an epimorphism
  from a finite free sheaf or an epimorphism from a finite-type sheaf;
- derived API:
  the source-facing finite-type conclusions for the corresponding kernels.

Source/core/bridge triage:
- `source-facing`: the finite-free kernel statement in part `(1)` of Stacks Project Lemma
  `17.11.4`;
- `core/canonical`: the generic owner theorem for kernels of epimorphisms from finite-type
  sheaves into finitely presented sheaves, inside `SheafOfModules R`;
- `bridge/view`: ringed spaces are only the specialization `R = (RingedSpace.ringCatSheaf X)`.

The public API in this file is therefore the generic owner theorem together with its finite-free
specialization. -/

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- A finite free sheaf of modules is of finite type. -/
theorem free_isFiniteType_of_finite (I : Type u) [Finite I] :
    (free (R := R) I).IsFiniteType := by
  sorry

/-- Lemma 17.11.4 (2): if `θ : 𝒢 \to ℱ` is surjective, `𝒢` is of finite type, and `ℱ` is of
finite presentation, then `kernel θ` is of finite type. -/
theorem isFiniteType_kernel_of_epi_of_finitePresentation
    {𝒢 ℱ : SheafOfModules R} (θ : 𝒢 ⟶ ℱ)
    [Epi θ] [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (kernel θ).IsFiniteType := by
  sorry

/-- Lemma 17.11.4 (1): if `ℱ` is a finitely presented `\mathcal O`-module and
`ψ : \mathcal O^{\oplus r} \to ℱ` is surjective, then `kernel ψ` is of finite type. -/
theorem isFiniteType_kernel_of_epi_free_of_finitePresentation
    {ℱ : SheafOfModules R} [ℱ.IsFinitePresentation] (r : ℕ)
    (ψ : free (R := R) (ULift.{u} (Fin r)) ⟶ ℱ) [Epi ψ] :
    (kernel ψ).IsFiniteType := by
  letI : (free (R := R) (ULift.{u} (Fin r)) : SheafOfModules R).IsFiniteType :=
    free_isFiniteType_of_finite (R := R) (ULift.{u} (Fin r))
  simpa using isFiniteType_kernel_of_epi_of_finitePresentation (R := R) ψ

end SheafOfModules
