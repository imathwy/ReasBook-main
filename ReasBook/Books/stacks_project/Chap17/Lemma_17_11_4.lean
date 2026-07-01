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
  `SheafOfModules.free`,
  `CategoryTheory.ObjectProperty.prop_of_epi`;
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

As in Lemma 17.9.3, the public statements are best kept at the generic `SheafOfModules` owner
layer rather than as ringed-space-specific wrappers. Accordingly, the generic finite-type source
theorem is kept as the owner result below, and the finite-free source statement is retained only
as the source-facing specialization. -/

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

-- Proof sketch: locally choose a surjection from a finite free sheaf onto `𝒢`; the composite with
-- `θ` is still epi, so the finite-free case gives finite type for its kernel. The canonical exact
-- sequence comparing `kernel (ψη)` and `kernel θ` then shows that `kernel θ` is an image of a
-- finite type sheaf, hence is itself of finite type.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Lemma 17.11.4 (2): if `θ : 𝒢 \to ℱ` is surjective, `𝒢` is of finite type, and `ℱ` is of finite
presentation, then `kernel θ` is of finite type. -/
theorem isFiniteType_kernel_of_epi_of_finitePresentation
    {𝒢 ℱ : SheafOfModules R} (θ : 𝒢 ⟶ ℱ)
    [Epi θ] [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (kernel θ).IsFiniteType := sorry

-- Proof sketch: this is the finite-free specialization of the owner theorem above, stated with
-- the source's rank-`r` free sheaf surface.
/-- Lemma 17.11.4 (1): if `ℱ` is a finitely presented `\mathcal O`-module and
`ψ : \mathcal O^{\oplus r} \to ℱ` is surjective, then `kernel ψ` is of finite type. -/
theorem isFiniteType_kernel_of_epi_free_of_finitePresentation
    {ℱ : SheafOfModules R} [ℱ.IsFinitePresentation] (r : ℕ)
    (ψ : free (ULift.{u} (Fin r)) ⟶ ℱ) [Epi ψ] :
    (kernel ψ).IsFiniteType := sorry

end SheafOfModules
