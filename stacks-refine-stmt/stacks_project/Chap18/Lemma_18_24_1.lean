import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.24.1:
- primary domain: finite type and finite presentation for sheaves of modules over a sheaf of
  rings on a site, with ringed sites as the source-facing specialization;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.Presentation`,
  `SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`;
- best owner abstraction:
  the generic owner category `SheafOfModules 𝒪`, with finite type / finite presentation as the
  canonical owner predicates and `cokernel` as derived abelian-category data;
- primitive data:
  a morphism `φ : 𝒢 ⟶ ℱ` together with `[𝒢.IsFiniteType]` and `[ℱ.IsFinitePresentation]`;
- derived API:
  the finite-presentation conclusion for `cokernel φ`.

Source/core/bridge triage:
- `source-facing`: the ringed-site statement of Stacks Project Lemma 18.24.1;
- `core/canonical`: the generic owner theorem
  `SheafOfModules.isFinitePresentation_cokernel`;
- `bridge/view`: ringed-space and ringed-site specializations obtained by instantiating the
  ambient sheaf of rings.

No upstream theorem with this exact interface is available in mathlib or earlier project files, so
this file keeps the generic owner theorem instead of introducing a ringed-site-local wrapper.
-/

-- Proof sketch: view `cokernel φ` as the quotient of `ℱ` by the image of `φ`. The image of a
-- finite type sheaf is finite type, and the local definition of finite presentation is stable
-- under quotienting a finitely presented sheaf by a finite type submodule.
/-- Lemma 18.24.1: for a morphism `φ : 𝒢 ⟶ ℱ` of `\mathcal O`-modules on a ringed site, if `𝒢`
is of finite type and `ℱ` is finitely presented, then the cokernel of `φ` is finitely
presented. -/
theorem isFinitePresentation_cokernel
    {𝒢 ℱ : SheafOfModules 𝒪} (φ : 𝒢 ⟶ ℱ) [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (cokernel φ).IsFinitePresentation := sorry

end SheafOfModules
