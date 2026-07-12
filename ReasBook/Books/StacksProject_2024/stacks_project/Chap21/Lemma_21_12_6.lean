import StacksProject_2024.Chap21.Lemma_21_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.12.6:
- primary domain: restriction maps on sections of presheaves and sheaves of modules on a site;
- sampled owner declarations:
  `SheafOfModules.forget`,
  `injective_as_presheaf_of_modules`;
- best owner abstraction: the source-facing owner is the sheaf-module restriction-surjectivity
  theorem below, with `injective_as_presheaf_of_modules` as the bridge to the underlying presheaf
  when proving it;
- primitive data: a site `(C, J)`, a sheaf of rings `R`, a monomorphism `a : U' ⟶ U`,
  an `R`-module sheaf `ℐ`, and the categorical injectivity hypothesis `Injective ℐ`;
- derived API: the site-level source-facing theorem below and the ringed-space specialization in
  Chapter 20.

Source/core/bridge triage:
- `source-facing`: surjectivity of restriction on sections along a monomorphism in the base;
- `core/canonical`: `SheafOfModules.forget`;
- `bridge/view`: `injective_as_presheaf_of_modules`.

This file is therefore the general owner for the site-level statement; downstream ringed-space
files should reuse it directly rather than keep parallel copies. -/

/-- Lemma 21.12.6: for a sheaf of rings `R` on a site, a monomorphism `a : U' ⟶ U`, and an
injective `R`-module sheaf `ℐ`, the restriction map on sections along `a` is surjective. -/
@[stacks 093X]
theorem injective_module_restriction_surjective_of_mono
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {U U' : C} (a : U' ⟶ U) [Mono a]
    (ℐ : SheafOfModules.{u} R) (hℐ : Injective ℐ) :
    Function.Surjective (((SheafOfModules.forget R).obj ℐ).map a.op) := sorry

end CategoryTheory
