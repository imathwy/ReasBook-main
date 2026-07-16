import StacksProject_2024.stacks_project.Chap21.SheafOfModulesForgetPreservesInjectiveObjects

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 21.12.1:
- primary domain: injective sheaves of modules on a ringed site and the underlying presheaf of
  modules;
- sampled owner declarations:
  `Functor.PreservesInjectiveObjects`,
  `Functor.injective_obj_of_injective`,
  `sheafOfModulesForgetPreservesInjectiveObjects`;
- best owner abstraction: the canonical Chapter 21 owner is the shared support instance
  `sheafOfModulesForgetPreservesInjectiveObjects` for the forgetful functor
  `SheafOfModules.forget 𝒪`, factored out so this file stays a thin source-facing bridge;
- primitive data: only the ring-valued sheaf `𝒪`;
- derived API: the source-facing objectwise injectivity statement below.

Source/core/bridge triage:
- `source-facing`: the textbook claim that an injective sheaf of `𝒪`-modules is injective as an
  object of `PMod(𝒪.obj)`;
- `core/canonical`: `Functor.PreservesInjectiveObjects` for `SheafOfModules.forget 𝒪`, supplied
  by the support instance `sheafOfModulesForgetPreservesInjectiveObjects`;
- `bridge/view`: the objectwise corollary `injective_as_presheaf_of_modules` below.
-/

/-- Lemma 21.12.1: an injective sheaf of modules on a ringed site is injective as an object of
`PMod(𝒪.obj)`, i.e. as a presheaf of `𝒪`-modules after forgetting the sheaf condition. -/
@[stacks 03FB]
theorem injective_as_presheaf_of_modules
    (F : SheafOfModules.{u} 𝒪) (hF : Injective F) :
    Injective ((SheafOfModules.forget 𝒪).obj F) := by
  simpa using (SheafOfModules.forget 𝒪).injective_obj_of_injective hF

end CategoryTheory
