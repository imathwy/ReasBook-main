import StacksProject_2024.Chap21.Lemma_21_12_4
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open SheafOfModules.RingedSite (ringSheaf unitModule)

noncomputable section

universe u

/- Domain-style sampling for Lemma 21.5.1:
- primary domain: first cohomology of sheaves of modules on a ringed site, represented in this
  project by the canonical degree-`1` comparison between module `Ext` and global cohomology;
- sampled owner declarations:
  `ringSheaf`,
  `unitModule`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- best owner abstraction:
  the source-facing content is the canonical identification of
  `Ext (unitModule J 𝒪) ℱ 1` with the degree-`1` global cohomology of the underlying abelian
  sheaf of `ℱ`;
- primitive data:
  a commutative-ring-valued sheaf `𝒪 : Sheaf J CommRingCat` and an `𝒪`-module
  `ℱ : SheafOfModules (ringSheaf J 𝒪)`;
- derived API:
  the source-facing degree-`1` comparison below, reusing the Chapter 21 global cohomology owner.

Source/core/bridge triage:
- `source-facing`: the canonical bijection from `Ext¹_{Mod(𝒪)}(𝒪, ℱ)` to `H¹(C, ℱ)`;
- `core/canonical`: `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- `bridge/view`: its degree-`1` specialization, read with the source-facing `ringSheaf` and
  `unitModule` owners.
-/

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasExt (SheafOfModules (ringSheaf J 𝒪))]
variable (ℱ : SheafOfModules (ringSheaf J 𝒪))

/-- Lemma 21.5.1: the canonical degree-`1` comparison identifies
`Ext¹_{Mod(𝒪)}(𝒪, ℱ)` with the global cohomology group `H¹(C, ℱ)` of the underlying abelian
sheaf. -/
@[stacks 03F1]
theorem moduleExtToH1_bijective :
    IsIsomorphic
      (AddCommGrpCat.of (Ext (unitModule J 𝒪) ℱ 1))
      (AddCommGrpCat.of (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H 1)) := sorry

end
