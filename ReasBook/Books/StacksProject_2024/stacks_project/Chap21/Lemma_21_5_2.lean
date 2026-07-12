import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_12_4

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open SheafOfModules.RingedSite (ringSheaf unitModule)

noncomputable section

universe u

/- Domain-style sampling for Lemma 21.5.2:
- primary domain: the comparison between sheaf cohomology of the underlying abelian sheaf of an
  `𝒪`-module and the corresponding Ext groups in `Mod(𝒪)` on a ringed site;
- sampled owner declarations:
  `ringSheaf`,
  `unitModule`,
  `SheafOfModules.toSheaf`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- best owner abstraction:
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`, with the commutative ringed-site
  structure sheaf viewed through the chapter owner `ringSheaf`;
- primitive data:
  a commutative-ring-valued sheaf `𝒪 : Sheaf J CommRingCat` and a `𝒪`-module
  `ℱ : SheafOfModules (ringSheaf J 𝒪)`;
- derived API here:
  the degree-`1` specialization of that canonical comparison theorem.

Source/core/bridge triage:
- `source-facing`: the Stacks statement identifying `H¹(C, ℱ_ab)` with
  `Ext¹_{Mod(𝒪)}(𝒪, ℱ)`;
- `core/canonical`: `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- `bridge/view`: specializing the coefficient sheaf from a commutative-ring-valued sheaf to the
  canonical owners `ringSheaf J 𝒪` and `unitModule J 𝒪`, and specializing the degree to `1`.

The local `ringedSiteRingSheaf` alias and the wrapper theorem were duplicate wheel API, so the
refined file uses the canonical owner theorem directly. -/

/- Lemma 21.5.2 is the degree-`1` specialization of the canonical comparison theorem between the
global cohomology of the underlying abelian sheaf and module-valued Ext groups on a ringed site. -/
recall underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)] [HasExt (SheafOfModules (ringSheaf J 𝒪))]
variable (ℱ : SheafOfModules (ringSheaf J 𝒪))

/- Source-facing specialization: for a sheaf `ℱ` of `𝒪`-modules on a ringed site `(C, 𝒪)`, the
degree-`1` case identifies `H¹(C, ℱ_ab)` with `Ext¹_{Mod(𝒪)}(𝒪, ℱ)`. -/
#check (underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology ℱ 1 :
  IsIsomorphic
    (AddCommGrpCat.of (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H 1))
    (AddCommGrpCat.of (Ext (unitModule J 𝒪) ℱ 1)))

end
