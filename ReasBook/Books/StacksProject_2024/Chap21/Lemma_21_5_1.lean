import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap21.Lemma_21_12_4

open CategoryTheory

noncomputable section

universe u

/- Domain-style sampling for Lemma 21.5.1:
- primary domain: the comparison between sheaf cohomology of the underlying abelian sheaf of an
  `\mathcal O`-module and the corresponding Ext groups in `\mathrm{Mod}(\mathcal O)` on a ringed
  site;
- sampled owner declarations:
  `ringSheaf`,
  `SheafOfModules.unit`,
  `SheafOfModules.unitHomEquiv`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- best owner abstraction:
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`, with the commutative ringed-site
  structure sheaf viewed through the chapter owner `ringSheaf`;
- primitive data:
  a commutative-ring-valued sheaf `𝒪 : Sheaf J CommRingCat` and an `\mathcal O`-module
  `ℱ : SheafOfModules (ringSheaf J 𝒪)`;
- derived API here:
  the degree-`1` specialization of that canonical comparison theorem.

Source/core/bridge triage:
- `source-facing`: the Stacks statement identifying `H¹(\mathcal C, \mathcal F_{ab})` with
  `Ext¹_{\mathrm{Mod}(\mathcal O)}(\mathcal O, \mathcal F)`;
- `core/canonical`: `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- `bridge/view`: specializing the coefficient sheaf from a `RingCat`-valued sheaf to the canonical
  owner `ringSheaf J 𝒪` attached to a commutative ringed site, and specializing the degree to `1`.

The local `ringedSiteRingSheaf` alias and the wrapper theorem were duplicate wheel API, so the
refined file uses the canonical owner theorem directly. -/

/- Lemma 21.5.1 is the degree-`1` specialization of the canonical comparison theorem between the
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

/- Source-facing specialization: for a sheaf `ℱ` of `\mathcal O`-modules on a ringed site
`(\mathcal C, \mathcal O)`, the degree-`1` case identifies `H¹(\mathcal C, \mathcal F_{ab})`
with `Ext¹_{\mathrm{Mod}(\mathcal O)}(\mathcal O, \mathcal F)`. -/
#check (underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology ℱ 1 :
  AddCommGrpCat.of (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H 1) =
    (Abelian.extFunctorObj (SheafOfModules.unit (ringSheaf J 𝒪)) 1).obj ℱ)

end
