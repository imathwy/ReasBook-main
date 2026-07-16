import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_12
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_4
import StacksProject_2024.stacks_project.Chap21.«21_3_0_2»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_12_4
import StacksProject_2024.stacks_project.Chap21.Lemma_21_14_5_Leray_spectral_sequence
import StacksProject_2024.stacks_project.Chap21.Lemma_21_7_4_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.14.6:
- primary domain: the Leray spectral sequence for global cohomology of sheaves of modules on a
  morphism of ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.modulePushforward`,
  `RingedSite.Hom.higherDirectImageModule`,
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`,
  `RingedSite.Hom.exists_leraySpectralSequence`;
- best owner abstraction:
  the source-facing statements here are the two Leray degeneration consequences, while the
  owner-level module direct-image data should come from `f.modulePushforward` and
  `R^{q}_[f](ℱ)`, not from new local wrappers;
- primitive data:
  a morphism `f : X ⟶ Y`, a module sheaf `ℱ : ModuleCat X`, and vanishing hypotheses on
  `R^{q}_[f](ℱ)` or on its positive-degree cohomology on `Y`;
- derived API:
  the underlying-abelian-sheaf global cohomology object
  `AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H p)`.

Source/core/bridge triage:
- `source-facing`: the two cohomological comparison theorems below;
- `core/canonical`: `f.modulePushforward`, `R^{q}_[f](ℱ)`, and
  `underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology`;
- `bridge/view`: the underlying-abelian-sheaf realization of module cohomology already used in
  Chapter `21`.

The former local `moduleGlobalCohomology` abbreviation duplicated that derived view without
introducing new mathematics. The statement surface here therefore keeps the Leray degeneration
consequences while writing their cohomology groups directly through the existing sheaf-cohomology
owner. -/

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [Functor.Additive f.modulePushforward]
variable [HasInjectiveResolutions (ModuleCat X)]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{max u v})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{max u v})]

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every higher direct image
-- `R^{q}_[f](ℱ)` with `q > 0` vanishes, the `E₂`-page is concentrated on the `q = 0` row, so the
-- abutment identifies with the degree-`p` cohomology of `f.modulePushforward.obj ℱ` on `Y`.
/-- Lemma 21.14.6 (1): if the higher direct images `R^q f_* \mathcal F` vanish for `q > 0`,
then the global degree-`p` cohomology of `\mathcal F` on `(\mathcal C, \mathcal O_\mathcal C)`
is canonically isomorphic to the global degree-`p` cohomology of `f_* \mathcal F` on
`(\mathcal D, \mathcal O_\mathcal D)`. -/
@[stacks 0733]
theorem moduleGlobalCohomology_iso_pushforward_of_higherDirectImageModule_isZero
    (ℱ : ModuleCat X)
    (hRq : ∀ q : ℕ, 0 < q → IsZero (R^{q}_[f](ℱ)))
    (p : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H p))
      (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (f.modulePushforward.obj ℱ)).H p)) := sorry

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every positive-degree
-- cohomology group of every higher direct image `R^{q}_[f](ℱ)` vanishes on `Y`, the `E₂`-page is
-- concentrated in the `p = 0` column, so the abutment in total degree `q` identifies with the
-- degree-`0` cohomology of `R^{q}_[f](ℱ)` on `Y`.
/-- Lemma 21.14.6 (2): if `H^p(\mathcal D, R^q f_* \mathcal F) = 0` for all `q` and all `p > 0`,
then the global degree-`q` cohomology of `\mathcal F` on
`(\mathcal C, \mathcal O_\mathcal C)` is canonically isomorphic to the degree-`0` cohomology of
`R^q f_* \mathcal F` on `(\mathcal D, \mathcal O_\mathcal D)`. -/
@[stacks 0733]
theorem moduleGlobalCohomology_iso_degreeZero_higherDirectImageModule_of_acyclicity
    (ℱ : ModuleCat X)
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (R^{q}_[f](ℱ))).H p)))
    (q : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H q))
      (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (R^{q}_[f](ℱ))).H 0)) := sorry

end

end RingedSite.Hom
