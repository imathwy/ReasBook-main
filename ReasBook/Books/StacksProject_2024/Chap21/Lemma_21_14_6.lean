import Mathlib
import StacksProject_2024.Chap21.Lemma_21_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

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
  `higherDirectImageModule f ℱ q`, not from new local wrappers;
- primitive data:
  a morphism `f : X ⟶ Y`, a module sheaf `ℱ : SheafOfModules X.structureSheaf`, and vanishing
  hypotheses on `R^q f_* ℱ` or on its positive-degree cohomology on `Y`;
- derived API:
  the underlying-abelian-sheaf global cohomology object
  `AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H p)`.

Source/core/bridge triage:
- `source-facing`: the two cohomological comparison theorems below;
- `core/canonical`: `f.modulePushforward` and `higherDirectImageModule f ℱ q`;
- `bridge/view`: the underlying-abelian-sheaf realization of module cohomology already used in
  Chapter `21`.

The former local `moduleGlobalCohomology` abbreviation duplicated that derived view without
introducing new mathematics, so the refined file removes it and writes the canonical object
directly in the public statements. -/

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [Functor.Additive f.modulePushforward]
variable [HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{max u v})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{max u v})]

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every higher direct image
-- `R^q f_* ℱ` with `q > 0` vanishes, the `E₂`-page is concentrated on the `q = 0` row, so the
-- abutment identifies with the degree-`p` cohomology of `f_* ℱ` on the target site.
/-- Lemma 21.14.6 (1): if the higher direct images `R^q f_* \mathcal F` vanish for `q > 0`,
then the global degree-`p` cohomology of `\mathcal F` on `(\mathcal C, \mathcal O_\mathcal C)`
is canonically isomorphic to the global degree-`p` cohomology of `f_* \mathcal F` on
`(\mathcal D, \mathcal O_\mathcal D)`. -/
theorem moduleGlobalCohomology_iso_pushforward_of_higherDirectImageModule_isZero
    (ℱ : SheafOfModules X.structureSheaf)
    (hRq : ∀ q : ℕ, 0 < q → IsZero (higherDirectImageModule f ℱ q))
    (p : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H p))
      (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (f.modulePushforward.obj ℱ)).H p)) := sorry

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every positive-degree
-- cohomology group of every higher direct image `R^q f_* ℱ` vanishes on the target site, the
-- `E₂`-page is concentrated in the `p = 0` column, so the abutment in total degree `q`
-- identifies with the edge term `H^0(\mathcal D, R^q f_* \mathcal F)`.
/-- Lemma 21.14.6 (2): if `H^p(\mathcal D, R^q f_* \mathcal F) = 0` for all `q` and all `p > 0`,
then the global degree-`q` cohomology of `\mathcal F` on
`(\mathcal C, \mathcal O_\mathcal C)` is canonically isomorphic to the degree-`0` cohomology of
`R^q f_* \mathcal F` on `(\mathcal D, \mathcal O_\mathcal D)`. -/
theorem moduleGlobalCohomology_iso_degreeZero_higherDirectImageModule_of_acyclicity
    (ℱ : SheafOfModules X.structureSheaf)
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (higherDirectImageModule f ℱ q)).H p)))
    (q : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (((SheafOfModules.toSheaf X.structureSheaf).obj ℱ).H q))
      (AddCommGrpCat.of (((SheafOfModules.toSheaf Y.structureSheaf).obj
        (higherDirectImageModule f ℱ q)).H 0)) := sorry

end

end RingedSite.Hom
