import Mathlib
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v

namespace RingedSite.Hom

/-- The direct-image functor on sheaves of modules attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The `i`-th higher direct image of a sheaf of modules along a morphism of ringed sites. -/
abbrev higherDirectImageModule {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [Functor.Additive f.modulePushforward]
    [HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
    (ℱ : SheafOfModules X.structureSheaf) (i : ℕ) :
    SheafOfModules Y.structureSheaf :=
  (f.modulePushforward.rightDerived i).obj ℱ

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasInjectiveResolutions (SheafOfModules X.structureSheaf)]
variable [Functor.Additive f.modulePushforward]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt.{max u v} (Sheaf X.siteTopology AddCommGrpCat.{max u v})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]

/- Domain-style sampling for Lemma 21.7.4:
- primary domain: higher direct images of sheaves of modules on a morphism of ringed sites and
  the comparison with objectwise cohomology of the underlying abelian sheaf;
- sampled owner declarations:
  `RingedSite.Hom.modulePushforward`,
  `RingedSite.Hom.higherDirectImageModule`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: the source-facing higher direct image owner
  `higherDirectImageModule f ℱ i`, built from the bundled morphism `f : RingedSite.Hom X Y`;
- primitive data: the bundled morphism `f`, an `\mathcal O_X`-module
  `ℱ : SheafOfModules X.structureSheaf`, and the degree `i`;
- derived API: the underlying abelian sheaf functor `SheafOfModules.toSheaf`, the right derived
  direct image owner `higherDirectImageModule f ℱ i`, and the sheafification of the objectwise
  cohomology presheaf on `Y`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement identifying the underlying abelian sheaf of
  `R^i f_* \mathcal F` with the sheaf associated to `V ↦ H^i(f^{-1}(V), \mathcal F)`;
- `core/canonical`: the chapter owners `RingedSite.Hom.modulePushforward` and
  `RingedSite.Hom.higherDirectImageModule`;
- `bridge/view`: forgetting module structure via `SheafOfModules.toSheaf` and expressing the
  target as a sheafification of the presheaf `f.base.op ⋙ ... .cohomologyPresheaf i`.

This theorem depends only on the owner-level ringed-site data, not on a particular presentation by
commutative ringed sites. The former local aliases for the source and target commutative ringed
sites were presentation-only duplicate scaffolding and are removed.
-/

-- Proof sketch: compute `R^i f_* ℱ` from an injective resolution of `ℱ` via the right-derived
-- functor of `f.modulePushforward`. After forgetting the module
-- structure, the resulting degree-`i` cohomology sheaf is the sheafification of the presheaf of
-- sectionwise cohomology of the same pushed-forward complex, and evaluating the direct image on
-- `V` identifies that presheaf with `V ↦ H^i(f^{-1}(V), ℱ)`.
/-- Lemma 21.7.4, owner form: for a morphism of ringed sites `f : X ⟶ Y`, the underlying abelian
sheaf of `R^i f_* \mathcal F`, formalized here as `higherDirectImageModule f ℱ i`, is
canonically isomorphic to the sheaf associated to the presheaf
`V ↦ H^i(f^{-1}(V), \mathcal F)`. In the Stacks commutative setting, this applies to ringed sites
arising from `RingedSite.ofCommRingSheaf`. -/
theorem higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology
    (ℱ : SheafOfModules X.structureSheaf) (i : ℕ) :
    IsIsomorphic
      ((SheafOfModules.toSheaf Y.structureSheaf).obj (higherDirectImageModule f ℱ i))
      ((presheafToSheaf Y.siteTopology AddCommGrpCat.{max u v}).obj
        (f.base.op ⋙ CategoryTheory.Sheaf.cohomologyPresheaf
          (J := X.siteTopology) ((SheafOfModules.toSheaf X.structureSheaf).obj ℱ) i)) := sorry

end RingedSite.Hom
