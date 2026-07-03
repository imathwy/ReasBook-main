import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_30_5
import StacksProject_2024.Chap18.Definition_18_19_1
import StacksProject_2024.Chap18.Definition_18_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open scoped SheafifiedRepresentable

universe w

noncomputable section

section

variable {C : Type w} [Category.{w} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type w)]
variable (𝒪 : Sheaf J RingCat.{w}) (U : C)

/- Domain-style sampling for Lemma 18.21.3:
- primary domain: representable localization of a ringed topos, expressed through the bridge from
  the general localization-at-a-sheaf construction to the slice-site localization at `U`;
- sampled owner declarations:
  `RingedSite.localizationAtSheaf`,
  `RingedSite.localizationAtSheafStructureMap`,
  `RingedSite.localization`,
  `SheafOfModules.pushforwardOver`,
  `GrothendieckTopology.representableLocalizationComparison_forget`,
  `SheafOfModules.overPushforwardOverAdj`;
- best owner abstraction: the source-facing owner is
  `RingedSite.localizationAtSheaf`, with bridge data carried by
  `RingedSite.localizationAtSheafStructureMap` and the comparison
  `J.representableLocalizationComparison_forget U`;
- primitive data: the site `(C, J)`, the ring sheaf `𝒪`, and the object `U : C`;
- derived API: the representable localized structure sheaf `𝒪.over U`, the canonical structure
  morphism `SheafOfModules.pushforwardOver U`, and the module adjunction
  `SheafOfModules.overPushforwardOverAdj U`.

Source/core/bridge triage:
- `source-facing`: `RingedSite.localizationAtSheaf` and
  `RingedSite.localizationAtSheafStructureMap`, specialized here to the representable case;
- `core/canonical`: `RingedSite.localization`, `SheafOfModules.pushforwardOver`, and
  `SheafOfModules.overPushforwardOverAdj`;
- `bridge/view`: `J.representableLocalizationComparison_forget U`, identifying the underlying
  localization functor at `h_U^#` with the representable localization at `U`.
-/

/- Lemma 18.21.3: for the representable sheaf `ℱ = h[U]^#[J]`, the general localization-at-a-sheaf
owner is definitionally the slice-site localization at `U`. -/
theorem localizationAtSheaf_sheafifiedRepresentable_eq_localization :
    RingedSite.localizationAtSheaf 𝒪 h[U]^#[J] =
      RingedSite.localization { carrier := C, siteTopology := J, structureSheaf := 𝒪 } U :=
  by
    sorry

/- Companion recall: on underlying topoi, the equivalence of Lemma `7.25.4` identifies the
localization morphism `j_U` with the slice forgetful functor over `h[U]^#[J]`, as recorded in
Lemma `7.30.5`. -/
#check (J.representableLocalizationComparison_forget U)

/- Companion recall: the module-level adjunction encoding the representable ringed localization is
the canonical owner `SheafOfModules.overPushforwardOverAdj U`. -/
recall SheafOfModules.overPushforwardOverAdj

end
