import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap07.Lemma_7_30_5
import stacks_proof.stacks_project.Chap18.Definition_18_19_1
import stacks_proof.stacks_project.Chap18.Definition_18_21_2

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
- primary domain: representable localization of a ringed topos, expressed by comparing the
  category-of-elements localization at `h[U]^#[J]` with the slice-site localization over `U`;
- sampled owner declarations:
  `sheafCategoryOfElementsEquivOver`,
  `GrothendieckTopology.representableLocalizationComparison`,
  `GrothendieckTopology.representableLocalizationComparison_isEquivalence`,
  `GrothendieckTopology.representableLocalizationComparison_forget`,
  `RingedSite.representableLocalizationStructureMap`,
  `SheafOfModules.overPushforwardOverAdj`;
- best owner abstraction: this file is a `bridge/view` file. The general localization-at-a-sheaf
  presentation and the representable slice localization are compared through the common slice topos
  `Sh(C, J) / h[U]^#[J]`, via `sheafCategoryOfElementsEquivOver h[U]^#[J]` and the equivalence
  carried by `J.representableLocalizationComparison U` together with
  `J.representableLocalizationComparison_isEquivalence U`; on the ringed side, the source-facing
  specialization `RingedSite.representableLocalizationStructureMap 𝒪 U` fixes the non-inferable
  structure-sheaf parameter of the generic owner `SheafOfModules.pushforwardOver`;
- primitive data: the site `(C, J)`, the ring sheaf `𝒪`, and the object `U : C`;
- derived API: the restricted structure sheaf `𝒪.over U`, the canonical representable structure
  map `RingedSite.representableLocalizationStructureMap 𝒪 U`, and the module adjunction
  `SheafOfModules.overPushforwardOverAdj U`.

Source/core/bridge triage:
- `source-facing`: the textbook identification of the localization at `h[U]^#[J]` with the
  representable localization at `U`;
- `core/canonical`: `sheafCategoryOfElementsEquivOver h[U]^#[J]`,
  `J.representableLocalizationComparison U`,
  `J.representableLocalizationComparison_isEquivalence U`, `SheafOfModules.pushforwardOver`, and
  `SheafOfModules.overPushforwardOverAdj`;
- `bridge/view`: `J.representableLocalizationComparison_forget U` and
  `RingedSite.representableLocalizationStructureMap 𝒪 U`, which identify the lower shriek and the
  ringed structure map of the representable localization with the slice-site owners.
-/

/- Lemma 18.21.3: in the representable case `ℱ = h[U]^#[J]`, the general localization-at-a-sheaf
presentation from Definition `18.21.2` and the slice-site localization from Definition `18.19.1`
are compared through the common slice topos `Sh(C, J) / h[U]^#[J]`. The category-of-elements side
is owned by the canonical equivalence below. -/
#check sheafCategoryOfElementsEquivOver h[U]^#[J]

/- The representable-localization side is the Chapter 7 comparison functor from sheaves on
`(C / U, J.over U)` to sheaves over `h[U]^#[J]`. -/
#check (J.representableLocalizationComparison U)

/- Lemma `7.25.4` records that this comparison functor is an equivalence, so the representable
side matches the equivalence-level owner used on the general-localization side. -/
#check (J.representableLocalizationComparison_isEquivalence U)

/- On underlying topoi, Lemma `7.30.5` records that this comparison forgets to the canonical lower
shriek `j_{U!}`. -/
#check (J.representableLocalizationComparison_forget U)

/- On the ringed side, the localized structure sheaf is the canonical restriction `𝒪.over U` on
the slice site. -/
#check (𝒪.over U)

/- The structure-map part `j_U^♯` is the canonical representable localization map on sheaves of
rings, specialized to the ambient structure sheaf `𝒪`. -/
#check (RingedSite.representableLocalizationStructureMap 𝒪 U)

/- Companion recall: the module-level adjunction encoding the representable ringed localization is
the canonical owner `SheafOfModules.overPushforwardOverAdj U`. -/
recall SheafOfModules.overPushforwardOverAdj

end
