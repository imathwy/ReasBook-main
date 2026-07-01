import Mathlib
import stacks_project.Chap15.Definition_15_59_1
import stacks_project.Chap18.Lemma_18_19_2
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MonoidalCategory ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false
set_option quotPrecheck false

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

section

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]

variable (U : C)

variable [Preadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [HasZeroObject (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [MonoidalPreadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [(curriedTensor (ringedSiteModuleCategory (J.over U) (𝒪.over U))).Additive]
variable [∀ X : ringedSiteModuleCategory (J.over U) (𝒪.over U),
  ((curriedTensor (ringedSiteModuleCategory (J.over U) (𝒪.over U))).obj X).Additive]
variable [(SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))).Additive]

/- Domain-style sampling for Lemma 21.17.4:
- primary domain: K-flat cochain complexes of sheaves of modules on a ringed site and their
  restriction to a localized ringed site;
- sampled owner declarations:
  `ringSheaf`,
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `ringedSiteLocalizedExtensionByZero_exact_iff`;
- best owner abstraction: the K-flat predicate `K.IsKFlat` on cochain complexes in the canonical
  module category `ringedSiteModuleCategory`, together with the canonical localized restriction
  functor `SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))`;
- primitive data: the ambient and localized module categories, the object `U : C`, and the given
  K-flat complex `K`;
- derived API: the localized restriction complex obtained by applying the canonical restriction
  functor degreewise.

Source/core/bridge triage:
- `source-facing`: K-flatness of the localized restriction `K^•|_U`;
- `core/canonical`: `ringSheaf J 𝒪`, `ringedSiteModuleCategory`, and `CochainComplex.IsKFlat`;
- `bridge/view`: the restriction functor on complexes induced by
  `SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))`.

The old local alias `ringedSiteRingSheaf` duplicated the chapter owner `ringSheaf`, so the refined
file uses `ringSheaf` directly and keeps only this source-facing specialization. -/

local instance : Preadditive (SheafOfModules ((ringSheaf J 𝒪).over U)) := by
  change Preadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

local instance : HasZeroObject (SheafOfModules ((ringSheaf J 𝒪).over U)) := by
  change HasZeroObject (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

local instance : MonoidalCategory (SheafOfModules ((ringSheaf J 𝒪).over U)) := by
  change MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

local instance : MonoidalPreadditive (SheafOfModules ((ringSheaf J 𝒪).over U)) := by
  change MonoidalPreadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

local instance :
    (curriedTensor (SheafOfModules ((ringSheaf J 𝒪).over U))).Additive := by
  change (curriedTensor (ringedSiteModuleCategory (J.over U) (𝒪.over U))).Additive
  infer_instance

local instance (X : SheafOfModules ((ringSheaf J 𝒪).over U)) :
    ((curriedTensor (SheafOfModules ((ringSheaf J 𝒪).over U))).obj X).Additive := by
  change ((curriedTensor (ringedSiteModuleCategory (J.over U) (𝒪.over U))).obj X).Additive
  infer_instance

-- Proof sketch: let `𝒢^•` be an acyclic complex of `\mathcal O_U`-modules. Apply extension by zero
-- `j_{U!}` to `Tot(𝒢^• \otimes_{\mathcal O_U} K^•|_U)`. Lemma `18.19.3` makes `j_{U!}` exact, and
-- Lemma `18.27.9` identifies the image with `Tot(j_{U!} 𝒢^• \otimes_{\mathcal O} K^•)`, which is
-- acyclic by the K-flatness of `K^•`. Lemma `18.19.4` then reflects exactness back to the
-- localized site.
/-- Lemma 21.17.4: if `K^•` is a K-flat complex of `\mathcal O`-modules on a ringed site and
`U : C`, then the restricted complex `K^•|_U`, formalized by applying the canonical localized
restriction functor degreewise, is K-flat over `\mathcal O_U`. -/
theorem isKFlat_localizedRestriction
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) (hK : K.IsKFlat) :
    (((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))).mapHomologicalComplex
        (up ℤ)).obj K).IsKFlat := sorry

end

end SheafOfModules.RingedSite
