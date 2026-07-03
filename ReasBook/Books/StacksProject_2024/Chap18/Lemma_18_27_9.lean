import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory
open Functor.OplaxMonoidal

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

private abbrev localizedStructureSheaf :=
  (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)

/- Domain-style sampling for Lemma 18.27.9:
- primary domain: localized extension by zero and restriction for sheaves of modules on a ringed
  site, together with the tensor comparison attached to `j_{U!}`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Functor.OplaxMonoidal.δ`;
- best owner abstraction: the canonical pullback/pushforward pair attached to the identity map of
  the localized structure sheaf `localizedStructureSheaf J 𝒪 U`, with localized modules surfaced
  through `ringedSiteModuleCategory (J.over U) (𝒪.over U)`;
- primitive data: the canonical `RingCat`-valued structure sheaf
  `((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)`, the identity morphism of its
  localization at `U`, and the ambient monoidal structures;
- derived API: the source-facing tensor comparison for `j_{U!}`, stated directly on the canonical
  oplax monoidal morphism and counit.

Source/core/bridge triage:
- `source-facing`: the comparison
  `j_{U!}(\mathcal G \otimes_{\mathcal O_U} \mathcal F|_U) ⟶
    j_{U!}\mathcal G ⊗_{\mathcal O} \mathcal F`;
- `core/canonical`: `((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)`,
  `SheafOfModules.pullback
    (𝟙 (localizedStructureSheaf J 𝒪 U))`,
  `SheafOfModules.pushforward
    (𝟙 (localizedStructureSheaf J 𝒪 U))`, and
  `SheafOfModules.pullbackPushforwardAdjunction`;
- `bridge/view`: the source-facing tensor-comparison statement below, specialized from these
  owners. -/

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]

local instance : MonoidalCategory (SheafOfModules (localizedStructureSheaf J 𝒪 U)) := by
  change MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

variable
  [(SheafOfModules.pushforward (𝟙 (localizedStructureSheaf J 𝒪 U))).LaxMonoidal]

local instance :
    (SheafOfModules.pullback (𝟙 (localizedStructureSheaf J 𝒪 U))).OplaxMonoidal :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (localizedStructureSheaf J 𝒪 U))).leftAdjointOplaxMonoidal

-- Proof sketch: apply Yoneda to the canonical comparison morphism. For every target
-- `\mathcal H`, the adjunction `j_{U!} ⊣ j_U^*`, the tensor-internal-Hom adjunction on the
-- ambient and localized module categories, and the compatibility of internal Hom with
-- restriction from Lemma `18.27.2` identify postcomposition with this comparison morphism with a
-- chain of Hom-set equivalences. Hence the comparison is invertible.
/-- Lemma 18.27.9: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`, an
`\mathcal O_U`-module `\mathcal G`, and an `\mathcal O`-module `\mathcal F`, the canonical
comparison morphism
`j_{U!}(\mathcal G \otimes_{\mathcal O_U} \mathcal F|_U) \to
j_{U!}\mathcal G \otimes_{\mathcal O} \mathcal F`,
namely the canonical map `δ j_{U!} ≫ (1 \otimes \epsilon_{\mathcal F})`, is an isomorphism. -/
theorem ringedSiteLocalizedExtensionByZero_tensorComparison_isIso
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsIso
      (δ (SheafOfModules.pullback (𝟙 (localizedStructureSheaf J 𝒪 U))) 𝒢
          ((SheafOfModules.pushforward (𝟙 (localizedStructureSheaf J 𝒪 U))).obj ℱ) ≫
        (𝟙 _ ⊗ₘ
          (SheafOfModules.pullbackPushforwardAdjunction
            (𝟙 (localizedStructureSheaf J 𝒪 U))).counit.app ℱ)) := sorry

end
