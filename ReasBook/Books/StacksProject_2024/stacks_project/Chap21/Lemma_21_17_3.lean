import StacksProject_2024.Chap15.Lemma_15_59_2
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [hAbelian : Abelian (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [hHomology : CategoryWithHomology (ringedSiteModuleCategory J 𝒪)]
variable [hMonoidal : MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [hMonoidalPreadditive : MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [hTensorAdditive : (curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ ℱ : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj ℱ).Additive]
variable [hMapBifunctor : ∀ (F G : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor F G (curriedTensor (ringedSiteModuleCategory J 𝒪))]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

local instance ringedSiteModuleCategory_preadditive : Preadditive Mod :=
  hAbelian.toPreadditive

local instance ringedSiteModuleCategory_hasZeroObject : HasZeroObject Mod :=
  inferInstance

-- Domain-style sampling for Lemma 21.17.3:
-- - primary domain: quasi-isomorphism preservation under totalized tensoring by a fixed K-flat
--   complex of `𝒪`-modules on a ringed site;
-- - sampled owner declarations:
--   `CochainComplex.IsKFlat`,
--   `HomologicalComplex.tensorHom`,
--   `_root_.tensorHom_right_quasiIso_of_isKFlat`;
-- - best owner abstraction: the Chapter 15 owner theorem remains the canonical owner, and this
--   file only records its ringed-site specialization so the Stacks item keeps its local tag and
--   namespace;
-- - source/core/bridge triage:
--   `source-facing`: Lemma 21.17.3 for complexes of `𝒪`-modules on a ringed site;
--   `core/canonical`: `_root_.tensorHom_right_quasiIso_of_isKFlat`;
--   `bridge/view`: the exact source-facing specialization below.
omit [HasZeroObject Mod] in
@[stacks 06YP]
theorem tensorHom_right_quasiIso_of_isKFlat
    (K : CochainComplex Mod ℤ) (hK : K.IsKFlat)
    {L M : CochainComplex Mod ℤ} (f : L ⟶ M) (hf : QuasiIso f) :
    QuasiIso (tensorHom f (𝟙 K)) :=
  _root_.tensorHom_right_quasiIso_of_isKFlat K hK f hf

end SheafOfModules.RingedSite
