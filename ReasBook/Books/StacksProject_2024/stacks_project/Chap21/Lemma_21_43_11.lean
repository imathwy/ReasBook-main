import StacksProject_2024.Chap13.Aux_13_17_1
import StacksProject_2024.Chap21.Definition_21_43_1

open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped DerivedCategoryWithCohomologyIn
open Opposite
open ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{u} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

local notation "Mod𝒪" => ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪
local notation "DMod𝒪" => DerivedCategory Mod𝒪
local notation "H" => DerivedCategory.homologyFunctor Mod𝒪
local notation "QCohMod" =>
  SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DQCoh" => derivedCategoryCohomologyInProperty QCohMod

/- Domain-style sampling for Lemma 21.43.11:
- primary domain: derived categories of module sheaves on the chaotic site and the flat
  comparison between the Section `21.43` base-change condition and cohomologywise
  quasi-coherence;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `CategoryTheory.ModulesOnCategory.chaoticRGamma`,
  `CategoryTheory.ModulesOnCategory.chaoticDerivedRestrict`,
  `SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso`,
  `SheafOfModules.quasicoherentModuleProperty_isWeakSerreSubcategory`;
- best owner abstraction:
  `source-facing`: this lemma is the flat chaotic-site statement equating the Section `21.43`
    comparison property with the condition that every cohomology sheaf is quasi-coherent;
  `core/canonical`: `isQuasiCoherent` from Definition `21.43.1`, together with the direct object
    property saying every cohomology sheaf is quasi-coherent;
  `bridge/view`: the flat comparison hypothesis `hcomparison`, which identifies the derived
    comparison map with the sectionwise tensor map from Lemma `18.24.3` under the source flatness
    assumption;
- primitive data: the sheaf `𝒪`, the sections functors, the derived restriction functors, the
  flat restriction maps, and the comparison natural transformation;
- derived API: the Section `21.43` owner property, the Chapter `18.24.3` tensor criterion, and the
  degreewise quasi-coherent conclusion, so the theorem surface should reuse the existing owners and
  expose the two inclusion directions as companion theorems rather than private wrapper
  definitions. -/

-- Proof sketch: apply Lemma `18.24.3` to each cohomology sheaf and use the flat comparison
-- hypothesis to identify the source Section `21.43` comparison maps with the sectionwise tensor
-- comparison maps in both directions.
section FlatComparisonCriterion

variable [∀ U : C, (chaoticSections 𝒪 U).Additive]
variable [∀ U : C,
  Functor.HasRightDerivedFunctor
    (mapHomotopyCategoryToDerived (chaoticSections 𝒪 U))
    (HomotopyCategory.quasiIso
      (SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) (up ℤ))]
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      chaoticRGamma 𝒪 V ⋙ chaoticDerivedRestrict 𝒪 f ⟶ chaoticRGamma 𝒪 U)

/-- Helper for Lemma 21.43.11: the flat comparison criterion identifies the Section `21.43`
comparison-isomorphism property for a derived object with cohomologywise quasi-coherence. -/
def SatisfiesFlatComparisonCriterion : Prop :=
    ∀ K : DMod𝒪,
      (∀ ⦃U V : C⦄ (f : U ⟶ V),
        RingHom.Flat ((𝒪.1.map f.op).hom) →
          IsIso ((comparison f).app K)) ↔
        ∀ n : ℤ, QCohMod ((H n).obj K)

/-- Helper for Lemma 21.43.11: under the flat comparison criterion, the Section `21.43` owner
property implies cohomologywise quasi-coherence. -/
theorem qc_le_derivedQuasiCoherent_of_flatComparisonCriterion
    (hcomparison : SatisfiesFlatComparisonCriterion 𝒪 comparison)
    : isQuasiCoherent 𝒪.1 (chaoticRGamma 𝒪) (chaoticDerivedRestrict 𝒪) comparison ≤ DQCoh := by
  intro K hK
  -- Evaluate the criterion on `K`; the Section `21.43` property supplies the required
  -- comparison isomorphisms for every flat restriction map.
  exact (hcomparison K).1 (fun {U V} f _ ↦ hK (U := U) (V := V) f)

/-- Helper for Lemma 21.43.11: under the flat comparison criterion, cohomologywise
quasi-coherence implies the Section `21.43` owner property. -/
theorem derivedQuasiCoherent_le_qc_of_flatComparisonCriterion
    (hflat : ∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.1.map f.op).hom))
    (hcomparison : SatisfiesFlatComparisonCriterion 𝒪 comparison)
    : DQCoh ≤
        isQuasiCoherent 𝒪.1 (chaoticRGamma 𝒪) (chaoticDerivedRestrict 𝒪) comparison := by
  intro K hK U V f
  -- Apply the reverse direction of the criterion to `K`, then specialize to the chosen arrow.
  exact ((hcomparison K).2 hK) f (hflat f)

/-- Lemma 21.43.11: if every restriction map `𝒪(V) ⟶ 𝒪(U)` on the chaotic site is flat, and the
canonical chaotic-site comparison for `chaoticDerivedRestrict 𝒪` satisfies the resulting flat
cohomological tensor criterion, then the Section `21.43` object property
`isQuasiCoherent 𝒪.1 (chaoticRGamma 𝒪) ...` agrees with the canonical Chapter `13` owner
`derivedCategoryCohomologyInProperty` for quasi-coherent cohomology. -/
@[stacks 0GZR]
theorem qc_eq_derivedQuasiCoherent_of_flatComparisonCriterion
    (hflat : ∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.1.map f.op).hom))
    (hcomparison : SatisfiesFlatComparisonCriterion 𝒪 comparison) :
    isQuasiCoherent 𝒪.1 (chaoticRGamma 𝒪) (chaoticDerivedRestrict 𝒪) comparison = DQCoh := by
  exact le_antisymm
    (qc_le_derivedQuasiCoherent_of_flatComparisonCriterion 𝒪 comparison hcomparison)
    (derivedQuasiCoherent_le_qc_of_flatComparisonCriterion 𝒪 comparison hflat hcomparison)

end FlatComparisonCriterion

end CategoryTheory.ModulesOnCategory
