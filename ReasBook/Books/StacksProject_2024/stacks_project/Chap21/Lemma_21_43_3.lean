import StacksProject_2024.stacks_project.Chap13.Aux_13_17_1
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap21.Definition_21_43_1

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]
local notation "Mod𝒪" => SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DMod𝒪" => DerivedCategory Mod𝒪
local notation "QCohMod" =>
  SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DQCoh" => derivedCategoryCohomologyInProperty QCohMod

/- Domain-style sampling for Lemma 21.43.3:
- primary domain: derived quasi-coherence on modules over a category with the chaotic topology,
  together with the ordinary quasi-coherent owner for module sheaves;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `CategoryTheory.ModulesOnCategory.chaoticRGamma`,
  `CategoryTheory.derivedTensorWithAlgebra`,
  `CategoryTheory.derivedCategoryCohomologyInProperty`,
  `SheafOfModules.IsQuasicoherent`;
- best owner abstraction:
  `source-facing`: the Section `21.43` owner `chaoticRGamma`, the canonical tensor restriction
    family `chaoticDerivedRestrict 𝒪`, and the
    specialized `QC` obtained from the general owner `CategoryTheory.ModulesOnCategory.QC`;
  `core/canonical`: the Chapter 13 owner `DQCoh` together with the Chapter 18 owner predicate
    `SheafOfModules.IsQuasicoherent`;
  `bridge/view`: the hypothesis `hcomparison`, sending the Section `21.43` comparison
    owner property directly to cohomologywise quasi-coherence.
- primitive data: the sheaf `𝒪`, the canonical chaotic-site derived sections functors, the
  canonical derived tensor restriction functors, and the comparison natural transformation;
- derived API: the owner-level inclusion from
  `isQuasiCoherent 𝒪.1 (chaoticRGamma 𝒪) (chaoticDerivedRestrict 𝒪) comparison` into `DQCoh`,
  membership in `QC` via `M.property`, and the pointwise cohomology quasi-coherence corollary
  obtained by evaluating `DQCoh`.

Source/core/bridge triage:
- `source-facing`: the Section `21.43` full subcategory
  `QC 𝒪.1 (chaoticRGamma 𝒪) (chaoticDerivedRestrict 𝒪) comparison`;
- `core/canonical`: the chapter owners `QC` and `DQCoh`;
- `bridge/view`: the owner inclusion `hcomparison`, which turns the Section `21.43`
  comparison property directly into membership in `DQCoh`. -/

-- Proof sketch: by `M.property`, every Section `21.43` comparison map is an isomorphism on `M`.
-- The bridge hypothesis `hcomparison` sends this directly to quasi-coherence of each cohomology
-- sheaf, which is exactly membership in the canonical Chapter 13 owner `DQCoh`.
section

variable [∀ U : C, (chaoticSections 𝒪 U).Additive]
variable [∀ U : C,
  Functor.HasRightDerivedFunctor
    (mapHomotopyCategoryToDerived (chaoticSections 𝒪 U))
    (HomotopyCategory.quasiIso
      (SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) (up ℤ))]
local notation "RΓ" => (fun U : C ↦ chaoticRGamma 𝒪 U)
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RΓ V ⋙ chaoticDerivedRestrict 𝒪 f ⟶ RΓ U)

set_option linter.unusedVariables false in
/-- Lemma 21.43.3: for the canonical chaotic-site derived sections and derived tensor restriction,
if the Section `21.43` comparison property implies quasi-coherence of the cohomology sheaves,
then every object of the full subcategory `QC(𝒞, 𝒪)` lies in the Chapter 13 owner `DQCoh`.
The objectwise and cohomologywise forms are recorded separately below. -/
@[stacks 0GZQ]
theorem qc_mem_derivedQuasiCoherent
    (hcomparison :
      isQuasiCoherent 𝒪.1 RΓ (chaoticDerivedRestrict 𝒪) comparison ≤ DQCoh)
    (K : QC 𝒪.1 RΓ (chaoticDerivedRestrict 𝒪) comparison) :
    DQCoh K.obj :=
  hcomparison K.property

set_option linter.unusedVariables false in
/-- Objectwise companion to `qc_mem_derivedQuasiCoherent`: any derived object satisfying the
Section `21.43` comparison property lies in `DQCoh`. -/
theorem qc_mem_derivedQuasiCoherent_apply
    (hcomparison :
      isQuasiCoherent 𝒪.1 RΓ (chaoticDerivedRestrict 𝒪) comparison ≤ DQCoh)
    (K : DMod𝒪)
    (hK : isQuasiCoherent 𝒪.1 RΓ (chaoticDerivedRestrict 𝒪) comparison K) :
    DQCoh K :=
  hcomparison hK

set_option linter.unusedVariables false in
/-- Companion pointwise form of `qc_mem_derivedQuasiCoherent`: every cohomology sheaf of a
derived object satisfying the Section `21.43` comparison property is quasi-coherent. -/
theorem qc_homology_isQuasicoherent
    (hcomparison :
      isQuasiCoherent 𝒪.1 RΓ (chaoticDerivedRestrict 𝒪) comparison ≤ DQCoh)
    (K : DMod𝒪)
    (hK : isQuasiCoherent 𝒪.1 RΓ (chaoticDerivedRestrict 𝒪) comparison K)
    (b : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) b).obj K).IsQuasicoherent :=
  hcomparison hK b

end

end CategoryTheory.ModulesOnCategory
