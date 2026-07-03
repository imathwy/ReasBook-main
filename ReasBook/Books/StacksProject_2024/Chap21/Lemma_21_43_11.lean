import Mathlib
import StacksProject_2024.Chap13.Lemma_13_17_1
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap18.Lemma_18_24_3
import StacksProject_2024.Chap21.Definition_21_43_1

open CategoryTheory
open Opposite
open ComplexShape

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, HasWeakSheafify ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective AddCommGrpCat]

local notation "Mod𝒪" => SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DMod𝒪" => DerivedCategory Mod𝒪
local notation "Qis𝒪" => HomotopyCategory.quasiIso Mod𝒪 (up ℤ)
local notation "QCoh" =>
  SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DQCoh" => derivedCategoryCohomologyInProperty QCoh

private noncomputable abbrev chaoticRGamma
    [hAdditive : ∀ U : C,
      (SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U) :
        Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U))).Additive]
    [hDerived : ∀ U : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived
          (SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U) :
            Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U))))
        Qis𝒪] :
    ∀ U : C, DMod𝒪 ⥤ DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
  fun U ↦
    let F : Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U)) :=
      SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U)
    let _ : F.Additive := by simpa [F] using hAdditive U
    let _ : Functor.HasRightDerivedFunctor (mapHomotopyCategoryToDerived F) Qis𝒪 := by
      simpa [F] using hDerived U
    Functor.totalRightDerived
      (mapHomotopyCategoryToDerived F)
      (DerivedCategory.Qh : HomotopyCategory Mod𝒪 (up ℤ) ⥤ DerivedCategory Mod𝒪)
      Qis𝒪

private noncomputable abbrev chaoticDerivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
  fun {U V} f ↦
    let _ : Algebra (𝒪.1.obj (op V)) (𝒪.1.obj (op U)) :=
      RingHom.toAlgebra ((𝒪.1.map f.op).hom)
    derivedTensorWithAlgebra _ _

/- Domain-style sampling for Lemma 21.43.11:
- primary domain: derived categories of module sheaves on the chaotic site and the comparison
  between the Section `21.43` base-change condition and cohomologywise quasi-coherence;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso`,
  `CategoryTheory.derivedCategoryCohomologyInProperty`;
- best owner abstraction:
  `source-facing`: this lemma is the bridge equating the Section `21.43` comparison property with
    the condition that every cohomology sheaf is quasi-coherent;
  `core/canonical`: `isQuasiCoherent` from Definition `21.43.1`, together with the Chapter 13
    cohomology-in-an-object-property owner specialized to `SheafOfModules.IsQuasicoherent`;
  `bridge/view`: the hypothesis `hcomparison`, which identifies the derived comparison map with
    the sectionwise tensor map from Lemma `18.24.3`;
- primitive data: the sheaf `𝒪`, the sections functors, the derived restriction functors, and the
  comparison natural transformation;
- derived API: the Section `21.43` owner property and the degreewise quasi-coherent conclusion, so
  the theorem surface should reuse the existing owners and inline the canonical
  evaluation/derived-functor constructions instead of naming one-off wrapper declarations. -/

-- Proof sketch: for each arrow `U \to V`, the comparison hypothesis identifies the derived
-- base-change isomorphism for `K` with the tensor-sections criterion of the cohomology sheaves
-- `H^n(K)`. Then the chaotic-topology characterization of quasi-coherence turns that objectwise
-- tensor criterion into quasi-coherence of every cohomology sheaf, and conversely.
/-- Lemma 21.43.11: for a category `\mathcal C` with the chaotic topology and a sheaf of rings
`\mathcal O`, once the source flat base-change comparison has been packaged into `hcomparison`,
an object of `D(\mathcal O)` lies in the Section `21.43` owner property exactly when all of its
cohomology sheaves are quasi-coherent. This is the objectwise form of the agreement
`QC(\mathcal O) = D_{\mathrm{QCoh}}(\mathcal O)`. -/
theorem qc_iff_derivedQuasiCoherent
    [hAdditive : ∀ U : C,
      (SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U) :
        Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U))).Additive]
    [hDerived : ∀ U : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived
          (SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U) :
            Mod𝒪 ⥤ ModuleCat (𝒪.1.obj (op U))))
        Qis𝒪]
    :
    let RGamma :
        ∀ U : C,
          DMod𝒪 ⥤ DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
      fun U ↦ chaoticRGamma 𝒪 U
    let derivedRestrict :
        ∀ {U V : C}, (U ⟶ V) →
          DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
            DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
      fun {U V} f ↦ chaoticDerivedRestrict 𝒪 f
    ∀ (comparison : ∀ {U V : C} (f : U ⟶ V), RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
      (hcomparison :
        ∀ (K : DMod𝒪) ⦃U V : C⦄ (f : U ⟶ V),
          IsIso ((comparison f).app K) ↔
            ∀ n : ℤ,
              IsIso
                (SheafOfModules.chaoticTensorSectionsMap 𝒪
                  ((DerivedCategory.homologyFunctor Mod𝒪 n).obj K) f))
      (K : DMod𝒪),
      let RGamma' :
          ∀ U : C, DMod𝒪 ⥤ DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
        fun U ↦ RGamma U
      let derivedRestrict' :
          ∀ {U V : C}, (U ⟶ V) →
            DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
              DerivedCategory (ModuleCat (𝒪.1.obj (op U))) :=
        fun {U V} f ↦ derivedRestrict f
      let comparison' :
          ∀ {U V : C} (f : U ⟶ V), RGamma' V ⋙ derivedRestrict' f ⟶ RGamma' U :=
        fun {U V} f ↦ comparison f
      let QCP : ObjectProperty DMod𝒪 :=
        isQuasiCoherent 𝒪.1 RGamma' derivedRestrict'
          (fun {U V : C} (f : U ⟶ V) ↦ comparison' f)
      QCP K ↔ DQCoh K := by
  dsimp
  intro comparison hcomparison K
  change
      (∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso ((comparison f).app K)) ↔
        ∀ n : ℤ, QCoh ((DerivedCategory.homologyFunctor Mod𝒪 n).obj K)
  constructor
  · intro h n
    rw [SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso 𝒪]
    intro U V f
    exact (hcomparison K f).mp (h f) n
  · intro h U V f
    refine (hcomparison K f).mpr ?_
    intro n
    exact (SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso 𝒪 _).mp (h n) f

end CategoryTheory.ModulesOnCategory
