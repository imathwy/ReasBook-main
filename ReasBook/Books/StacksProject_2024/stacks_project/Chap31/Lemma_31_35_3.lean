import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap29.Definition_29_7_1
import StacksProject_2024.Chap31.Definition_31_33_1
import StacksProject_2024.Chap31.Definition_31_34_1
import StacksProject_2024.Chap31.Lemma_31_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` only surfaced the surrounding module-side local-freeness
-- APIs. Local Chapter 29/31/20 precedent fixes the source-facing owners here as
-- `schemeTheoreticallyDense`, `IsAdmissibleBlowup`, `strictTransformModule`, and the degree-zero
-- derived perfectness / tor-dimension predicates.

section

variable {X X' : Scheme.{u}} (b : X' ⟶ X)

/-- The pullback scheme underlying the strict transform for the blowup of `X` along
`Scheme.fittingIdealSheaf ℱ r`. -/
private abbrev fittingBlowupAmbient : Scheme.{u} :=
  Limits.pullback (𝟙 X) b

/-- The pullback of an `\mathcal O_X`-module to the ambient pullback scheme used for the strict
transform. -/
private abbrev fittingBlowupPullbackModule
    (ℱ : X.Modules) : (fittingBlowupAmbient b).Modules :=
  (Scheme.Modules.pullback (Limits.pullback.fst (𝟙 X) b)).obj ℱ

/-- The inverse image of an open subscheme `U ⊆ X` on the ambient pullback scheme of the blowup
construction. -/
private abbrev fittingBlowupPreimageOpen (U : X.Opens) : Opens (fittingBlowupAmbient b) :=
  (Opens.map (Limits.pullback.fst (𝟙 X) b).base).obj U

/-- The kernel of the canonical surjection from the pullback module to its strict transform along
the blowup in `Fit_r(ℱ)`. -/
private noncomputable def fittingBlowupStrictTransformKernel
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] (r : ℕ) :
    (fittingBlowupAmbient b).Modules :=
  let Y : Scheme.{u} := fittingBlowupAmbient b
  let E : X'.IdealSheafData := (Scheme.fittingIdealSheaf ℱ r).comap b
  let EpullSupport : Set Y :=
    (((E.comap (Limits.pullback.snd (𝟙 X) b)).support :
      TopologicalSpace.Closeds Y) : Set Y)
  let hEpull : IsClosed EpullSupport :=
    (E.comap (Limits.pullback.snd (𝟙 X) b)).support.2
  let V : Opens Y := ⟨EpullSupportᶜ, hEpull.isOpen_compl⟩
  let 𝒢 : Y.Modules := fittingBlowupPullbackModule b ℱ
  let structureHom :
      Y.ringCatSheaf ⟶
        (TopCat.Sheaf.pushforward RingCat.{u} V.inclusion').obj
          ((TopCat.Sheaf.pullback RingCat.{u} V.inclusion').obj Y.ringCatSheaf) :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} V.inclusion').unit.app
      Y.ringCatSheaf
  let restriction :
      𝒢 ⟶
        (SheafOfModules.pushforward structureHom).obj
          ((moduleSheafRestrictionToOpen V Y.ringCatSheaf).obj 𝒢) :=
    (SheafOfModules.pullbackPushforwardAdjunction structureHom).unit.app 𝒢
  let supportedSections : Subobject 𝒢 := kernelSubobject restriction
  kernel (cokernel.π supportedSections.arrow)

end

/-- Lemma 31.35.3 (1): let `X` be a scheme, let `ℱ` be a finitely presented `\mathcal O_X`-
module, and let `U ⊆ X` be a scheme theoretically dense open such that `ℱ|_U` is finite locally
free of constant rank `r`. Then the blowup of `X` in `Fit_r(ℱ)` is `U`-admissible. -/
@[stacks 0ESN]
theorem isAdmissibleBlowup_of_schemeTheoreticallyDense_open_of_isFiniteLocallyFreeOfRank_on_of_isBlowup_fittingIdealSheaf
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    IsAdmissibleBlowup U b := sorry

/-- Lemma 31.35.3 (2): under the hypotheses of Lemma `31.35.3`, the strict transform of `ℱ`
along the blowup in `Fit_r(ℱ)` is locally free of rank `r`. -/
@[stacks 0ESN]
theorem strictTransformModule_isFiniteLocallyFreeOfRank_of_schemeTheoreticallyDense_open_of_isFiniteLocallyFreeOfRank_on_of_isBlowup_fittingIdealSheaf
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      (strictTransformModule b ((Scheme.fittingIdealSheaf ℱ r).comap b) (𝟙 X) ℱ) := sorry

/-- Lemma 31.35.3 (3): under the hypotheses of Lemma `31.35.3`, the kernel of the canonical
surjection from the pullback module to the strict transform is finitely presented. -/
@[stacks 0ESN]
theorem strictTransformKernel_isFinitePresentation_of_schemeTheoreticallyDense_open_of_isFiniteLocallyFreeOfRank_on_of_isBlowup_fittingIdealSheaf
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    (fittingBlowupStrictTransformKernel b ℱ r).IsFinitePresentation := sorry

/-- Lemma 31.35.3 (4): under the hypotheses of Lemma `31.35.3`, the kernel of the canonical
surjection from the pullback module to the strict transform restricts to zero over the inverse
image of `U`. -/
@[stacks 0ESN]
theorem strictTransformKernel_isZero_over_preimage_of_schemeTheoreticallyDense_open_of_isFiniteLocallyFreeOfRank_on_of_isBlowup_fittingIdealSheaf
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    Limits.IsZero
      ((fittingBlowupStrictTransformKernel b ℱ r).over (fittingBlowupPreimageOpen b U)) := sorry

/-- Lemma 31.35.3 (5): under the hypotheses of Lemma `31.35.3`, every stalk of the pullback
module `b^*ℱ` is a perfect module over the local ring and has tor dimension at most `1`. -/
@[stacks 0ESN]
theorem pullbackModule_stalk_isPerfect_and_moduleHasTorDimensionLE_one_of_schemeTheoreticallyDense_open_of_isFiniteLocallyFreeOfRank_on_of_isBlowup_fittingIdealSheaf
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    ∀ y : fittingBlowupAmbient b,
      ModuleCat.IsPerfect (RingedSpace.stalkModuleCat (fittingBlowupPullbackModule b ℱ) y) ∧
        CategoryTheory.ModuleHasTorDimensionLE
          (RingedSpace.stalkModuleCat (fittingBlowupPullbackModule b ℱ) y) 1 := sorry

/-- Lemma 31.35.3 (6): under the hypotheses of Lemma `31.35.3`, the kernel of the canonical
surjection from the pullback module to the strict transform has stalks that are perfect modules
of tor dimension at most `1`. -/
@[stacks 0ESN]
theorem strictTransformKernel_stalk_isPerfect_and_moduleHasTorDimensionLE_one_of_schemeTheoreticallyDense_open_of_isFiniteLocallyFreeOfRank_on_of_isBlowup_fittingIdealSheaf
    {X X' : Scheme.{u}} (b : X' ⟶ X) (U : X.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (r : ℕ)
    (hU_dense : schemeTheoreticallyDense U)
    (hℱU : SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Scheme.Modules.pullback (X.ofRestrict U.isOpenEmbedding)).obj ℱ))
    [IsBlowup b (Scheme.fittingIdealSheaf ℱ r)] :
    ∀ y : fittingBlowupAmbient b,
      ModuleCat.IsPerfect (RingedSpace.stalkModuleCat (fittingBlowupStrictTransformKernel b ℱ r) y) ∧
        CategoryTheory.ModuleHasTorDimensionLE
          (RingedSpace.stalkModuleCat (fittingBlowupStrictTransformKernel b ℱ r) y) 1 := sorry

end AlgebraicGeometry.Scheme.Modules
