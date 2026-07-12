import Mathlib
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.Chap31.Definition_31_4_1
import StacksProject_2024.Chap31.Definition_31_23_7
import StacksProject_2024.Chap31.Lemma_31_12_4
import StacksProject_2024.Chap31.Lemma_31_23_9

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
variable [SymmetricCategory (SheafOfModules X.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]

local notation "ModX" => SheafOfModules X.ringCatSheaf
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation "IsInvertibleX" => (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

variable {ℒ : ModX}
variable [IsInvertibleX ℒ]
variable {s : X.toLocallyRingedSpace.meromorphicSections ℒ}

-- Semantic recall: `lean_leansearch` surfaced only generic support/image API and the existing
-- denominator owner from Lemma `31.23.9`. Local Chapter 31 precedent therefore keeps the
-- denominator ideal itself as `RegularMeromorphicSectionIdealSheaf` data and formalizes `Iℱ` as
-- the image subobject of the raw tensor multiplication map into `ℱ`.

/-- The closed subset `T` from Lemma `31.24.5`, written as the union of the supports of the two
cokernels already appearing in the denominator-ideal package from Lemma `31.23.9`. -/
abbrev denominatorSupportSet
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s) : Set X :=
  moduleSupport (cokernel hden.idealSheafArrow) ∪
    moduleSupport (cokernel hden.sectionMap)

/-- The raw tensor multiplication map
`\mathcal I \otimes_{\mathcal O_X} \mathcal F \to \mathcal F` induced by
`1 : \mathcal I \to \mathcal O_X`. -/
noncomputable abbrev denominatorIdealTensorToModule
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s) (ℱ : ModX) :
    ((show ModX from Subobject.underlying.obj hden.idealSheaf) ⊗ ℱ : ModX) ⟶ ℱ :=
  tensorHom
      (hden.idealSheafArrow ≫ (SheafOfModules.unitIsoTensorUnit : 𝒪X ≅ (𝟙_ ModX)).hom)
      (𝟙 ℱ) ≫
    (λ_ ℱ).hom

/-- The source-theoretic product `\mathcal I \mathcal F`, formalized as the image subobject of the
raw tensor multiplication map
`\mathcal I \otimes_{\mathcal O_X} \mathcal F \to \mathcal F`. -/
abbrev denominatorIdealMulSubobject
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s) (ℱ : ModX) : Subobject ℱ :=
  imageSubobject (denominatorIdealTensorToModule ℒ s hden ℱ)

/-- The raw tensor map
`\mathcal I \otimes_{\mathcal O_X} \mathcal F \to \mathcal F \otimes_{\mathcal O_X} \mathcal L`
induced by the denominator-section map `s : \mathcal I \to \mathcal L`. -/
noncomputable abbrev denominatorIdealTensorToTensor
    (ℒ : ModX) [IsInvertibleX ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s) (ℱ : ModX) :
    ((show ModX from Subobject.underlying.obj hden.idealSheaf) ⊗ ℱ : ModX) ⟶ (ℱ ⊗ ℒ : ModX) :=
  tensorHom hden.sectionMap (𝟙 ℱ) ≫ (β_ ℒ ℱ).hom

/-- Lemma 31.24.5 (1): let `X` be a locally Noetherian scheme, let `\mathcal L` be an invertible
`\mathcal O_X`-module, let `s` be a regular meromorphic section of `\mathcal L`, let
`\mathcal F` be a coherent `\mathcal O_X`-module without embedded associated points and with
support equal to `X`, and let `hden` be the denominator-ideal package from Lemma `31.23.9`.
Then the canonical map `1 : \mathcal I \mathcal F \to \mathcal F`, formalized as the subobject
arrow of `denominatorIdealMulSubobject hden ℱ`, is injective and its cokernel is supported on the
closed subset `T = denominatorSupportSet hden`. -/
@[stacks 02P2]
theorem denominatorIdealMulSubobjectArrow_mono_and_cokernel_support
    [IsLocallyNoetherian X]
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s)
    (ℱ : ModX) [ℱ.IsCoherent]
    (hEmbedded : embeddedAssociatedPoints ℱ = (∅ : Set X))
    (hSupp : moduleSupport ℱ = Set.univ) :
    Mono (Subobject.arrow (denominatorIdealMulSubobject ℒ s hden ℱ)) ∧
      moduleSupport (cokernel (Subobject.arrow (denominatorIdealMulSubobject ℒ s hden ℱ))) ⊆
        denominatorSupportSet ℒ s hden := sorry

/-- Lemma 31.24.5 (2): under the same hypotheses, there is a canonical map
`s : \mathcal I \mathcal F \to \mathcal F \otimes_{\mathcal O_X} \mathcal L`. In the image
formalization of `\mathcal I \mathcal F`, this means that the raw tensor map
`denominatorIdealTensorToTensor hden ℱ` factors through the image subobject
`denominatorIdealMulSubobject hden ℱ`; the induced map is injective and its cokernel is supported
on the same closed subset `T = denominatorSupportSet hden`. -/
@[stacks 02P2]
theorem exists_denominatorIdealMulSubobjectSectionMap
    [IsLocallyNoetherian X]
    (hden : RegularMeromorphicSectionIdealSheaf ℒ s)
    (ℱ : ModX) [ℱ.IsCoherent]
    (hEmbedded : embeddedAssociatedPoints ℱ = (∅ : Set X))
    (hSupp : moduleSupport ℱ = Set.univ) :
    ∃ (σ : (show ModX from Subobject.underlying.obj (denominatorIdealMulSubobject ℒ s hden ℱ)) ⟶
        (ℱ ⊗ ℒ : ModX)) (_hσ : Mono σ),
      factorThruImageSubobject (denominatorIdealTensorToModule ℒ s hden ℱ) ≫ σ =
          denominatorIdealTensorToTensor ℒ s hden ℱ ∧
        moduleSupport (cokernel σ) ⊆ denominatorSupportSet ℒ s hden := sorry

end AlgebraicGeometry.Scheme
