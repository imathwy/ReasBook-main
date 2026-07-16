import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_13_1_Owner
import StacksProject_2024.stacks_project.Chap17.TensorPowerSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme-module pullback/pushforward
adjunction owners, and local Chapter 17 precedent already fixes the closed-immersion ideal sheaf
as `RingedSpace.closedImmersionIdealSheaf` and the natural tensor powers as `T^[n] ℒ`. The
displayed row is therefore recorded directly as a short complex built from those existing owners.
-/

section

variable {X Z : Scheme.{u}} (i : Z ⟶ X)
variable [IsClosedImmersion i]
variable [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "φi" => RingedSpace.Hom.toRingCatSheafHom i.toShHom
local notation "𝓘" => RingedSpace.closedImmersionIdealSheaf i.toShHom
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
local notation "IsInvertibleX" => (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

/-- The canonical inclusion of the ideal sheaf of a closed immersion into the ambient structure
sheaf. -/
private noncomputable abbrev closedImmersionIdealSheafι : 𝓘 ⟶ 𝒪X :=
  CategoryTheory.Limits.kernel.ι (SheafOfModules.unitToPushforwardObjUnit φi)

/-- The tensorized structure-sheaf action on a module sheaf, written with the ambient
structure-sheaf owner rather than the abstract tensor unit. -/
private noncomputable def structureSheafLeftUnitor (ℱ : ModX) :
    (𝒪X ⊗ₘ ℱ : ModX) ⟶ ℱ := by
  simpa using (λ_ ℱ).hom

/-- The left map in the tensorized closed-immersion row: it is induced from the inclusion
`\mathcal I \hookrightarrow \mathcal O_X` after tensoring with the chosen power of `\mathcal L`.
-/
@[stacks 0B8T]
noncomputable def closedImmersionTensorPowerLeftMap
    (ℒ : ModX) (n : ℕ) :
    (𝓘 ⊗ₘ (T^[n] ℒ) : ModX) ⟶ (T^[n] ℒ) :=
  tensorHom (closedImmersionIdealSheafι i) (𝟙 (T^[n] ℒ)) ≫
    structureSheafLeftUnitor (T^[n] ℒ)

/-- The right map in the tensorized closed-immersion row: it is the adjunction unit
`\mathcal L^{\otimes n} \to i_* i^* \mathcal L^{\otimes n}`. -/
@[stacks 0B8T]
noncomputable def closedImmersionTensorPowerRestrictionMap
    (ℒ : ModX) (n : ℕ) :
    (T^[n] ℒ) ⟶
      (SheafOfModules.pushforward φi).obj
        ((SheafOfModules.pullback φi).obj (T^[n] ℒ)) :=
  (SheafOfModules.pullbackPushforwardAdjunction φi).unit.app (T^[n] ℒ)

/-- The tensorized ideal-sheaf map factors through the adjunction unit to zero. -/
@[stacks 0B8T]
theorem closedImmersionTensorPower_comp_zero
    (ℒ : ModX) (n : ℕ) :
    closedImmersionTensorPowerLeftMap i ℒ n ≫
      closedImmersionTensorPowerRestrictionMap i ℒ n = 0 := sorry

/-- 30.17.5.1: if `i : Z ⟶ X` is a closed immersion with ideal sheaf `\mathcal I`, then for an
invertible `\mathcal O_X`-module `\mathcal L` and `n : \mathbf N`, the canonical row
`0 \to \mathcal I \otimes_{\mathcal O_X} \mathcal L^{\otimes n} \to
\mathcal L^{\otimes n} \to i_* i^* \mathcal L^{\otimes n} \to 0`
is short exact. -/
@[stacks 0B8T]
theorem closedImmersionTensorPowerShortExact
    (ℒ : ModX) [IsInvertibleX ℒ] (n : ℕ) :
    (ShortComplex.mk
      (closedImmersionTensorPowerLeftMap i ℒ n)
      (closedImmersionTensorPowerRestrictionMap i ℒ n)
      (closedImmersionTensorPower_comp_zero i ℒ n)).ShortExact := sorry

end

end AlgebraicGeometry
