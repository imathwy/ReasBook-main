import StacksProject_2024.Chap06.Definition_6_26_1
import Mathlib

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))

/- The regularity condition uses only the ambient ringed-space module category: for an invertible
sheaf `ℒ`, a global section corresponds canonically to a morphism `𝒪_X ⟶ ℒ` via
`unitHomEquiv.symm`, and regularity is the monomorphism condition on that map. The source-facing
owner therefore lives on `RingedSpace`; `LocallyRingedSpace` reuses it below through a thin
bridge. -/

/-- The underlying ringed-space regularity predicate used by
`LocallyRingedSpace.IsRegularSection`. -/
abbrev IsRegularSection (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) : Prop :=
  Mono (ℒ.unitHomEquiv.symm s : 𝒪X ⟶ ℒ)

/-- Companion to Definition 31.14.6: a regular section is exactly a global section whose
associated morphism from the structure sheaf is a monomorphism. -/
theorem isRegularSection_iff_mono (ℒ : ModX) [IsInvertibleX ℒ] (s : ℒ.sections) :
    IsRegularSection ℒ s ↔ Mono (ℒ.unitHomEquiv.symm s : 𝒪X ⟶ ℒ) :=
  Iff.rfl

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "𝒪X" =>
  (SheafOfModules.unit X.toRingedSpace.ringCatSheaf : ModX)

/-- Definition 31.14.6: for an invertible sheaf `\mathcal L` on a locally ringed space `X`, a
global section `s` is regular if the associated morphism `\mathcal O_X \to \mathcal L`,
equivalently the map `f ↦ fs`, is injective. -/
@[stacks 01WY]
abbrev IsRegularSection (ℒ : ModX) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections) :
    Prop :=
  RingedSpace.IsRegularSection ℒ s

/-- Companion to Definition 31.14.6: a regular section is exactly a global section whose
associated morphism from the structure sheaf is a monomorphism. -/
theorem isRegularSection_iff_mono
    (ℒ : ModX) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections) :
    IsRegularSection ℒ s ↔ Mono (ℒ.unitHomEquiv.symm s : 𝒪X ⟶ ℒ) :=
  RingedSpace.isRegularSection_iff_mono ℒ s

end AlgebraicGeometry.LocallyRingedSpace
