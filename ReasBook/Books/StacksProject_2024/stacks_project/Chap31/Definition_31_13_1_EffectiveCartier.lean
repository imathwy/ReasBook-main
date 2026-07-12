import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap17.Definition_17_13_1_Owner

-- Declarations extracted from Definition 31.13.1 for files that only use the
-- effective-Cartier owner and its ideal-sheaf-data bridge.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Definition 31.13.1 (2): an effective Cartier divisor on a scheme `S` is a closed subscheme
`i : D ⟶ S` whose ideal sheaf is an invertible `\mathcal O_S`-module. -/
class IsEffectiveCartierDivisor
    {S D : Scheme.{u}} (i : D ⟶ S)
    [MonoidalCategory (RingedSpace.Modules S.toRingedSpace)]
    : Prop extends IsClosedImmersion i,
      Functor.IsEquivalence
        (tensorRight (RingedSpace.closedImmersionIdealSheaf i.toShHom))

/-- Companion to Definition 31.13.1 (2): an effective Cartier divisor is exactly a closed
immersion whose ideal sheaf is invertible. -/
theorem isEffectiveCartierDivisor_iff
    {S D : Scheme.{u}} (i : D ⟶ S)
    [MonoidalCategory (RingedSpace.Modules S.toRingedSpace)] :
    IsEffectiveCartierDivisor i ↔
      IsClosedImmersion i ∧
        Functor.IsEquivalence
          (tensorRight (RingedSpace.closedImmersionIdealSheaf i.toShHom)) := by
  constructor
  · intro h
    exact ⟨h.toIsClosedImmersion, h.toIsEquivalence⟩
  · rintro ⟨hi, hinv⟩
    exact
      { toIsClosedImmersion := hi
        toIsEquivalence := hinv }

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}
variable [MonoidalCategory (RingedSpace.Modules X.toRingedSpace)]

/-- The source-facing effective-Cartier condition on `X.IdealSheafData`, expressed through the
canonical Chapter 31 owner on the closed immersion `D.subschemeι`. -/
abbrev IsEffectiveCartierDivisor (D : X.IdealSheafData) : Prop :=
  AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι

/-- Bridge back to the source-facing ideal-sheaf owner. -/
@[simp] theorem isEffectiveCartierDivisor_subschemeι_iff (D : X.IdealSheafData) :
    D.IsEffectiveCartierDivisor ↔ AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι := by
  rfl

end Scheme.IdealSheafData

end AlgebraicGeometry
