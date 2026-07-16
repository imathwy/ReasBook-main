import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_7_1
import StacksProject_2024.stacks_project.Chap31.31_27_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped RingedSpacePicard

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [IsLocallyNoetherian X] [IsIntegral X]
variable [PrimeDivisorDiscreteValuationRings X]
variable [MonoidalCategory (RingedSpace.Modules X.toLocallyRingedSpace.toRingedSpace)]
variable [SymmetricCategory (RingedSpace.Modules X.toLocallyRingedSpace.toRingedSpace)]

/- Lemma 31.27.6: let `X` be a locally Noetherian integral scheme. If `X` is normal, then the map
`Pic(X) → Cl(X)` of `(31.27.5.1)` is injective.

In the current project, the normality owner is `Scheme.isNormal`, the Picard-group owner is the
ringed-space notation `Pic(X.toLocallyRingedSpace.toRingedSpace)`, and the divisor-class-group
owner is `Cl(X)`, and `31.27.5.1` now provides the canonical comparison map
`picardToWeilDivisorClassGroup X`. -/
theorem injective_picardToWeilDivisorClassGroup (hX : X.isNormal) :
    Function.Injective (picardToWeilDivisorClassGroup X) := by
  sorry

end AlgebraicGeometry.Scheme
