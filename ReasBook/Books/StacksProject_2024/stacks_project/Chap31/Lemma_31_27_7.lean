import Mathlib
import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap31.Lemma_31_27_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [IsLocallyNoetherian X] [IsIntegral X]
variable [PrimeDivisorDiscreteValuationRings X]
variable [MonoidalCategory (RingedSpace.Modules X.toLocallyRingedSpace.toRingedSpace)]
variable [SymmetricCategory (RingedSpace.Modules X.toLocallyRingedSpace.toRingedSpace)]

/- Lemma 31.27.7: let `X` be a locally Noetherian integral scheme. The local rings of `X` are
UFDs if and only if `X` is normal and the map `Pic(X) -> Cl(X)` of `(31.27.5.1)` is surjective;
in this case that map is an isomorphism.

The current project has the normality owner `Scheme.isNormal`, the Picard-group owner
`Pic(X.toLocallyRingedSpace.toRingedSpace)`, and the Chapter 31 divisor-class-group notation
`Cl(X)`, while `31.27.5.1` provides the canonical map `picardToWeilDivisorClassGroup X`. -/
theorem isNormal_and_surjective_picardToWeilDivisorClassGroup_of_stalks_uniqueFactorizationMonoid
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    X.isNormal ∧ Function.Surjective (picardToWeilDivisorClassGroup X) := by
  sorry

theorem stalks_uniqueFactorizationMonoid_of_isNormal_of_surjective_picardToWeilDivisorClassGroup
    (hNormal : X.isNormal)
    (hsurj : Function.Surjective (picardToWeilDivisorClassGroup X)) :
    ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  sorry

theorem bijective_picardToWeilDivisorClassGroup_of_stalks_uniqueFactorizationMonoid
    (hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    Function.Bijective (picardToWeilDivisorClassGroup X) := by
  sorry

end AlgebraicGeometry.Scheme
