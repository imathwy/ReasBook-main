import Mathlib
import StacksProject_2024.Chap20.Definition_20_26_14
import StacksProject_2024.Chap20.Definition_20_48_1
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: work locally using the `(a - 1)`-pseudo-coherent approximation by a strictly
-- perfect complex inducing cohomology isomorphisms in degrees `≥ a`. The cone is then a shift of
-- a kernel sheaf in degree `a - 1`. Derived tensoring with arbitrary modules and using the
-- tor-amplitude bound in `[a, b]` shows the corresponding cokernel sheaf is flat by Lemma
-- `20.26.16`; by Modules, Lemma `17.18.3` it is locally a direct summand of a finite free sheaf,
-- so the local truncation is again strictly perfect and represents `E`.
/-- Lemma 20.49.4: if an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` and is
`(a - 1)`-pseudo-coherent, with `a ≤ b`, then `E` is perfect. -/
theorem isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
    (E : DMod) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitudeIn E a b)
    (hpc : IsMPseudoCoherent E (a - 1)) :
    DerivedCategory.IsPerfect E := sorry

end

end AlgebraicGeometry.RingedSpace
