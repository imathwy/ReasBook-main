import StacksProject_2024.stacks_project.Chap20.Definition_20_47_1_Core
import StacksProject_2024.stacks_project.Chap20.Definition_20_48_1_Core
import StacksProject_2024.stacks_project.Chap20.Definition_20_49_1

open AlgebraicGeometry
open CategoryTheory
open _root_.AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [MonoidalCategory (DerivedCategory (Modules X))]

local notation "DMod" => DerivedCategory (Modules X)

/- Domain-style sampling for Lemma 20.49.4:
- primary domain: perfect objects of `D(𝒪_X)` detected by tor-amplitude and pseudo-coherence;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `ModuleDerived.IsMPseudoCoherent`,
  `DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: the Chapter 20 perfection criterion for `D(𝒪_X)`;
  `core/canonical`: the Chapter 20 ringed-space owners `HasTorAmplitudeIn`,
    `ModuleDerived.IsMPseudoCoherent`, and `DerivedCategory.IsPerfect`;
  `bridge/view`: none in the public API of this file; the opens-ringed-site comparison belongs in
    the dedicated bridge modules.
-/
namespace DerivedCategory

/-- Lemma 20.49.4: if an object `E` of `D(𝒪_X)` has tor-amplitude in `[a, b]` and is
`(a - 1)`-pseudo-coherent, then `E` is perfect. -/
@[stacks 08CP]
theorem isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
    (E : DMod) (a b : ℤ)
    (hamp : HasTorAmplitudeIn E a b)
    (hpc : IsMPseudoCoherent E (a - 1)) :
    IsPerfect E := by
  sorry

end DerivedCategory

end

end AlgebraicGeometry.RingedSpace
