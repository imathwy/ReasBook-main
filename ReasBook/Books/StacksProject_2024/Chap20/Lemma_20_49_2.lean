import Mathlib
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "Q" =>
  (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DModX)

-- Proof sketch: apply the representative bridge from Definition `20.49.1`; the given perfect
-- complex `K` already supplies the chosen representative required there.
/-- Lemma 20.49.2 (1): a perfect representative complex determines a perfect object of
`D(\mathcal O_X)`. -/
theorem derived_isPerfect_of_perfect_representative
    (E : DModX) (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (e : E ≅ Q.obj K) (hK : CochainComplex.IsPerfect K) :
    DerivedCategory.IsPerfect E := sorry

-- Proof sketch: unpack the perfect representative supplied by `DerivedCategory.IsPerfect E`,
-- obtaining a perfect complex `L` with `E ≅ Q.obj L`. Compose this isomorphism with the chosen
-- representation `E ≅ Q.obj K` and transport perfection across the induced isomorphism between
-- `Q.obj L` and `Q.obj K`; by the local definition of `CochainComplex.IsPerfect`, the complex `K`
-- inherits the same strictly perfect local presentation.
/-- Lemma 20.49.2 (2): if `E` is a perfect object of `D(\mathcal O_X)`, then every cochain
complex representing `E` is perfect. -/
theorem representing_complex_isPerfect_of_derived_isPerfect
    (E : DModX) (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (e : E ≅ Q.obj K) (hE : DerivedCategory.IsPerfect E) :
    CochainComplex.IsPerfect K := sorry

end AlgebraicGeometry.RingedSpace
