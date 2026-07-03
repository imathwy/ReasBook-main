import Mathlib
import StacksProject_2024.Chap20.Example_20_50_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: this is the derived-category analogue of the module statement from
-- `Lemma 15.127.3`. Starting from a left dual pairing, the textbook proof factors the
-- coevaluation through a bounded flat subcomplex, showing that `M` is a retract of an object with
-- finite tor amplitude; then the pseudo-coherence induction of Lemma `20.49.4` upgrades this to
-- perfection.
/-- Lemma 20.50.8: if an object `M` of `D(\mathcal O_X)` has a left dual in the monoidal
category `D(\mathcal O_X)`, then `M` is perfect. -/
theorem exactPairing_isPerfect
    {M N : DMod} (hpair : ExactPairing M N) :
    DerivedCategory.IsPerfect M := sorry

/-- The unique isomorphism from a chosen left dual of `M` in `D(\mathcal O_X)` to the canonical
derived dual `R\mathcal H\!\mathit{om}(M, \mathcal O_X)` from Example `20.50.7`. This is the
textbook identification of an arbitrary left dual with the one constructed there. -/
noncomputable def exactPairing_rightDualIso_ringedSpaceDerivedDual
    {M N : DMod} (hpair : ExactPairing M N) :
    N ≅ ringedSpaceDerivedDual M :=
  rightDualIso hpair (ringedSpaceDerivedDualExactPairing (exactPairing_isPerfect hpair))

end

end AlgebraicGeometry.RingedSpace
