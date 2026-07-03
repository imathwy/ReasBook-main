import Mathlib
import StacksProject_2024.Chap20.Example_20_50_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [BraidedCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSpace.Modules X) ℤ)]

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ

-- Proof sketch: write the coevaluation and evaluation of the chosen left dual degreewise. The
-- triangle identities show that each term `F.X n` is locally a retract of a finite free
-- `\mathcal O_X`-module, by the module-sheaf lemma `17.18.2` applied in every degree. The
-- coevaluation is locally a finite sum, so only finitely many degrees occur near each point,
-- giving local boundedness; combine these two pieces into local strict perfectness.
/-- Lemma 20.50.3: if a complex `F^\bullet` of `\mathcal O_X`-modules has a left dual in the
monoidal category of complexes, then `F^\bullet` is locally strictly perfect. Equivalently, near
every point it is bounded and each term is a direct summand of a finite free `\mathcal O_X`
module. -/
theorem exactPairing_isLocallyStrictlyPerfect
    {F G : CpxX} (hpair : ExactPairing F G) :
    CochainComplex.IsLocallyStrictlyPerfect F := sorry

end AlgebraicGeometry.RingedSpace
