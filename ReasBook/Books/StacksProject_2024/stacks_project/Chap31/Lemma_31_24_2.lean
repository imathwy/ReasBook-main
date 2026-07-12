import Mathlib
import StacksProject_2024.Chap31.Lemma_31_23_6
import StacksProject_2024.Chap31.Lemma_31_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

local notation "KX" => X.toLocallyRingedSpace.meromorphicFunctionSheaf

-- Source/core/bridge triage:
-- * `source-facing`: Lemma 31.24.2 is the locally Noetherian specialization of the meromorphic
--   total-quotient statements.
-- * `core/canonical`: the Chapter 31 owners are `meromorphicStalk_isLocalization` and
--   `meromorphicSections_isLocalization_of_isAffineOpen`.
-- * `bridge/view`: local Noetherianity identifies `X.weakAss` with the generic points via
--   `weakAss_subset_genericPoints`.

/-- Lemma 31.24.2 (1): for a locally Noetherian scheme `X` and a point `x`, the meromorphic
stalk `𝒦_{X,x}` is the total quotient ring of the local ring `𝒪_{X,x}`. -/
@[stacks 0EMG]
theorem meromorphicStalk_isLocalization_of_isLocallyNoetherian (x : X) :
    IsLocalization (nonZeroDivisors (X.presheaf.stalk x)) ((KX).presheaf.stalk x) := by
  simpa using
    (meromorphicStalk_isLocalization (X := X)
      (hweak := Scheme.weakAss_subset_genericPoints (X := X)) x)

/-- Lemma 31.24.2 (2): for a locally Noetherian scheme `X` and an affine open `U`, the ring of
meromorphic sections `𝒦_X(U)` is the total quotient ring of the affine coordinate ring
`Γ(U, 𝒪_X)`. -/
@[stacks 0EMG]
theorem meromorphicSections_isLocalization_of_isAffineOpen_of_isLocallyNoetherian
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsLocalization (nonZeroDivisors Γ(X, U)) ((KX).presheaf.obj (op U)) := by
  simpa using
    (meromorphicSections_isLocalization_of_isAffineOpen (X := X)
      (hweak := Scheme.weakAss_subset_genericPoints (X := X)) U hU)

end AlgebraicGeometry
