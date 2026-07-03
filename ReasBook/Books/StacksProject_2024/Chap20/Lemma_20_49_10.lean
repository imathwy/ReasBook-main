import StacksProject_2024.Chap20.Lemma_20_33_6
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

local notation "DModU" => DerivedCategory (openSubspaceModuleCategory X U)

-- Proof sketch: by Lemma `20.33.6 (2)`, the support hypothesis identifies `Rj_* E` with
-- extension by zero from `U`. Perfectness is local on `X`: on `U` this extension restricts to
-- `E`, hence is perfect, while on the open complement of the closed image of `T` it vanishes.
/-- Lemma 20.49.10: let `j : U ↪ X` be an open subspace of a ringed space and let `E` be a
perfect object of `D(\mathcal O_U)`. If the cohomology sheaves of `E` are supported on a subset
`T ⊆ U` whose image is closed in `X`, then `Rj_* E` is a perfect object of `D(\mathcal O_X)`. -/
theorem isPerfect_pushforwardFromOpen_of_isPerfect_of_cohomologySupported
    {T : Set X.carrier} (hT_closed : IsClosed T)
    (hTU : T ⊆ (U : Set X.carrier))
    (E : DModU)
    (hE_perfect : DerivedCategory.IsPerfect E)
    (hE_support : moduleDerivedCohomologySupportedOn
      ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))
      E
      (Subtype.val ⁻¹' T)) :
    DerivedCategory.IsPerfect ((moduleDerivedPushforwardFromOpen U).obj E) :=
  by
    sorry

end

end AlgebraicGeometry.RingedSpace
