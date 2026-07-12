import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

-- Source/core/bridge triage:
-- `source-facing`: vanishing of `H^p(U, ℱ)` on an affine open `U`;
-- `core/canonical`: sheaf cohomology on the underlying additive sheaf
-- `((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ)`;
-- `bridge/view`: the affine-open hypothesis is exposed directly as `IsAffineOpen U` rather than
-- the subtype `X.affineOpens`, since the source item only needs the open together with its
-- affineness.

/-- Lemma 30.2.2: let `X` be a scheme and let `ℱ` be a quasi-coherent `\mathcal O_X`-module.
For any affine open `U ⊆ X`, the higher cohomology groups `H^p(U, \mathcal F)` vanish for all
`p > 0`. -/
@[stacks 01XB]
theorem higherCohomology_isZero_on_affineOpen
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p U) :=
  sorry

/-- Affine schemes have vanishing higher cohomology for quasi-coherent modules. -/
theorem higherCohomology_isZero_of_isAffine
    [IsAffine X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p (⊤ : X.Opens)) := by
  simpa using higherCohomology_isZero_on_affineOpen
    ℱ (⊤ : X.Opens) (isAffineOpen_top X) p hp

end AlgebraicGeometry.Scheme
