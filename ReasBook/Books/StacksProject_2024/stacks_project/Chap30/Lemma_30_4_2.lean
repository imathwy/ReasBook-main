import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the affine-diagonal owner
-- `IsAffineHom (prod.lift (𝟙 X) (𝟙 X))`, the quasi-coherent-module owner
-- `SheafOfModules.IsQuasicoherent`, and local Chapter 30 precedent uses `IsZero` of the global
-- sheaf cohomology object `H' n (⊤ : Opens X)` for vanishing.

/-- A finite family of affine opens covering a scheme. -/
structure FiniteAffineOpenCover (X : Scheme.{u}) (t : ℕ) where
  /-- The finite family of open subsets. -/
  opens : Fin t → X.Opens
  /-- The family covers the whole underlying topological space. -/
  isOpenCover : IsOpenCover opens
  /-- Every member of the family is affine. -/
  isAffineOpen : ∀ i, IsAffineOpen (opens i)

/-- Lemma 30.4.2: let `X` be a quasi-compact scheme with affine diagonal, and let `t = t(X)` be
the minimal number of affine opens needed to cover `X`. Then `H^n(X, \mathcal F) = 0` for every
`n ≥ t` and every quasi-coherent `\mathcal O_X`-module `\mathcal F`. -/
@[stacks 01XI]
theorem globalCohomology_isZero_of_minimal_affineOpenCoverCard
    [CompactSpace X.carrier] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (t : ℕ)
    (𝒰 : FiniteAffineOpenCover X t)
    (hminimal : ∀ m : ℕ, m < t → IsEmpty (FiniteAffineOpenCover X m))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (n : ℕ) (hn : t ≤ n) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' n (⊤ : Opens X)) := sorry

end AlgebraicGeometry.Scheme
