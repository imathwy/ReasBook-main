import StacksProject_2024.Chap30.Lemma_30_17_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme predicates
-- `Scheme.IsQuasiAffine` and `IsAffine`. Local Chapter 30 precedent represents
-- `H^p(X, \mathcal O_X)` as `Sheaf.H'` on the underlying additive sheaf of
-- `SheafOfModules.unit X.ringCatSheaf`.

/-- Lemma 30.17.8: let `X` be a quasi-affine scheme. If
`H^p(X, \mathcal O_X) = 0` for every `p > 0`, then `X` is affine. -/
@[stacks 0EBE]
theorem IsQuasiAffine.isAffine_of_structureSheaf_higherCohomology_isZero
    {X : Scheme.{u}} (hX : X.IsQuasiAffine)
    (hvanish : ∀ p : ℕ, 0 < p →
      IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H' p (⊤ : X.Opens))) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme
