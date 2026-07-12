import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical affine/quasi-compact scheme API;
-- local Lemma 30.3.1 represents ideal sheaves as subobjects of `\mathcal O_X` and uses
-- sheaf cohomology as `Sheaf.H'` on the top open.

/-- Lemma 30.3.2: let `X` be a quasi-compact and quasi-separated scheme. If
`H^1(X, \mathcal I) = 0` for every finite type quasi-coherent sheaf of ideals
`\mathcal I`, then `X` is affine. -/
@[stacks 01XG]
theorem isAffine_of_H1_vanishes_for_finiteType_quasiCoherent_idealSheaves
    (X : Scheme.{u}) [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (hH1 : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules),
      (Subobject.underlying.obj I).IsQuasicoherent →
        (Subobject.underlying.obj I).IsFiniteType →
          IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj (Subobject.underlying.obj I)).H' 1
            (⊤ : X.Opens))) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme
