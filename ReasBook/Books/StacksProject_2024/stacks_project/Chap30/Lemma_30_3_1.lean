import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData`, while local Chapter 30/31
-- precedent represents ideal sheaves as subobjects of the structure sheaf and states global
-- sheaf cohomology through `SheafOfModules.toSheaf` and `Sheaf.H'`.

/-- Lemma 30.3.1: let `X` be a quasi-compact scheme. If `H^1(X, I) = 0` for every
quasi-coherent sheaf of ideals `I ⊂ \mathcal O_X`, then `X` is affine. -/
@[stacks 01XF]
theorem isAffine_of_H1_vanishes_for_quasiCoherent_idealSheaves
    (X : Scheme.{u}) [CompactSpace X.carrier]
    (hH1 : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj (Subobject.underlying.obj I)).H' 1
          (⊤ : X.Opens))) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme
