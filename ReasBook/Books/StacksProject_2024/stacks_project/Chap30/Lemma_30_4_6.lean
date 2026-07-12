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

variable {X S : Scheme.{u}}

-- Semantic recall: `lean_leansearch` returned the affine-scheme owner `IsAffine`; local Chapter
-- 20/30 precedent states sheaf cohomology on the `SheafOfModules.toSheaf` owner and higher direct
-- images on `((Scheme.Modules.pushforward f).rightDerived q).obj ℱ`.

/-- Lemma 30.4.6: let `f : X ⟶ S` be a quasi-separated and quasi-compact morphism of
schemes, with `S` affine. For any quasi-coherent `\mathcal O_X`-module `\mathcal F`, the
degree-`q` global cohomology of `\mathcal F` on `X` identifies with the degree-zero global
cohomology on `S` of the higher direct image `R^q f_* \mathcal F`. This Lean surface uses the
standard `ℕ`-indexed cohomology and right-derived-functor owners. -/
@[stacks 01XK]
theorem globalCohomology_iso_degreeZero_higherDirectImage_of_quasiCompact_quasiSeparated_affine
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffine S]
    [HasInjectiveResolutions X.Modules]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u})]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (q : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' q (⊤ : Opens X))
      (((SheafOfModules.toSheaf S.ringCatSheaf).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj ℱ)).H' 0 (⊤ : Opens S)) := sorry

end AlgebraicGeometry.Scheme
