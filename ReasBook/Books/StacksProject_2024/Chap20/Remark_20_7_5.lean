import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The underlying abelian sheaf of an `\mathcal O_X`-module on a ringed space. -/
private abbrev ringedSpaceModuleUnderlyingSheaf {X : RingedSpace.{u}}
    (F : SheafOfModules (ringedSpaceRingCatSheaf X)) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj F

-- Proof sketch: the sheafification functor on presheaves of `\mathcal O_X`-modules is exact and
-- the derived-functor description from Lemma `20.11.4` identifies the higher right derived
-- functors of the inclusion with the cohomology presheaves. This yields the restatement of Lemma
-- `20.7.2` used in the remark: the sheafification of the positive cohomology presheaf is zero.
/-- Remark 20.7.5: for a ringed space `(X, \mathcal O_X)`, the sheafification of the positive
cohomology presheaf `\underline H^p(\mathcal F)` of an `\mathcal O_X`-module vanishes; this is
the derived-functor reformulation underlying the alternative proof of Lemma `20.7.2`. -/
theorem positive_cohomologyPresheaf_sheafification_isZero
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : SheafOfModules (ringedSpaceRingCatSheaf X)) {p : ℕ} (hp : 0 < p) :
    IsZero
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((ringedSpaceModuleUnderlyingSheaf F).cohomologyPresheaf p)) := sorry

end AlgebraicGeometry
