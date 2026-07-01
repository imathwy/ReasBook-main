import Mathlib
import stacks_project.Chap20.Lemma_20_11_5
import stacks_project.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

section OpenCohomology

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]

-- Proof sketch: compute `H^i(U, \mathcal F)` as the `i`-th right derived functor of the sections
-- functor `\Gamma(U, -)` on `\mathcal O_X`-modules, then forget the `\Gamma(U, \mathcal O_X)`-
-- module structure. The same injective resolution, viewed through `SheafOfModules.toSheaf`,
-- computes the abelian-sheaf cohomology group on `U`.
/-- Lemma 20.13.3 (1): for an open subset `U ⊆ X`, the degree-`i` cohomology of an
`\mathcal O_X`-module `\mathcal F` computed in the category of `\mathcal O_X`-modules agrees,
after forgetting the module structure, with the degree-`i` cohomology of the underlying abelian
sheaf of `\mathcal F` on `U`. -/
theorem moduleCohomologyAtOpen_underlying_isomorphic_underlyingSheafCohomology
    (ℱ : (RingedSpace.Modules X)) (U : Opens X.carrier) (i : ℕ) :
    IsIsomorphic
      ((forget₂ (ModuleCat.{u} (X.presheaf.obj (op U))) AddCommGrpCat.{u}).obj
        (moduleCohomologyAtOpen U ℱ i))
      (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).H' i U) := sorry

end OpenCohomology

section HigherDirectImage

variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable [HasInjectiveResolutions
  (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

-- Proof sketch: forget an injective resolution of `\mathcal F` in `(RingedSpace.Modules X)` to an
-- injective resolution of the underlying abelian sheaf, use Remark `20.13.2` to identify the
-- section complexes termwise, and then apply Lemma `20.7.3` to identify the resulting right
-- derived direct images.
/-- Lemma 20.13.3 (2): for a morphism of ringed spaces `f : X ⟶ Y`, the degree-`i` higher direct
image of an `\mathcal O_X`-module `\mathcal F`, viewed as an abelian sheaf on `Y`, agrees with
the degree-`i` higher direct image of the underlying abelian sheaf of `\mathcal F`. -/
theorem higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf
    (f : X ⟶ Y)
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).Additive]
    (ℱ : (RingedSpace.Modules X)) (i : ℕ) :
    IsIsomorphic
      ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf Y)).obj
        (((RingedSpace.Hom.pushforward f).rightDerived i).obj ℱ))
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).rightDerived i).obj
        ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ)) := sorry

end HigherDirectImage

end AlgebraicGeometry.RingedSpace
