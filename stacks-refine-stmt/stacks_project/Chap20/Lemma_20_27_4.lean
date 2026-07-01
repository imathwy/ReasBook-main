import Mathlib
import stacks_project.Chap20.Lemma_20_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [Abelian (RingedSpace.Modules X)]
variable [Abelian (RingedSpace.Modules Y)]
variable
  [Abelian
    (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf Y)))]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

variable
  (leftDerivedPullback : DModY ⥤ DModX)
  (derivedTensorSource : DModX ⥤ DModX ⥤ DModX)
  (derivedTensorInverseImage :
    DerivedCategory
        (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf Y))) ⥤
      DModX ⥤ DModX)
  (inverseImageDerived :
    DModY ⥤
      DerivedCategory
        (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf Y))))

-- Proof sketch: replace `Lf^*` and the two derived tensor products by K-flat representatives,
-- identify the underived comparison using the formula
-- `f^*\mathcal G = \mathcal O_X \otimes_{f^{-1}\mathcal O_Y} f^{-1}\mathcal G`, and descend the
-- resulting termwise comparison to the derived categories. The canonical bifunctoriality is
-- encoded as a natural isomorphism in the functor category `D(\mathcal O_Y) ⥤ D(\mathcal O_X) ⥤
-- D(\mathcal O_X)`.
/-- Lemma 20.27.4: for a morphism of ringed spaces
`f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`, the canonical bifunctorial isomorphism
`\mathcal F^\bullet \otimes_{\mathcal O_X}^{\mathbf L} Lf^* \mathcal G^\bullet \cong
\mathcal F^\bullet \otimes_{f^{-1}\mathcal O_Y}^{\mathbf L} f^{-1}\mathcal G^\bullet`
is expressed canonically as a natural isomorphism of functors
`D(\mathcal O_Y) ⥤ D(\mathcal O_X) ⥤ D(\mathcal O_X)`. -/
theorem derivedTensor_leftDerivedPullback_iso :
    leftDerivedPullback ⋙ derivedTensorSource ≅
      inverseImageDerived ⋙ derivedTensorInverseImage := sorry

end

end AlgebraicGeometry.RingedSpace
