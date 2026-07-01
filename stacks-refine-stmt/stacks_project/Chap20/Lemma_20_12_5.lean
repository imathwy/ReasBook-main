import Mathlib
import stacks_project.Chap20.Lemma_20_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(RingedSpace.Hom.pushforward f).Additive]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]

-- Proof sketch: by Lemma `20.7.3`, the underlying abelian sheaf of `R^p f_* ℱ` is the
-- sheafification of the presheaf `V ↦ H^p(f⁻¹(V), ℱ)`. Lemma `20.12.3` shows these cohomology
-- groups vanish for `p > 0` when `ℱ` is flasque, so the associated sheaf is zero; hence the
-- higher direct image itself is the zero `\mathcal O_Y`-module.
/-- Lemma 20.12.5: if an `\mathcal O_X`-module on a ringed space is flasque, then every positive
higher direct image along a morphism of ringed spaces is zero. -/
theorem higherDirectImageModule_isZero_of_flasque
    (ℱ : (RingedSpace.Modules X))
    (hℱ : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (p : ℕ) (hp : 0 < p) :
    IsZero (((RingedSpace.Hom.pushforward f).rightDerived p).obj ℱ) := sorry

end AlgebraicGeometry.RingedSpace
