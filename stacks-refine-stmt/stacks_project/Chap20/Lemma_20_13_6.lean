import Mathlib
import stacks_project.Chap20.Lemma_20_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(modulePushforward f).Additive]
variable [HasInjectiveResolutions (SheafOfModules ((RingedSpace.ringCatSheaf X)))]
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every higher direct image
-- `R^q f_* ℱ` with `q > 0` vanishes, the `E₂`-page is concentrated on the `q = 0` row, so the
-- abutment identifies with the `p`-th cohomology of `f_* ℱ` on `Y`.
/-- Lemma 20.13.6 (1): if the higher direct images `R^q f_* \mathcal F` vanish for `q > 0`,
then the global degree-`p` cohomology of `\mathcal F` on `X` is canonically isomorphic to the
global degree-`p` cohomology of `f_* \mathcal F` on `Y`. -/
theorem globalCohomology_iso_pushforward_of_higherDirectImageModule_isZero
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    (hRq : ∀ q : ℕ, 0 < q → IsZero (((modulePushforward f).rightDerived q).obj ℱ))
    (p : ℕ) :
    IsIsomorphic (moduleGlobalCohomology ℱ p)
      (moduleGlobalCohomology ((modulePushforward f).obj ℱ) p) := sorry

-- Proof sketch: apply the Leray spectral sequence for `f` and `ℱ`. If every positive-degree
-- cohomology group of every higher direct image `R^q f_* ℱ` vanishes on `Y`, the `E₂`-page is
-- concentrated in the `p = 0` column, so the abutment in total degree `q` identifies with the
-- edge term `H^0(Y, R^q f_* ℱ)`.
/-- Lemma 20.13.6 (2): if `H^p(Y, R^q f_* \mathcal F) = 0` for all `q` and all `p > 0`, then
the global degree-`q` cohomology of `\mathcal F` on `X` is canonically isomorphic to the degree-`0`
cohomology of the higher direct image `R^q f_* \mathcal F` on `Y`. -/
theorem globalCohomology_iso_degreeZero_higherDirectImageModule_of_acyclicity
    (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero (moduleGlobalCohomology (((modulePushforward f).rightDerived q).obj ℱ) p))
    (q : ℕ) :
    IsIsomorphic (moduleGlobalCohomology ℱ q)
      (moduleGlobalCohomology (((modulePushforward f).rightDerived q).obj ℱ) 0) := sorry

end AlgebraicGeometry.RingedSpace
