import Mathlib
import StacksProject_2024.Chap20.Lemma_20_10_2
import StacksProject_2024.Chap20.Lemma_20_11_11

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

-- Proof sketch: apply the Čech-to-cohomology spectral sequence of Lemma `20.11.5` to `ℱ`. By
-- Lemma `20.12.3`, all positive cohomology presheaves `\underline H^q(\mathcal F)` vanish because
-- `ℱ` is flasque, so the spectral sequence is concentrated in the `q = 0` row. The same lemma
-- also gives `H^p(U, \mathcal F) = 0` for `p > 0`, forcing the surviving row
-- `\check H^p(\mathcal U, \mathcal F)` to vanish.
/-- Lemma 20.12.4: if `\mathcal F` is a flasque `\mathcal O_X`-module on a ringed space `X`,
then for every open covering `𝒰` of `U`, the positive-degree Čech cohomology
`\check H^p(\mathcal U, \mathcal F)` vanishes. -/
theorem ringedSpaceCechCohomology_isZero_of_pos_of_flasque
    (h𝒰 : iSup (fun i ↦ (𝒰 i).left) = U)
    (ℱ : (RingedSpace.Modules X))
    (hℱ : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (p : ℕ) (hp : 0 < p) :
    IsZero
      ((ringedSpaceCechCohomologyDegree U 𝒰 p).obj.obj
        ((SheafOfModules.forget ((RingedSpace.ringCatSheaf X))).obj ℱ)) := sorry

end AlgebraicGeometry.RingedSpace
