import Mathlib
import StacksProject_2024.Chap20.Lemma_20_11_5

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

/-- The degree-`p` Čech cohomology of an `\mathcal O_X`-module for the cover `𝒰`, viewed as the
`q = 0` row of the Čech-to-cohomology spectral sequence. -/
abbrev moduleCechCohomologyAtCover
    (ℱ : (RingedSpace.Modules X)) (p : ℕ) :
    ModuleCat.{u} (X.presheaf.obj (op U)) :=
  moduleCechToCohomologyPageTwoTerm U 𝒰 ℱ p 0

-- Proof sketch: unfold `moduleCechCohomologyAtCover`; it is defined to be the `q = 0` term
-- `moduleCechToCohomologyPageTwoTerm U 𝒰 ℱ p 0`.
/-- The Čech cohomology abbreviation is the `q = 0` page-two term of the spectral sequence from
Lemma `20.11.5`. -/
theorem moduleCechCohomologyAtCover_def
    (ℱ : (RingedSpace.Modules X)) (p : ℕ) :
    moduleCechCohomologyAtCover U 𝒰 ℱ p =
      moduleCechToCohomologyPageTwoTerm U 𝒰 ℱ p 0 := sorry

-- Proof sketch: apply the spectral sequence of Lemma `20.11.5` to `ℱ`. The hypothesis implies
-- that the higher cohomology presheaves vanish on every finite intersection of the cover, so the
-- `E₂`-page is concentrated on the `q = 0` row. Hence the spectral sequence degenerates at `E₂`,
-- and the edge map identifies the `p`-th Čech cohomology with the degree-`p` cohomology on `U`.
/-- Lemma 20.11.6: if every positive-degree cohomology group of `\mathcal F` vanishes on every
finite intersection of the members of the open covering `𝒰` of `U`, then the degree-`p` Čech
cohomology of `𝒰` with coefficients in `\mathcal F` is canonically isomorphic to the degree-`p`
cohomology of `\mathcal F` on `U` as an `\mathcal O_X(U)`-module. -/
theorem moduleCechCohomologyAtCover_iso_moduleCohomologyAtOpen_of_acyclic_on_intersections
    (h𝒰 : iSup (fun i ↦ (𝒰 i).left) = U)
    (ℱ : (RingedSpace.Modules X))
    (hacyclic : ∀ q : ℕ, 0 < q → ∀ n : ℕ, ∀ σ : Fin (n + 1) → ι,
      IsZero (((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ).H' q
        (⨅ a, (𝒰 (σ a)).left)))
    (p : ℕ) :
    IsIsomorphic (moduleCechCohomologyAtCover U 𝒰 ℱ p)
      (moduleCohomologyAtOpen U ℱ p) := sorry

end AlgebraicGeometry.RingedSpace
