import Mathlib
import StacksProject_2024.Chap30.Lemma_30_2_2

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the affine-open cover owners but no lighter
-- already-built comparison-map owner. The source-facing statement is therefore kept on the
-- Chapter 30 Čech cohomology owner and mathlib sheaf cohomology owner, specialized to `X`.

/-- Lemma 30.2.6: if `X` admits an open covering whose every finite intersection is affine open,
then for any quasi-coherent `\mathcal O_X`-module `\mathcal F` and any degree `p`, the
Čech cohomology of that cover on `X` identifies with the cohomology of the underlying additive
sheaf. -/
@[stacks 01XD]
theorem moduleCechCohomology_isomorphic_cohomology_of_affineIntersections
    [HasInjectiveResolutions X.Modules]
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {ι : Type u} (𝒰 : ι → X.Opens) (h𝒰 : iSup 𝒰 = ⊤)
    (hAffine : ∀ n : ℕ, ∀ σ : Fin (n + 1) → ι, IsAffineOpen (⨅ a, 𝒰 (σ a)))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ) :
    IsIsomorphic (RingedSpace.moduleCechCohomology 𝒰 ℱ p)
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p (⊤ : X.Opens)) := sorry

end AlgebraicGeometry.Scheme
