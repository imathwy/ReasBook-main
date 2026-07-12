import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.Chap06.ClosedSubsetInclusion

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits
open TopCat.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}}

/-- The object property selecting open neighbourhoods of a subset `Z ⊆ X`. -/
def openNeighborhoodProperty (Z : Set X) : ObjectProperty (Opens X) :=
  fun U ↦ Z ⊆ U

/-- The category of open neighbourhoods of `Z` in `X`, ordered by reverse inclusion. -/
abbrev OpenNeighborhoodCat (Z : Set X) :=
  (openNeighborhoodProperty Z).FullSubcategoryᵒᵖ

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (X.Sheaf AddCommGrpCat.{u})]

/-- The cohomology diagram on open neighbourhoods of `Z`, ordered by reverse inclusion, with
values `U ↦ H^p(U, 𝓕)`. -/
abbrev openNeighborhoodCohomologyDiagram (Z : Set X)
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    OpenNeighborhoodCat Z ⥤ AddCommGrpCat.{u} :=
  (openNeighborhoodProperty Z).ι.op ⋙ ℱ.cohomologyPresheaf p

variable (Z : Set X)
variable [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
variable [HasExt ((TopCat.of Z).Sheaf AddCommGrpCat.{u})]
variable (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)

-- Proof sketch: for `p = 0`, sections on the subspace `Z` come from sections on some open
-- neighbourhood of `Z`, and compactness plus pairwise ambient separation lets one refine and glue
-- these local extensions. For higher degrees, resolve by injective sheaves, use the compact
-- Hausdorff-type hypothesis on `Z` to obtain vanishing of higher cohomology on the restricted
-- injectives, and conclude by dimension shifting exactly as in the text.
/-- Lemma 20.16.3: if `Z ⊆ X` is quasi-compact and any two points of `Z` admit disjoint open
neighbourhoods in `X`, then for every abelian sheaf `ℱ` on `X` and every degree `p`, the filtered
colimit of the cohomology groups `H^p(U, 𝓕)` over open neighbourhoods `U` of `Z` is
canonically isomorphic to the cohomology of the pullback sheaf on the subspace `Z`. -/
@[stacks 09V3]
theorem openNeighborhoodCohomology_isomorphic_subspaceCohomology_of_compact_ambiently_separated
    (hZqc : IsCompact Z)
    (hZsep : ∀ x y : Z, x ≠ y → SeparatedNhds ({x.1} : Set X) {y.1}) :
    IsIsomorphic
      (colimit (openNeighborhoodCohomologyDiagram Z ℱ p))
      (((pullback AddCommGrpCat.{u} (X.subsetInclusion Z)).obj ℱ).H' p
        (⊤ : Opens (TopCat.of Z))) := sorry

end Sheaf
end CategoryTheory
