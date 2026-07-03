import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}}

/-- The object property selecting open neighbourhoods of a subset `Z ⊆ X`. -/
def openNeighborhoodProperty (Z : Set X) : CategoryTheory.ObjectProperty (Opens X) :=
  fun U ↦ Z ⊆ U

/-- The opposite category of open neighbourhoods of `Z` in `X`. -/
abbrev OpenNeighborhoodCat (Z : Set X) :=
  (openNeighborhoodProperty Z).FullSubcategoryᵒᵖ

/-- The inclusion of the subspace `Z` into the ambient space `X`. -/
abbrev subsetInclusion (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (X.Sheaf AddCommGrpCat.{u})]

/-- The diagram of degree-`p` cohomology groups over the open neighbourhoods of `Z`. -/
def openNeighborhoodCohomologyFunctor (Z : Set X)
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    OpenNeighborhoodCat Z ⥤ AddCommGrpCat.{u} :=
  (openNeighborhoodProperty Z).ι.op ⋙ ℱ.cohomologyPresheaf p

variable (Z : Set X)
variable [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
variable [HasExt ((TopCat.of Z).Sheaf AddCommGrpCat.{u})]

-- Proof sketch: for `p = 0`, sections on the subspace `Z` come from sections on some open
-- neighbourhood of `Z`, and compactness plus pairwise ambient separation lets one refine and glue
-- these local extensions. For higher degrees, resolve by injective sheaves, use the compact
-- Hausdorff-type hypothesis on `Z` to obtain vanishing of higher cohomology on the restricted
-- injectives, and conclude by dimension shifting exactly as in the text.
/-- Lemma 20.16.3: if `Z ⊆ X` is quasi-compact and any two points of `Z` admit disjoint open
neighbourhoods in `X`, then for every abelian sheaf `ℱ` on `X` and every degree `p`, the filtered
colimit of the cohomology groups `H^p(U, \mathcal F)` over open neighbourhoods `U` of `Z` is
canonically isomorphic to the cohomology of the pullback sheaf on the subspace `Z`. -/
theorem openNeighborhoodCohomology_isomorphic_subspaceCohomology_of_compact_ambiently_separated
    (hZqc : IsCompact Z)
    (hZsep : ∀ x y : Z, x ≠ y → SeparatedNhds ({x.1} : Set X) {y.1})
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    [HasColimit (openNeighborhoodCohomologyFunctor Z ℱ p)] :
    IsIsomorphic
      (colimit (openNeighborhoodCohomologyFunctor Z ℱ p))
      (((TopCat.Sheaf.pullback AddCommGrpCat.{u} (subsetInclusion Z)).obj ℱ).H' p
        (⊤ : Opens (TopCat.of Z))) := sorry

end Sheaf
end CategoryTheory
