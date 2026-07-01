import Mathlib
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Constructible

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The preorder of quasi-compact open neighborhoods of `E` in the spectral space `X`. -/
abbrev qcOpenNeighborhoods (E : Set X) :=
  { U : CompactOpens X // E ⊆ (U : Set X) }

/-- The inclusion of quasi-compact open neighborhoods of `E` into the lattice of open subsets of
`X`. -/
def qcOpenNeighborhoodsToOpens (E : Set X) : qcOpenNeighborhoods E →o Opens X where
  toFun U := U.1.toOpens
  monotone' := fun _ _ hUV ↦ hUV

/-- The canonical cohomology diagram on quasi-compact open neighborhoods of `E`, ordered by
reverse inclusion, with values `U ↦ H^p(U, \mathcal F)`. -/
abbrev qcOpenNeighborhoodCohomologyDiagram
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) (p : ℕ) :
    (qcOpenNeighborhoods E)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (qcOpenNeighborhoodsToOpens E).toFunctor.op ⋙ ℱ.cohomologyPresheaf p

/-- The inclusion `nhdsKer E ↪ X` of the specializing subset of `E` into the ambient spectral
space. -/
abbrev specializingSubsetInclusion (E : Set X) :
    TopCat.of ↥(nhdsKer E) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of an abelian sheaf on `X` to the specializing subset `nhdsKer E`. -/
abbrev specializingSubsetSheaf
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) :
    (TopCat.of ↥(nhdsKer E)).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} (specializingSubsetInclusion E)).obj ℱ

/-- The inclusion `(nhdsKer E \ E) ↪ X` of the complement of `E` inside its specializing subset. -/
abbrev specializingSubsetSDiffInclusion (E : Set X) :
    TopCat.of ↥((nhdsKer E \ E : Set X)) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of an abelian sheaf on `X` to the spectral subspace `nhdsKer E \ E`. -/
abbrev specializingSubsetSDiffSheaf
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) :
    (TopCat.of ↥((nhdsKer E \ E : Set X))).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} (specializingSubsetSDiffInclusion E)).obj ℱ

/-- The inclusion `(U \ E) ↪ X` for a quasi-compact open neighborhood `U` of `E`. -/
abbrev neighborhoodComplementInclusion
    (E : Set X) (U : qcOpenNeighborhoods E) :
    TopCat.of ↥((((U.1 : Set X) \ E : Set X))) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of an abelian sheaf on `X` to the locally closed complement `U \ E` inside a
quasi-compact open neighborhood `U` of `E`. -/
abbrev neighborhoodComplementSheaf
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) (U : qcOpenNeighborhoods E) :
    (TopCat.of ↥((((U.1 : Set X) \ E : Set X)))).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} (neighborhoodComplementInclusion E U)).obj ℱ

variable {ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}} {E : Set X}

variable [HasSheafify (Opens.grothendieckTopology ↥(nhdsKer E)) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology ↥(nhdsKer E)) AddCommGrpCat.{u})]

-- Proof sketch: identify `nhdsKer E` with the cofiltered limit of the quasi-compact open
-- neighborhoods of `E` using Lemma `5.24.7`, then apply the inverse-limit cohomology comparison of
-- Lemma `20.19.3` to the restriction of `ℱ` along the projection maps.
/-- Lemma 20.22.1 (1): if `E ⊆ X` is quasi-compact and `W = nhdsKer E` is the subset of points
specializing to a point of `E`, then the cohomology of `\mathcal F|_W` is the filtered colimit of
the cohomology groups over the quasi-compact open neighborhoods of `E`. -/
theorem specializingSubset_cohomology_isomorphic_colimit_of_qcOpenNeighborhoods
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) (hE : IsCompact E) (p : ℕ)
    [HasColimit (qcOpenNeighborhoodCohomologyDiagram ℱ E p)] :
    IsIsomorphic
      (colimit (qcOpenNeighborhoodCohomologyDiagram ℱ E p))
      ((specializingSubsetSheaf ℱ E).H' p (⊤ : Opens ↥(nhdsKer E))) := sorry

variable [HasSheafify (Opens.grothendieckTopology ↥((nhdsKer E \ E : Set X)))
  AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology ↥((nhdsKer E \ E : Set X)))
  AddCommGrpCat.{u})]

-- Proof sketch: use Lemma `5.24.8` to identify `nhdsKer E \ E` with the inverse limit of the
-- complements `U \ E` over quasi-compact open neighborhoods `U` of `E`, and then apply the same
-- inverse-limit cohomology comparison as in part `(1)` to any chosen diagram realizing the groups
-- `H^p(U \ E, \mathcal F|_{U \ E})`.
/-- Lemma 20.22.1 (2): if `E ⊆ X` is constructible and `W = nhdsKer E`, then the cohomology of
`\mathcal F|_{W \setminus E}` is the filtered colimit of the cohomology groups
`H^p(U \setminus E, \mathcal F|_{U \setminus E})` over quasi-compact open neighborhoods `U` of
`E`, expressed using a chosen neighborhood-complement cohomology diagram. -/
theorem specializingSubset_sdiff_cohomology_isomorphic_colimit_of_qcOpenNeighborhoods
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) (hE : Topology.IsConstructible E)
    (p : ℕ)
    (D : (qcOpenNeighborhoods E)ᵒᵖ ⥤ AddCommGrpCat.{u}) [HasColimit D]
    (hD :
      ∀ U : qcOpenNeighborhoods E,
        IsIsomorphic
          (D.obj (Opposite.op U))
          ((neighborhoodComplementSheaf ℱ E U).H' p
            (⊤ : Opens ↥((((U.1 : Set X) \ E : Set X)))))) :
    IsIsomorphic
      (colimit D)
      ((specializingSubsetSDiffSheaf ℱ E).H' p
        (⊤ : Opens ↥((nhdsKer E \ E : Set X)))) := sorry

end Sheaf
end CategoryTheory
