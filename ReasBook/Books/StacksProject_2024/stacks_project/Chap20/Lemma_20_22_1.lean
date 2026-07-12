import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Constructible
import StacksProject_2024.Chap05.Lemma_5_24_8
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

/-
Domain-style sampling for Lemma 20.22.1:
- primary domain: sheaf cohomology on spectral subspaces obtained from `nhdsKer E` and from the
  compact-open inverse systems computing those subspaces;
- sampled owner declarations:
  `TopCat.subsetInclusion`,
  `sdiffDiagram_of_compactOpenDirectedIntersection`,
  `openNeighborhoodCohomologyFunctor`,
  `spectralInverseLimit_projectionOpenCohomology_isomorphic`;
- best owner abstraction: subset embeddings should reuse `TopCat.subsetInclusion`, while the
  neighborhood-complement system in part `(2)` should keep the Chapter 5 owner
  `sdiffDiagram_of_compactOpenDirectedIntersection`, but its public cohomology diagram should be
  expressed in the fixed ambient subspace `X \ E`, where each `U \ E` is an ordinary open subset;
- primitive data: the compact-open neighborhood indexing type, the ambient complement subspace
  `X \ E`, the opens `U \ E ⊆ X \ E`, and the two subset inclusions defining the pullback sheaves
  on `nhdsKer E` and `nhdsKer E \ E`;
- derived API: the two cohomology diagrams and the restricted sheaves on `nhdsKer E`,
  `nhdsKer E \ E`, and `X \ E`.

Source/core/bridge triage:
- `source-facing`: the compact-open neighborhood system and the two cohomology comparison
  theorems for `nhdsKer E` and `nhdsKer E \ E`;
- `core/canonical`: `TopCat.subsetInclusion` and
  `spectralInverseLimit_projectionOpenCohomology_isomorphic`;
- `bridge/view`: restriction of `ℱ` to the relevant subspaces via sheaf pullback and the fixed
  ambient-open realization of `U \ E` inside `X \ E`.
-/

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]

/-- The preorder of quasi-compact open neighborhoods of `E` in `X`. -/
abbrev qcOpenNeighborhoods (E : Set X) :=
  { U : CompactOpens X // E ⊆ (U : Set X) }

/-- The inclusion of quasi-compact open neighborhoods of `E` into the lattice of open subsets of
`X`. -/
private def qcOpenNeighborhoodsToOpens (E : Set X) : qcOpenNeighborhoods E →o Opens X where
  toFun U := U.1.toOpens
  monotone' := fun _ _ hUV ↦ hUV

/-- The canonical cohomology diagram on quasi-compact open neighborhoods of `E`, ordered by
reverse inclusion, with values `U ↦ H^p(U, ℱ)`. -/
abbrev qcOpenNeighborhoodCohomologyDiagram
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (E : Set X) (p : ℕ) :
    (qcOpenNeighborhoods E)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (qcOpenNeighborhoodsToOpens E).toFunctor.op ⋙ ℱ.cohomologyPresheaf p

/-- The fixed ambient complement subspace `X \ E`. -/
abbrev ambientComplementSpace (E : Set X) :=
  TopCat.of ↥((Set.univ : Set X) \ E)

/-- The restriction of `ℱ` to the ambient complement subspace `X \ E`. -/
abbrev ambientComplementSheaf
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (E : Set X) :
    (ambientComplementSpace E).Sheaf AddCommGrpCat.{u} :=
  (pullback AddCommGrpCat.{u} (X.subsetInclusion ((Set.univ : Set X) \ E))).obj ℱ

/-- The subspace `nhdsKer E \ E` occurring in Lemma 20.22.1 (2). -/
abbrev specializingSubsetSdiffSpace (E : Set X) :=
  TopCat.of ↥(nhdsKer E \ E)

/-- The open subset `U \ E` of the fixed ambient complement subspace `X \ E` attached to a
quasi-compact open neighborhood `U` of `E`. -/
def qcOpenNeighborhoodsToAmbientComplementOpens (E : Set X) :
    qcOpenNeighborhoods E →o Opens (ambientComplementSpace E) where
  toFun U :=
    ⟨Subtype.val ⁻¹' (U.1 : Set X), U.1.isOpen.preimage continuous_subtype_val⟩
  monotone' := fun _ _ hUV _ hx ↦ hUV hx

/-- The restriction of `ℱ` to the subspace `nhdsKer E \ E`. -/
abbrev specializingSubsetSdiffSheaf
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (E : Set X) :
    (specializingSubsetSdiffSpace E).Sheaf AddCommGrpCat.{u} :=
  (pullback AddCommGrpCat.{u} (X.subsetInclusion (nhdsKer E \ E))).obj ℱ

/-- The source-facing cohomology diagram on quasi-compact open neighborhoods of `E`, ordered by
reverse inclusion, with values `U ↦ H^p(U \ E, ℱ|_{U \ E})`. Since each
`U \ E` is an open subset of the fixed ambient subspace `X \ E`, the transition
maps are the ordinary restriction maps of the cohomology presheaf on that ambient space. -/
abbrev qcOpenNeighborhoodComplementCohomologyDiagram
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (E : Set X) (p : ℕ) :
    (qcOpenNeighborhoods E)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (qcOpenNeighborhoodsToAmbientComplementOpens E).toFunctor.op ⋙
    (ambientComplementSheaf ℱ E).cohomologyPresheaf p

variable {ℱ : X.Sheaf AddCommGrpCat.{u}} {E : Set X}
variable [SpectralSpace X]

variable [HasSheafify (Opens.grothendieckTopology (TopCat.of (nhdsKer E))) AddCommGrpCat.{u}]
variable [HasExt.{u} ((TopCat.of (nhdsKer E)).Sheaf AddCommGrpCat.{u})]

-- Proof sketch: identify `nhdsKer E` with the cofiltered limit of the quasi-compact open
-- neighborhoods of `E` using Lemma `5.24.7`, then apply the inverse-limit cohomology comparison of
-- Lemma `20.19.3` to the restriction of `ℱ` along the projection maps.
/-- Lemma 20.22.1 (1): if `E ⊆ X` is quasi-compact and `W = nhdsKer E` is the subset of points
specializing to a point of `E`, then the cohomology of `ℱ|_W` is the filtered colimit of
the cohomology groups over the quasi-compact open neighborhoods of `E`. -/
@[stacks 0A3D]
theorem specializingSubset_cohomology_isomorphic_colimit_of_qcOpenNeighborhoods
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (E : Set X) (hE : IsCompact E) (p : ℕ) :
    IsIsomorphic
      (colimit (qcOpenNeighborhoodCohomologyDiagram ℱ E p))
      (((pullback AddCommGrpCat.{u} (X.subsetInclusion (nhdsKer E))).obj ℱ).H' p
        (⊤ : Opens (TopCat.of (nhdsKer E)))) := sorry

variable [HasSheafify (Opens.grothendieckTopology (specializingSubsetSdiffSpace E))
  AddCommGrpCat.{u}]
variable [HasExt.{u} ((specializingSubsetSdiffSpace E).Sheaf AddCommGrpCat.{u})]

-- Proof sketch: use Lemma `5.24.8` to identify `nhdsKer E \ E` with the inverse limit of the
-- complements `U \ E` over quasi-compact open neighborhoods `U` of `E`, and then apply the same
-- inverse-limit cohomology comparison as in part `(1)` to the source-facing neighborhood-
-- complement cohomology diagram `U ↦ H^p(U \ E, ℱ|_{U \ E})`.
/-- Lemma 20.22.1 (2): if `E ⊆ X` is constructible and `W = nhdsKer E`, then the cohomology of
`ℱ|_{W \ E}` is the filtered colimit of the cohomology groups
`H^p(U \ E, ℱ|_{U \ E})` over quasi-compact open neighborhoods `U` of
`E`. -/
@[stacks 0A3D]
theorem specializingSubset_sdiff_cohomology_isomorphic_colimit_of_qcOpenNeighborhoods
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (E : Set X) (hE : Topology.IsConstructible E)
    (p : ℕ) :
    IsIsomorphic
      (colimit (qcOpenNeighborhoodComplementCohomologyDiagram ℱ E p))
      ((specializingSubsetSdiffSheaf ℱ E).H' p
        (⊤ : Opens (specializingSubsetSdiffSpace E))) := sorry

end Sheaf
end CategoryTheory
