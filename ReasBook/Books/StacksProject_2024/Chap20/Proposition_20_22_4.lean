import Mathlib
import StacksProject_2024.Chap17.Lemma_17_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped ClosedSubsetSectionsWithSupport

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}} [SpectralSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]

/-- The cohomology of an abelian sheaf on `X` with support in a closed subset `Z`, modeled as the
ordinary cohomology of the sheaf of sections with support on the subspace `Z`. -/
noncomputable abbrev closedSubsetCohomologyWithSupport
    {Z : Set X} (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
    [HasExt.{u} ((TopCat.of Z).Sheaf AddCommGrpCat.{u})] :
    AddCommGrpCat.{u} :=
  ((𝓗[hZ]).obj F).H' q
    (⊤ : Opens (TopCat.of Z))

-- Proof sketch: unfold `closedSubsetCohomologyWithSupport`; it is defined to be the degree-`q`
-- cohomology of the sheaf of sections with support in `Z` on the closed subspace.
/-- The support-cohomology abbreviation is given by sheaf cohomology of the sections-with-support
sheaf on the closed subspace. -/
theorem closedSubsetCohomologyWithSupport_def
    {Z : Set X} (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
    [HasExt.{u} ((TopCat.of Z).Sheaf AddCommGrpCat.{u})] :
    closedSubsetCohomologyWithSupport hZ F q =
      (((𝓗[hZ]).obj F).H' q
        (⊤ : Opens (TopCat.of Z))) := sorry

-- Proof sketch: this is the induction-on-dimension vanishing statement proved in the text; the
-- base case uses profinite vanishing and the inductive step uses the surjectivity statement in
-- part `(2)` together with Leray acyclicity for the image sheaf occurring in an injective
-- resolution.
/-- Proposition 20.22.4 (1): if `X` is a spectral space of Krull dimension `d`, then every
abelian sheaf on `X` has vanishing global cohomology in degrees strictly larger than `d`. -/
theorem isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_eq
    (d : ℕ) (hXdim : topologicalKrullDim X = d) (F : X.Sheaf AddCommGrpCat.{u}) {q : ℕ}
    (hq : d < q) :
    IsZero (F.H' q (⊤ : Opens ↑X)) := sorry

-- Proof sketch: let `Z = X \ U` and consider the specializing locus `W` of `Z`. By the
-- colimit description from Lemma `20.22.1`, the restriction of a class in `H^d(U, F)` to
-- `W \ Z` vanishes after shrinking around `Z`; Mayer-Vietoris for the cover `X = U ∪ V` then
-- lifts the class to `H^d(X, F)`.
/-- Proposition 20.22.4 (2): if `X` is a spectral space of Krull dimension `d`, then for every
quasi-compact open subset `U ⊆ X` the restriction map `H^d(X, \mathcal F) → H^d(U, \mathcal F)`
is surjective. -/
theorem surjective_restriction_topCohomology_to_compactOpen_of_spectralSpace_of_topologicalKrullDim_eq
    (d : ℕ) (hXdim : topologicalKrullDim X = d) (F : X.Sheaf AddCommGrpCat.{u})
    (U : CompactOpens ↑X) :
    Function.Surjective
      (((F.cohomologyPresheaf d).map
          (homOfLE
            (show U.toOpens ≤ (⟨Set.univ, isOpen_univ⟩ : Opens ↑X) from
              fun _ _ ↦ Set.mem_univ _)).op) :
        F.H' d (⊤ : Opens ↑X) ⟶ F.H' d U.toOpens) := sorry

-- Proof sketch: apply the long exact sequence for cohomology with support of the pair
-- `(X, X \ Z)`. Since `Z` is constructible and closed, the complement `X \ Z` is again a
-- quasi-compact open spectral subspace of dimension at most `d`; combine part `(1)` on `X` and on
-- `X \ Z` with the surjectivity from part `(2)` to force the supported cohomology to vanish in
-- degrees above `d`.
/-- Proposition 20.22.4 (3): if `X` is a spectral space of Krull dimension `d`, then for every
constructible closed subset `Z ⊆ X` the cohomology with support in `Z` vanishes in degrees
strictly larger than `d`. -/
theorem isZero_higherClosedSubsetCohomologyWithSupport_of_spectralSpace_of_topologicalKrullDim_eq
    (d : ℕ) (hXdim : topologicalKrullDim X = d) (F : X.Sheaf AddCommGrpCat.{u})
    {Z : Set X} (hZclosed : IsClosed Z) (hZconstructible : Topology.IsConstructible Z) {q : ℕ}
    (hq : d < q)
    [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
    [HasExt.{u} ((TopCat.of Z).Sheaf AddCommGrpCat.{u})] :
    IsZero (closedSubsetCohomologyWithSupport hZclosed F q) := sorry

end Sheaf
end CategoryTheory
