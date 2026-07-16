import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Constructible
import StacksProject_2024.stacks_project.Chap17.Lemma_17_6_3
import StacksProject_2024.stacks_project.Chap20.Lemma_20_22_3

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
variable (d : ℕ) (F : X.Sheaf AddCommGrpCat.{u})

/- Domain-style sampling for Proposition 20.22.4:
- primary domain: higher cohomology of abelian sheaves on spectral spaces, bounded by topological
  Krull dimension, together with the closed-support functor on constructible closed subsets;
- sampled owner declarations:
  `topologicalKrullDim`,
  `CategoryTheory.Sheaf.H'`,
  `CategoryTheory.Sheaf.cohomologyPresheaf`,
  `𝓗[hZ]`;
- best owner abstraction: the cohomology objects should stay on the canonical owner `F.H' p U`,
  the degree-`d` restriction map should stay the canonical `cohomologyPresheaf` map on the
  inclusion of opens, and cohomology with support should use the chapter's existing owner
  `𝓗[hZ]` rather than a local wrapper around supported sections;
- primitive data: the spectral space `X`, the dimension bound, the sheaf `F`, the compact open
  `U`, and the constructible closed subset `Z`;
- derived API: the vanishing objects `F.H' q (⊤ : Opens X)`,
  the canonical restriction morphism `F.H' d (⊤ : Opens X) ⟶ F.H' d (U : Opens X)`,
  and the supported cohomology object `((𝓗[hZ]).obj F).H' q (⊤ : Opens (TopCat.of Z))`.

Source/core/bridge triage:
- `source-facing`: the three proposition statements;
- `core/canonical`: `topologicalKrullDim`, `Sheaf.H'`, `Sheaf.cohomologyPresheaf`, and `𝓗[hZ]`;
- `bridge/view`: evaluation of the cohomology presheaf on the inclusion `(U : Opens X) ⟶ ⊤`, and
  restriction of `F` to the closed subspace through `𝓗[hZ]`.

This file therefore keeps the proposition itself as the source-facing owner, while reusing the
chapter's existing cohomology and closed-support owners directly.
-/

-- Proof sketch: this is the induction-on-dimension vanishing statement proved in the text; the
-- base case uses profinite vanishing and the inductive step uses the surjectivity statement in
-- part `(2)` together with Leray acyclicity for the image sheaf occurring in an injective
-- resolution.
/-- Proposition 20.22.4 (1): if `X` is a spectral space of Krull dimension at most `d`, then every
abelian sheaf on `X` has vanishing global cohomology in degrees strictly larger than `d`. -/
@[stacks 0A3G]
theorem isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_le
    (hXdim : topologicalKrullDim X ≤ d) {q : ℕ} (hq : d < q) :
    IsZero (F.H' q (⊤ : Opens X)) := sorry

-- Proof sketch: let `Z = X \ U` and consider the specializing locus `W` of `Z`. By the
-- colimit description from Lemma `20.22.1`, the restriction of a class in `H^d(U, F)` to
-- `W \ Z` vanishes after shrinking around `Z`; Mayer-Vietoris for the cover `X = U ∪ V` then
-- lifts the class to `H^d(X, F)`.
/-- Proposition 20.22.4 (2): if `X` is a spectral space of Krull dimension at most `d`, then for
every quasi-compact open subset `U ⊆ X` the restriction map
`H^d(X, F) ⟶ H^d(U, F)` is surjective. -/
@[stacks 0A3G]
theorem surjective_restriction_cohomology_to_compactOpen_of_spectralSpace_of_topologicalKrullDim_le
    (hXdim : topologicalKrullDim X ≤ d) (U : CompactOpens X) :
    Function.Surjective
      (((F.cohomologyPresheaf d).map (homOfLE le_top).op) :
        F.H' d (⊤ : Opens X) ⟶ F.H' d U.toOpens) := sorry

-- Proof sketch: apply the long exact sequence for cohomology with support of the pair
-- `(X, X \ Z)`. Since `Z` is constructible and closed, the complement `X \ Z` is again a
-- quasi-compact open spectral subspace of dimension at most `d`; combine part `(1)` on `X` and on
-- `X \ Z` with the surjectivity from part `(2)` to force the supported cohomology to vanish in
-- degrees above `d`.
/-- Proposition 20.22.4 (3): if `X` is a spectral space of Krull dimension at most `d`, then for
every constructible closed subset `Z ⊆ X` the cohomology with support in `Z` vanishes in degrees
strictly larger than `d`. -/
@[stacks 0A3G]
theorem isZero_higherClosedSubsetCohomologyWithSupport_of_spectralSpace_of_topologicalKrullDim_le
    {Z : Set X} (hZclosed : IsClosed Z) (hZconstructible : Topology.IsConstructible Z)
    (hXdim : topologicalKrullDim X ≤ d) {q : ℕ} (hq : d < q)
    [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
    [HasExt.{u} ((TopCat.of Z).Sheaf AddCommGrpCat.{u})] :
    IsZero (((𝓗[hZclosed]).obj F).H' q (⊤ : Opens (TopCat.of Z))) := sorry

end Sheaf
end CategoryTheory
