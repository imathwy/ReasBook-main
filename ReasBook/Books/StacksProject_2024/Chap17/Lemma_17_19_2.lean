import Mathlib
import StacksProject_2024.Chap17.«17_19_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty TopCat TopologicalSpace
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.19.2:
- primary domain: filtered-colimit presentations of set-valued sheaves by finite coequalizers of
  lower-shriek constant sheaves;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.ind`,
  `ColimitPresentation`,
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `j![U, S]`;
- best owner abstraction: the filtered-colimit statement itself should use the canonical owner
  `CategoryTheory.ObjectProperty.ind` applied to the source-facing stagewise predicate
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (· ∈ B)`, rather than
  restating the `ColimitPresentation` witness data explicitly in the theorem surface;
- primitive data: a filtered colimit presentation of `ℱ`;
- derived API: the `ObjectProperty.ind` packaging of that presentation together with the stagewise
  owner predicate for the diagram objects.

Source/core/bridge triage:
- `source-facing`: the filtered-colimit presentation relative to the basis `B`;
- `core/canonical`: `CategoryTheory.ObjectProperty.ind` applied to the owner from `17.19.2.1`;
- `bridge/view`: the later spectral-space consequences deduced from that stagewise owner.
-/

-- Proof sketch: start from the epimorphic coproduct presentation of Lemma `17.19.1`, apply the
-- same construction to the kernel pair, and then restrict to finite subdiagrams. Quasi-compactness
-- of the basis opens and Lemma `6.29.1` let sections over the relevant opens commute with the
-- filtered colimit, so the resulting finite coequalizer stages indexed by finite subsets form a
-- filtered colimit presentation of `ℱ`.
/-- Lemma 17.19.2: if `X` has a basis `B` of quasi-compact opens, then every sheaf of sets on `X`
is a filtered colimit of sheaves admitting finite coequalizer presentations by lower-shriek
constant sheaves on members of `B` with finite fibres. We state this in the canonical owner form
`ObjectProperty.ind` applied to
`HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (· ∈ B)`. -/
theorem exists_filteredColimitPresentation_by_finite_basis_open_extensionByZeroConstantSheaf_coequalizers
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    (ℱ : Sh(X)) :
    ind
      (HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (· ∈ B))
      ℱ := sorry

end
