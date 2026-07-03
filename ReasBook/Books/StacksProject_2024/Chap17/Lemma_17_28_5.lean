import Mathlib
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.Chap17.Lemma_17_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open TopCat.Sheaf

noncomputable section

universe u

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.28.5:
- primary domain: restriction of sheaves of relative differentials to an open subset;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `TopCat.Sheaf.pullback`,
  `moduleSheafRestrictionToOpen`;
- best owner abstraction: the owner-level inverse-image comparison
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`, with this file keeping only the
  open-inclusion specialization written through the Chapter 6 restriction functor;
- primitive data: the owner `relativeDifferentials` and the canonical restriction functor
  `moduleSheafRestrictionToOpen`;
- derived API: the restriction comparison theorem below.

Source/core/bridge triage:
- `core/canonical`: `TopCat.Sheaf.relativeDifferentials` and its generic inverse-image comparison
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`;
- `bridge/view`: this file rewrites that generic comparison for the open inclusion
  `U.inclusion'` and the source-facing restriction functor notation;
- the former local pullback/sheafification transport lemmas duplicated the owner theorem from
  Lemma `17.28.6`, so they should be deleted rather than maintained in parallel. -/

/-- Lemma 17.28.5: for an open subset `U ⊆ X`, the restriction of the sheaf of relative
differentials `Ω(φ)` is canonically isomorphic to the canonical relative-differentials owner for
the restricted morphism, specialized from
`TopCat.Sheaf.inverseImage_relativeDifferentialsIso` along the open inclusion `U ↪ X`. -/

theorem sheaf_relative_differentials_restrict_isIsomorphic
    (U : Opens X) {O₁ O₂ : TopCat.Sheaf CommRingCat.{u} X} (φ : O₁ ⟶ O₂) :
    IsIsomorphic ((moduleSheafRestrictionToOpen U (ringSheaf O₂)).obj Ω(φ))
      ((SheafOfModules.restrictScalars
          (pullbackRingSheafIso U.inclusion' O₂).inv).obj
        Ω((pullback CommRingCat.{u} U.inclusion').map φ)) := by
  exact ⟨by
    simpa [moduleSheafRestrictionToOpen] using
      inverseImage_relativeDifferentialsIso U.inclusion' φ⟩
