import Mathlib
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
import StacksProject_2024.Chap17.Lemma_17_28_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open TopCat.Sheaf

noncomputable section

universe u

variable {X : TopCat.{u}}

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 17.28.5:
- primary domain: restriction of sheaves of relative differentials to an open subset;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferential`,
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `moduleSheafRestrictionToOpen`;
- best owner abstraction: the Chapter 17 inverse-image comparison
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`, specialized to the open inclusion
  `U.inclusion'`;
- primitive data: the owner `Ω(φ)`, its universal derivation `relativeDifferential φ`, and the
  open-inclusion restriction functor `moduleSheafRestrictionToOpen`;
- derived API: the restriction isomorphism and its sectionwise compatibility with universal
  differentials.

Source/core/bridge triage:
- `source-facing`: restriction of `Ω(φ)` and of the universal derivation `d : O₂ → Ω(φ)` to the
  open subset `U`;
- `core/canonical`: `Ω(φ)`, `relativeDifferential φ`, and
  `inverseImage_relativeDifferentialsIso`;
- `bridge/view`: open restriction is inverse image along `U.inclusion'`, expressed in this chapter
  by `moduleSheafRestrictionToOpen`.

This file should therefore expose the open-subset specialization as a direct use of the canonical
comparison isomorphism together with the sectionwise formula on `d`, rather than by introducing a
parallel local owner. -/

variable (U : Opens X) {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂)

/- Lemma 17.28.5: for an open subset `U ⊆ X`, the restriction of `Ω(φ)` to `U` is exactly the
specialization of `inverseImage_relativeDifferentialsIso` to the open inclusion `U.inclusion'`,
viewed through the chapter’s owner `moduleSheafRestrictionToOpen`. -/
#check
  ((inverseImage_relativeDifferentialsIso U.inclusion' φ) :
    (moduleSheafRestrictionToOpen U (ringSheaf O₂)).obj Ω(φ) ≅
      (SheafOfModules.restrictScalars (pullbackRingSheafIso U.inclusion' O₂).inv).obj
        Ω((pullback CommRingCat.{u} U.inclusion').map φ))

/-- Lemma 17.28.5: the canonical restriction comparison for relative differentials along the open
inclusion `U.inclusion'` is exactly the Chapter 17 inverse-image comparison property specialized
to that inclusion. -/
@[stacks 08RQ]
theorem restrictionToOpen_relativeDifferentialsIso_characterizing :
    inverseImage_relativeDifferentialsComparisonProperty U.inclusion' φ
      (inverseImage_relativeDifferentialsIso U.inclusion' φ).hom :=
  inverseImage_relativeDifferentialsIso_characterizing U.inclusion' φ

end TopCat.Sheaf
