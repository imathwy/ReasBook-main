import Mathlib.CategoryTheory.IsomorphismClasses

open CategoryTheory

noncomputable section

namespace SheafOfModules.RingedSite

section TensorComparison

variable {ModGrA : Type*} [Category ModGrA]
variable {ModGrAU : Type*} [Category ModGrAU]
variable {ModGrB : Type*} [Category ModGrB]
variable {ModGrBU : Type*} [Category ModGrBU]
variable {BimodGrAB : Type*} [Category BimodGrAB]
variable {BimodGrAUBU : Type*} [Category BimodGrAUBU]
variable (tensorAmbient : ModGrA → BimodGrAB → ModGrB)
variable (tensorLocalized : ModGrAU → BimodGrAUBU → ModGrBU)
variable (extensionByZeroLeft : ModGrAU ⥤ ModGrA)
variable (extensionByZeroRight : ModGrBU ⥤ ModGrB)
variable (restrictionBimodule : BimodGrAB ⥤ BimodGrAUBU)

-- Owner/API choice note: the chapter-level localized tensor comparison only needs the ambient and
-- localized tensor operations together with the two extension-by-zero functors and the bimodule
-- restriction functor. In the concrete Chapter 18/24 setting, these inputs come from the
-- localized lower-shriek/restriction owners and the graded tensor owner.

/- Source/core/bridge triage for Lemma 24.10.2:
- `source-facing`: the localized graded tensor comparison statement
  `j_{U!}\mathcal M \otimes_{\mathcal A} \mathcal N \cong
    j_{U!}(\mathcal M \otimes_{\mathcal A_U} \mathcal N|_U)`;
- `core/canonical`: the ambient tensor operation, the localized tensor operation, the two
  extension-by-zero functors, and the bimodule restriction functor;
- `bridge/view`: the comparison is kept at the proposition-level owner `IsIsomorphic`, since the
  present generic inputs do not yet determine a canonical comparison morphism term.

This file therefore keeps the source-facing comparison surface directly, without introducing a new
packaged owner. The Chapter 18 localization functors and Chapter 24 tensor owner instantiate this
API in the intended ringed-site setting. -/

/-- Lemma 24.10.2: for fixed ambient/localized tensor and localization operators, the source
comparison
`j_{U!}\mathcal M \otimes_{\mathcal A} \mathcal N \cong
  j_{U!}(\mathcal M \otimes_{\mathcal A_U} \mathcal N|_U)`.

The public statement stays on the explicit source and target tensor objects, using the
proposition-level owner `IsIsomorphic`, because the ambient data here does not determine a
canonical comparison isomorphism term. -/
theorem gradedExtensionByZeroTensorRestrictionComparison
    (ℳ : ModGrAU) (𝒩 : BimodGrAB) :
    IsIsomorphic
      (tensorAmbient (extensionByZeroLeft.obj ℳ) 𝒩)
      (extensionByZeroRight.obj
        (tensorLocalized ℳ (restrictionBimodule.obj 𝒩))) := by
  sorry

/-- The comparison of Lemma 24.10.2 in the reverse direction, obtained by symmetry of
`CategoryTheory.IsIsomorphic`. -/
theorem gradedExtensionByZeroTensorRestrictionComparison_symm
    (ℳ : ModGrAU) (𝒩 : BimodGrAB) :
    IsIsomorphic
      (extensionByZeroRight.obj
        (tensorLocalized ℳ (restrictionBimodule.obj 𝒩)))
      (tensorAmbient (extensionByZeroLeft.obj ℳ) 𝒩) := by
  simpa using
    (gradedExtensionByZeroTensorRestrictionComparison
      tensorAmbient tensorLocalized extensionByZeroLeft extensionByZeroRight
      restrictionBimodule ℳ 𝒩).symm

end TensorComparison

end SheafOfModules.RingedSite
