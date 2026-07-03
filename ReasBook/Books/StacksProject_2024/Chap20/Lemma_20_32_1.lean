import Mathlib
import StacksProject_2024.Chap13.Lemma_13_31_9
import StacksProject_2024.Chap20.Lemma_20_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.32.1:
- primary domain: restriction and extension by zero for sheaves of modules on a ringed space,
  together with preservation of `CochainComplex.IsKInjective` under an exact-adjunction pair;
- sampled owner declarations:
  `moduleSheafExtensionByZeroFromOpen`,
  `moduleRestrictionToOpen`,
  `openSubspaceModuleCategory`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstractions:
  `moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)` for `j_{U!}`,
  `moduleRestrictionToOpen X U` for `j^{-1}`,
  `openSubspaceModuleCategory X U` for the localized module category;
- primitive data: only the ringed space `X`, the open subset `U`, and the K-injective complex
  `I`;
- derived API: exactness of `j_{U!}` and K-injectivity of the restricted complex.

Source/core/bridge triage:
- `source-facing`: exactness of extension by zero on `\mathcal O_U`-modules and preservation of
  K-injectivity under restriction to `U`;
- `core/canonical`: the Chapter 6 functors `moduleSheafExtensionByZeroFromOpen` and
  `moduleRestrictionToOpen`, the Chapter 20 owner `openSubspaceModuleCategory`, and the Chapter 13
  K-injective preservation theorem;
- `bridge/view`: this file is the ringed-space specialization of that generic exact-adjunction
  owner theorem, so it should reuse those owners directly instead of introducing parallel ambient
  and localized module-category aliases. -/

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

-- Proof sketch: extension by zero on `\mathcal O_U`-modules is left adjoint to restriction by
-- Lemma `6.31.8`. On underlying abelian sheaves, this is the usual exact extension-by-zero
-- functor from Lemma `17.3.4`; exactness lifts to module sheaves because the module forgetful
-- functor is exact and reflects finite limits and colimits.
/-- Extension by zero from an open subspace of a ringed space is exact on module sheaves. -/
theorem moduleSheafExtensionByZeroFromOpen_exact :
    exactFunctor (openSubspaceModuleCategory X U) (RingedSpace.Modules X)
      (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) := sorry

-- Proof sketch: restriction to the open subspace `U` is right adjoint to extension by zero by
-- Lemma `6.31.8`, and the left adjoint is exact by
-- `moduleSheafExtensionByZeroFromOpen_exact`. Apply Lemma `13.31.9` to the induced functors on
-- cochain complexes.
/-- Lemma 20.32.1: if `X` is a ringed space, `U ⊆ X` is open, and `I` is a K-injective complex
of `\mathcal O_X`-modules, then the restricted complex `I|_U` is K-injective as a complex of
`\mathcal O_U`-modules. -/
theorem moduleRestrictionToOpen_isKInjective
    (I : CochainComplex (RingedSpace.Modules X) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective (((moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)).obj I) := by
  let adj := moduleSheafExtensionByZeroAdjunction U (RingedSpace.ringCatSheaf X)
  letI : (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).Additive :=
    adj.left_adjoint_additive
  simpa using
    CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (moduleRestrictionToOpen X U)
      (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X))
      adj
      (moduleSheafExtensionByZeroFromOpen_exact (X := X) U)
      I

end

end AlgebraicGeometry.RingedSpace
