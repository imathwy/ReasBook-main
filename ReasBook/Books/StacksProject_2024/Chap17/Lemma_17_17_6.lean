import Mathlib
import StacksProject_2024.Chap06.Lemma_6_31_8
import StacksProject_2024.Chap17.Lemma_17_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopCat
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

/- Domain-style sampling for Lemma 17.17.6:
- primary domain: extension by zero for sheaves of modules on a ringed space, specialized to the
  structure sheaf on an open subspace, together with flatness of the resulting `\mathcal O_X`-module;
- sampled owner declarations:
  `moduleSheafExtensionByZeroFromOpen`,
  `openSubsetModuleSheafExtensionByZero`,
  `openSubsetModuleSheafExtensionByZero_eq_moduleSheafExtensionByZeroFromOpen`,
  `SheafOfModules.RingedSite.IsFlat`;
- best owner abstraction: the chapter-level owner for module-valued extension by zero is the
  canonical left adjoint `moduleSheafExtensionByZeroFromOpen`; the explicit
  `openSubsetModuleSheafExtensionByZero` construction is a source-facing bridge already identified
  with that owner in Chapter 6;
- primitive data: an open subset `U ⊆ X`;
- derived API: the specific lower-shriek structure module `structureSheafLowerShriek U =
  j_{U!}\mathcal O_U` and its flatness statement.

Source/core/bridge triage:
- `source-facing`: the module sheaf `j_{U!}\mathcal O_U` and the claim that it is flat;
- `core/canonical`: `moduleSheafExtensionByZeroFromOpen` and
  `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the explicit Chapter-6 `openSubsetModuleSheafExtensionByZero` model.

This file should therefore keep the source-facing owner `j_{U!}\mathcal O_U` as the short public
surface `structureSheafLowerShriek U`, defined using the canonical extension-by-zero owner rather
than by repeating the explicit Chapter-6 bridge term.
-/

/-- The lower-shriek structure sheaf `j_{U!}\mathcal O_U` attached to an open subspace
`U ⊆ X`, viewed as an `\mathcal O_X`-module sheaf. -/
noncomputable abbrev structureSheafLowerShriek
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    SheafOfModules (ringCatSheaf X) :=
  (moduleSheafExtensionByZeroFromOpen U (ringCatSheaf X)).obj
    (SheafOfModules.unit
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (ringCatSheaf X)))

-- Proof sketch: by Lemma 17.17.2 it is enough to check flatness stalkwise. If `x ∈ U`, the
-- stalk of `j_{U!}\mathcal O_U` identifies with `\mathcal O_{U,x} \cong \mathcal O_{X,x}` by the
-- extension-by-zero stalk description on `U`, hence is flat over `\mathcal O_{X,x}`. If
-- `x ∉ U`, the stalk is zero by the extension-by-zero stalk description outside `U`, and the zero
-- module is flat.
/-- Lemma 17.17.6: for an open subset `U ⊆ X`, the extension by zero `j_{U!}\mathcal O_U` is a
flat sheaf of `\mathcal O_X`-modules. -/
theorem structureSheafLowerShriek_isFlat
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    SheafOfModules.RingedSite.IsFlat X.sheaf (structureSheafLowerShriek U) := sorry

end AlgebraicGeometry.RingedSpace.ModuleSheaf
