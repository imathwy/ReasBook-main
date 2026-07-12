import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall:
-- - mathlib already owns the qcqs principal-open localization statement as
--   `AlgebraicGeometry.Γ_restrict_isLocalization`;
-- - for quasi-coherent module sheaves, the corresponding source-facing content is the anonymous
--   principal-open `IsLocalizedModule` instance on restriction to `X.basicOpen f`;
-- - this matches the recall-only shape used by neighboring Chapter 28 files for the same API.

/- Lemma 28.17.1: if `X` is quasi-compact and quasi-separated and `f` is a global section, then
the canonical map from the localization of global functions at `f` to the functions on the
principal open `X_f = X.basicOpen f` is an isomorphism; if `\mathcal{F}` is quasi-coherent, then
the corresponding restriction map on `\mathcal{F}` is likewise the canonical localized-module map.

These are already owned canonically by mathlib's qcqs principal-open localization API: the ring
statement is the named owner `Γ_restrict_isLocalization`, and the module statement is the
quasi-coherent principal-open `IsLocalizedModule` instance on the restriction morphism
`ℱ(X) → ℱ(X_f)`. This file keeps the executable recall surface at the named ring owner together
with the anonymous module-side instance recall, rather than introducing a chapter-local wrapper. -/
recall AlgebraicGeometry.Γ_restrict_isLocalization

#check fun {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent ℱ] (f : Γ(X, ⊤)) ↦
  (inferInstance :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))
end AlgebraicGeometry.Scheme.Modules
