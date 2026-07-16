import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_25_7
import StacksProject_2024.stacks_project.Chap28.Lemma_28_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local notation "ModX" => X.Modules
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))

-- Semantic recall:
-- - `lean_leansearch` surfaced the canonical principal-open localization owner
--   `AlgebraicGeometry.Γ_restrict_isLocalization`;
-- - local Chapter 17 supplies the concrete graded section owners `Γ_*(ℒ)` and `Γ_*(ℒ, ℱ)`;
-- - `28.17.1.1` records that the full localized graded comparison map
--   `Γ_*(X, ℒ, ℱ)_(s) → Γ(X_s, ℱ|_{X_s})` is not yet packaged as a local declaration;
-- - the Stacks source tag evidence is consistent with tag `01PW`.

/- Lemma 28.17.2: for a scheme `X`, an invertible `\mathcal O_X`-module `\mathcal L`, a section
`s ∈ Γ(X, \mathcal L)`, and a quasi-coherent `\mathcal O_X`-module `\mathcal F`, the displayed
map from `28.17.1.1`
`Γ_*(X, \mathcal L, \mathcal F)_(s) → Γ(X_s, \mathcal F|_{X_s})` is injective when `X` is
quasi-compact, and is an isomorphism when `X` is quasi-compact and quasi-separated. In particular,
the degree-zero canonical map
`Γ_*(X, \mathcal L)_(s) → Γ(X_s, \mathcal O_X)`, sending `a / s^n` to
`a ⊗ s^{-n}`, is an isomorphism when `X` is quasi-compact and quasi-separated.

The current dependency-closed API has the graded global-section owners and the principal-open
localization owners below, but not the full localized graded comparison map from `28.17.1.1` as a
single concrete declaration. This item is therefore recorded as a source-faithful recall block
rather than as a fake theorem about an arbitrary map. -/
#check AlgebraicGeometry.RingedSpace.gradedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree
#check AlgebraicGeometry.Γ_restrict_isLocalization
#check fun {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : Γ(X, ⊤)) ↦
  (inferInstance :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))

end AlgebraicGeometry.Scheme.Modules
