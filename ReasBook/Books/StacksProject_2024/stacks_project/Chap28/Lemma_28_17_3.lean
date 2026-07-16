import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_16_1
import StacksProject_2024.stacks_project.Chap28.Lemma_28_16_2
import StacksProject_2024.stacks_project.Chap28.Lemma_28_17_2

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
-- - `lean_leansearch` surfaced `Scheme.Modules`, `Scheme.Modules.Hom`, finite-type and
--   finite-presentation module-sheaf owners, and the affine basic-open localization API;
-- - local Chapter 28 records `28.17.2.1` as a recall-only block because the localized graded Hom
--   comparison map is not yet packaged as a concrete declaration;
-- - local Chapter 28 records Lemma `28.17.2` through the graded twisted-global-section and
--   principal-open localization owners;
-- - the Stacks source tag evidence is consistent with tag `01XQ`.

/- Lemma 28.17.3: let `X` be a scheme, let `\mathcal L` be an invertible
`\mathcal O_X`-module, let `s ∈ Γ(X, \mathcal L)` be a section, and let
`\mathcal F`, `\mathcal G` be quasi-coherent `\mathcal O_X`-modules. For the displayed map
`28.17.2.1`
`(\bigoplus_n Hom_{\mathcal O_X}(\mathcal F,
\mathcal G \otimes \mathcal L^{\otimes n}))_(s) →
Hom_{\mathcal O_{X_s}}(\mathcal F|_{X_s}, \mathcal G|_{X_s})`:

* if `X` is quasi-compact and `\mathcal F` is of finite type, the map is injective;
* if `X` is quasi-compact and quasi-separated and `\mathcal F` is of finite presentation, the map
  is bijective.

The current dependency-closed API exposes the graded twisted-global-section owners and the
principal-open localization owners below, together with the affine finite-type/finite-presentation
bridges used in the proof. It still does not expose the localized graded Hom comparison map from
`28.17.2.1` as a concrete declaration, so this item is recorded as a source-faithful recall block
rather than as a theorem about a fake arbitrary map. -/
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree
#check AlgebraicGeometry.Γ_restrict_isLocalization
#check fun {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : Γ(X, ⊤)) ↦
  (inferInstance :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))
#check tilde_isFiniteType_iff_module_finite
#check tilde_isFinitePresentation_iff_module_finitePresentation
#check ihom
#check SheafOfModules.IsFiniteType
#check SheafOfModules.IsFinitePresentation
#check SheafOfModules.IsQuasicoherent

end AlgebraicGeometry.Scheme.Modules
