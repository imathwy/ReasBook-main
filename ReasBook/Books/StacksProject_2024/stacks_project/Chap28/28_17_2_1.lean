import Mathlib
import StacksProject_2024.stacks_project.Chap28.«28_17_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry SectionNonvanishingOpen

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local notation "ModX" => X.Modules
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

variable (ℒ : ModX) [IsInvertibleX ℒ] (ℱ 𝒢 : ModX) (s : Γ(ℒ, ⊤))

-- Semantic recall:
-- - `28.17.1.1` already packages the localized twisted graded module
--   `Γ_*(X, ℒ, ℱ)_(s)` and its generic comparison-target sections on the nonvanishing open `X_s`;
-- - Chapter 17 provides the canonical internal-Hom owner `ihom` and the section/morphism bridge
--   `SheafOfModules.unitHomEquiv`;
-- - `Lemma_28_17_1` remains the qcqs localization owner used later in the proof layer;
-- - the Stacks source tag is `0B5M`.

-- Source/core/bridge triage:
-- - source-facing: the localized graded internal-Hom source and the codomain
--   `Hom_{O_{X_s}}(\mathcal F|_{X_s}, \mathcal G|_{X_s})`;
-- - core/canonical: `localizedTwistedGlobalSections` from `28.17.1.1`, `ihom`, and the Chapter 17
--   nonvanishing-open sections owner from `28.17.1.1`;
-- - bridge/view: identify sections of the restricted internal-Hom sheaf on `X_s` with the local
--   morphisms `\mathcal F|_{X_s} ⟶ \mathcal G|_{X_s}`.

/- 28.17.2.1 (Stacks tag `0B5M`): for an invertible `\mathcal O_X`-module `\mathcal L`, a section
`s : \Gamma(X, \mathcal L)`, and `\mathcal O_X`-modules `\mathcal F`, `\mathcal G`, the source of
the displayed comparison map is the localized graded internal-Hom module
`(\bigoplus_n \operatorname{Hom}_{\mathcal O_X}(\mathcal F,
\mathcal G \otimes \mathcal L^{\otimes n}))_(s)`.

The current repository already owns the same source canonically as the localized twisted global
sections object from `28.17.1.1`, specialized to the internal-Hom sheaf `(ihom ℱ).obj 𝒢`. -/
#check localizedTwistedGlobalSections ℒ (ℱ ⟶[ModX] 𝒢) s

/-- The target-side bridge for 28.17.2.1: sections of the restricted internal-Hom sheaf on the
nonvanishing open `X_s` are canonically the same as local morphisms
`\mathcal F|_{X_s} ⟶ \mathcal G|_{X_s}`. -/
noncomputable abbrev nonvanishingOpenInternalHomSectionsEquivHom
    :
    nonvanishingOpenSections ℒ (ℱ ⟶[ModX] 𝒢) s ≃
      (ℱ.over (show X.Opens from (X.toRingedSpace)_[show ℒ.val.sections from s]) ⟶
        𝒢.over (show X.Opens from (X.toRingedSpace)_[show ℒ.val.sections from s])) :=
  let U : X.Opens := show X.Opens from (X.toRingedSpace)_[show ℒ.val.sections from s]
  (RingedSpace.over_sections_equiv_evaluation ((ℱ ⟶[ModX] 𝒢).over U)).symm.trans <|
    (((ℱ ⟶[ModX] 𝒢).over U).unitHomEquiv).symm.trans <|
      (((ihom (ℱ.over U)).obj (𝒢.over U)).unitHomEquiv).symm

end AlgebraicGeometry.Scheme.Modules
