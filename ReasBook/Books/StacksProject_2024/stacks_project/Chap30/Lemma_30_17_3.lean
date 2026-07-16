import Mathlib
import StacksProject_2024.stacks_project.Chap12.Lemma_12_5_20
import StacksProject_2024.stacks_project.Chap20.Lemma_20_8_2_Mayer_Vietoris
import StacksProject_2024.stacks_project.Chap28.Lemma_28_17_2
import StacksProject_2024.stacks_project.Chap28.Lemma_28_26_4
import StacksProject_2024.stacks_project.Chap30.Lemma_30_2_2
import StacksProject_2024.stacks_project.Chap30.Lemma_30_4_1_Induction_Principle

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

-- Semantic recall: `lean_leansearch` surfaced the canonical sheaf-cohomology owner `Sheaf.H'`
-- and principal-open localization APIs. Local Chapter 28 records the degree-zero comparison as a
-- recall block because the full localized graded comparison map is not yet packaged as a concrete
-- declaration; the same obstruction applies to the higher-cohomology map in this item.

/- Lemma 30.17.3: let `X` be a scheme, let `\mathcal L` be an invertible sheaf on `X`, let
`s ∈ Γ(X, \mathcal L)`, and let `\mathcal F` be a quasi-coherent `\mathcal O_X`-module. If
`X` is quasi-compact and quasi-separated, then the canonical map
`H^p_*(X, \mathcal L, \mathcal F)_(s) → H^p(X_s, \mathcal F)`, sending `ξ / s^n` to
`s^{-n} ξ`, is an isomorphism.

The current dependency-closed API exposes the relevant graded twisted global-section owners, the
canonical sheaf-cohomology owner, the principal-open localization owners used in the degree-zero
case, affine-open higher-cohomology vanishing, the compact-open induction principle, the
Mayer-Vietoris sequence, and the five-lemma. It does not yet expose the localized graded
cohomology object `H^p_*(X, \mathcal L, \mathcal F)_(s)` or the displayed canonical comparison
map as concrete declarations, so this item is recorded as a source-faithful recall block rather
than as a theorem about an arbitrary map. The Stacks source tag evidence is consistent with
tag `09MR`. -/
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree
#check CategoryTheory.Sheaf.H'
#check CategoryTheory.Sheaf.cohomologyPresheafFunctor
#check AlgebraicGeometry.Γ_restrict_isLocalization
#check fun {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : Γ(X, ⊤)) ↦
  (inferInstance :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))
#check AlgebraicGeometry.Scheme.higherCohomology_isZero_on_affineOpen
#check AlgebraicGeometry.Scheme.compactOpen_induction_principle_top
#check AlgebraicGeometry.ringedSpaceModule_mayerVietoris_sequence_exact
#check CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono

end AlgebraicGeometry.Scheme.Modules
