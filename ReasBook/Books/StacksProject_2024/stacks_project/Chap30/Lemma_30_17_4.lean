import Mathlib
import StacksProject_2024.Chap30.Lemma_30_17_3

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

-- Semantic recall: `lean_leansearch` surfaced the standard qcqs localization/power-killing
-- lemmas for global sections, and local Chapter 30 precedent records Lemma 30.17.3 as a recall
-- block because the localized graded higher-cohomology object and its canonical comparison map
-- are not yet exposed as concrete declarations. The same missing owner is needed here to express
-- the source operation `s^n ξ` without inventing an arbitrary surrogate map. The Stacks source
-- tag evidence is consistent with tag `01XR`.

/- Lemma 30.17.4: let `X` be a scheme, let `\mathcal L` be an invertible
`\mathcal O_X`-module, and let `s ∈ Γ(X, \mathcal L)`. Assume that `X` is quasi-compact and
quasi-separated, and that the principal open `X_s` is affine. Then for every quasi-coherent
`\mathcal O_X`-module `\mathcal F`, every `p > 0`, and every
`ξ ∈ H^p(X, \mathcal F)`, there exists `n ≥ 0` such that
`s^n ξ = 0` in `H^p(X, \mathcal F \otimes_{\mathcal O_X} \mathcal L^{\otimes n})`.

The available dependency-closed API provides the twisted graded-section owners, the canonical
sheaf-cohomology owner, the degree-piece action on twisted graded global sections, the preceding
localized comparison recall from Lemma 30.17.3, affine-open higher-cohomology vanishing from
Lemma 30.2.2, and the standard qcqs localization/power-killing lemmas for global sections. It
does not yet expose the localized graded higher-cohomology module or the canonical cohomology map
realizing multiplication by powers of an invertible-section, so this item is recorded as a
source-faithful recall block rather than as a theorem about an arbitrary map. -/
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsSmul
#check CategoryTheory.Sheaf.H'
#check CategoryTheory.Sheaf.cohomologyPresheafFunctor
#check AlgebraicGeometry.Scheme.higherCohomology_isZero_on_affineOpen
#check AlgebraicGeometry.exists_of_res_zero_of_qcqs
#check AlgebraicGeometry.Γ_restrict_isLocalization
#check fun {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : Γ(X, ⊤)) ↦
  (inferInstance :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))

end AlgebraicGeometry.Scheme.Modules
