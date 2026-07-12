import StacksProject_2024.Chap28.Situation_28_28_1
import StacksProject_2024.Chap28.Lemma_28_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable (ℒ : X.Modules) [hℒ : Invertible ℒ] [IsAmple ℒ]
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` surfaced the current mathlib `Proj` construction layer,
-- especially `Proj.fromOfGlobalSections`, while local Chapter 17 and Chapter 28 dependencies
-- provide the graded global-section owners, the ample invertible sheaf situation, and the
-- basic-open localization statements used in the proof. The source tag evidence is consistent
-- with tag `01QJ`.

/- Lemma 28.28.3: in Situation 28.28.1, for an ample invertible sheaf `\mathcal L` on `X` and a
quasi-coherent sheaf `\mathcal F`, set
`M = \Gamma_*(X, \mathcal L, \mathcal F)` as a graded `S = \Gamma_*(X, \mathcal L)`-module.
There are isomorphisms
`f^*\widetilde M \simeq \mathcal F`, functorial in `\mathcal F`, such that the composite
`M_0 \to \Gamma(Proj(S), \widetilde M) \to \Gamma(X, \mathcal F)` is the identity map.

The dependency-closed API available here has the graded section-ring and twisted-section-module
owners, the generic `Proj` and `Proj.fromOfGlobalSections` construction, and the affine
basic-open localization inputs used by the Stacks proof. It does not yet package the exact
Situation 28.28.1 morphism `f : X \to Proj(\Gamma_*(X, \mathcal L))`, the associated sheaf
`\widetilde M` of a graded module on `Proj(S)`, the pullback comparison isomorphism, its
functoriality in `\mathcal F`, or the degree-zero global-section identity as concrete reusable
declarations. This item is therefore recorded as a labeled recall block rather than as a fake
existence theorem over arbitrary comparison data. -/
#check (IsAmple ℒ : Prop)
#check (ℱ.IsQuasicoherent : Prop)
#check AlgebraicGeometry.RingedSpace.gradedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedGlobalSectionsDegree
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree
#check AlgebraicGeometry.Proj
#check AlgebraicGeometry.Proj.basicOpen
#check AlgebraicGeometry.Proj.fromOfGlobalSections
#check AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen
#check AlgebraicGeometry.Γ_restrict_isLocalization
#check fun {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : Γ(X, ⊤)) ↦
  (inferInstance :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))
#check AlgebraicGeometry.Scheme.Modules.pullback

end AlgebraicGeometry.Scheme.Modules
