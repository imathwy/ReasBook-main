import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.FibredCategoryOverLowerShriek
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.Remark_21_37_3
import StacksProject_2024.Chap21.SiteAbelianDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.FibredCategoryMor
open RingedSite.Hom
open scoped RingedSite.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

/-
Domain-style sampling for Lemma 21.38.5:
- primary domain: inverse image and lower shriek for module sheaves and abelian sheaves in the
  inherited ringed-topos situation;
- source-facing owners for clauses `(1)`–`(3)` live in
  `CategoryTheory.FibredCategoryOver`;
- the derived owners for clauses `(4)`–`(6)` are recalled from Chapter `21`'s canonical
  derived-functor API. -/

section

variable {D : RingedSite.{u, v}}
variable {C C' : FibredCategoryOver.{u, v} D}
variable (u : C' ⟶ C)
variable [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
variable [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
variable [IsMorphismOfSites
  (inheritedTopology D.siteTopology C')
  (inheritedTopology D.siteTopology C)
  (toFunctor u)]
variable [Functor.IsRightAdjoint (moduleInverseImage u)]
variable [Functor.IsRightAdjoint (abelianInverseImage u)]

/-- Lemma 21.38.5 (3): after forgetting module structures, the canonical lower shriek on modules
is naturally isomorphic to the canonical lower shriek on abelian sheaves. This source-facing
statement is phrased entirely in terms of the public inherited inverse-image and lower-shriek
owners from clauses `(1)` and `(2)`. -/
@[stacks 08PC]
theorem lowerShriek_forget_functor_isomorphic :
    IsIsomorphic
      (underlyingAbelianSheafFunctor (inheritedRingedSite D C') ⋙ abelianLowerShriek u)
      (moduleLowerShriek u ⋙ underlyingAbelianSheafFunctor (inheritedRingedSite D C)) := by
  exact ⟨asIso (lowerShriekForgetComparison u)⟩

/-- Lemma 21.38.5 (3), objectwise source-facing companion. -/
@[stacks 08PC]
theorem lowerShriek_forget_isomorphic
    (M : SheafOfModules (inheritedRingedSite D C').structureSheaf) :
    IsIsomorphic
      ((underlyingAbelianSheafFunctor (inheritedRingedSite D C') ⋙ abelianLowerShriek u).obj M)
      ((moduleLowerShriek u ⋙ underlyingAbelianSheafFunctor (inheritedRingedSite D C)).obj M) :=
  by
    exact ⟨(asIso (lowerShriekForgetComparison u)).app M⟩

end

/- Lemma 21.38.5 (4): on derived categories of module sheaves, the inverse-image owner is the
canonical derived pushforward functor `modulePushforwardDerived (inheritedRingedSiteHom u)`, and
the corresponding derived lower shriek is packaged by a chosen adjunction with that owner.

Lemma 21.38.5 (5): on derived categories of abelian sheaves, the inverse-image owner is the
canonical derived functor `siteAbelianInverseImageDerived JC' JC (toFunctor u)`, and the
existence of the abelian derived lower shriek is expressed on that owner by
`Functor.leftAdjoint`.

Lemma 21.38.5 (6): the derived lower-shriek/forget comparison is the canonical owner
`CategoryTheory.derivedLowerShriek_forget_comparison`, specialized to the inherited ringed-site
morphism `inheritedRingedSiteHom u`. -/

section

variable {D : RingedSite.{u, v}}
variable {C C' : FibredCategoryOver.{u, v} D}
variable (u : C' ⟶ C)
variable [Functor.IsContinuous C'.p (inheritedTopology D.siteTopology C') D.siteTopology]
variable [Functor.IsContinuous C.p (inheritedTopology D.siteTopology C) D.siteTopology]
variable [IsMorphismOfSites
  (inheritedTopology D.siteTopology C')
  (inheritedTopology D.siteTopology C)
  (toFunctor u)]
variable [Functor.Additive (RingedSite.Hom.modulePushforward (inheritedRingedSiteHom u))]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (inheritedRingedSiteHom u))
  (ModuleQis (inheritedRingedSite D C))]
variable [Functor.Additive
  ((toFunctor u).sheafPushforwardContinuous
    AddCommGrpCat.{max u v}
    (inheritedTopology D.siteTopology C')
    (inheritedTopology D.siteTopology C))]
variable [IsGrothendieckAbelian.{max u v}
  (SiteAbelianSheafCat (inheritedTopology D.siteTopology C))]

/- Lemma 21.38.5 (4): on derived categories of module sheaves, the inverse-image owner is the
canonical derived pushforward functor `modulePushforwardDerived (inheritedRingedSiteHom u)`. -/
#check modulePushforwardDerived (inheritedRingedSiteHom u)

variable [Functor.IsRightAdjoint (modulePushforwardDerived (inheritedRingedSiteHom u))]

/- Lemma 21.38.5 (4), lower-shriek owner: once that derived inverse-image owner is a right
adjoint, the lower shriek is the canonical owner
`Functor.leftAdjoint (modulePushforwardDerived (inheritedRingedSiteHom u))`. -/
#check Functor.leftAdjoint (modulePushforwardDerived (inheritedRingedSiteHom u))

/- Lemma 21.38.5 (5): on derived categories of abelian sheaves, the inverse-image owner is the
canonical owner `siteAbelianInverseImageDerived (inheritedTopology D.siteTopology C')
(inheritedTopology D.siteTopology C) (toFunctor u)`. -/
#check siteAbelianInverseImageDerived
    (inheritedTopology D.siteTopology C')
    (inheritedTopology D.siteTopology C)
    (toFunctor u)

variable [Functor.IsRightAdjoint
  (siteAbelianInverseImageDerived
    (inheritedTopology D.siteTopology C')
    (inheritedTopology D.siteTopology C)
    (toFunctor u))]

/- Lemma 21.38.5 (5), lower-shriek owner: once that abelian derived inverse-image owner is a
right adjoint, the lower shriek is the canonical owner
`Functor.leftAdjoint (siteAbelianInverseImageDerived (inheritedTopology D.siteTopology C')
(inheritedTopology D.siteTopology C) (toFunctor u))`. -/
#check Functor.leftAdjoint
  (siteAbelianInverseImageDerived
    (inheritedTopology D.siteTopology C')
    (inheritedTopology D.siteTopology C)
    (toFunctor u))

/- Lemma 21.38.5 (6): the derived lower-shriek/forget comparison is already owned upstream by
`CategoryTheory.derivedLowerShriek_forget_comparison`, specialized to the inherited ringed-site
morphism `inheritedRingedSiteHom u`. -/
recall CategoryTheory.derivedLowerShriek_forget_comparison

end

end FibredCategoryOver
end CategoryTheory
