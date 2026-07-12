import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)

/-- The direct-image functor on sheaves of modules along a morphism of ringed sites. -/
abbrev pushforward :
    SheafOfModules.{max u v} X.structureSheaf ⥤ SheafOfModules.{max u v} Y.structureSheaf :=
  SheafOfModules.pushforward.{max u v} f.structureSheafMap

/-- Definition 18.13.1: pushforward is the canonical direct image of module sheaves. -/
@[stacks 03D6]
theorem pushforward_eq :
    pushforward f = SheafOfModules.pushforward.{max u v} f.structureSheafMap := rfl

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]

/-- Bridge instance used by later exactness statements: the canonical module pushforward along the
structure-sheaf map inherits the standard sheaf-level right-adjoint structure. This is not the
source-facing content of Definition 18.13.1. -/
@[stacks 03D6]
instance structureSheafMap_pushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{max u v} f.structureSheafMap).IsRightAdjoint := by
  exact SheafOfModules.instIsRightAdjointPushforward (φ := f.structureSheafMap)

end RingedSite.Hom

/- Companion for Definition 18.13.1 (1): for a morphism of ringed topoi or ringed sites, the
direct image of a sheaf of modules is the canonical functor `SheafOfModules.pushforward`, whose
underlying sheaf of abelian groups is the usual pushforward and whose module structure is obtained
by restricting scalars along the structure-sheaf map
`f^\sharp : \mathcal O_{\mathcal D} \to f_* \mathcal O_{\mathcal C}`. -/
recall SheafOfModules.pushforward

/- Companion for Definition 18.13.1 (2): for a morphism of ringed topoi or ringed sites, the
inverse image of a sheaf of modules is the canonical functor `SheafOfModules.pullback`, i.e. the
sheaf `\mathcal O_{\mathcal C} \otimes_{f^{-1}\mathcal O_{\mathcal D}} f^{-1}\mathcal G` with
its canonical `\mathcal O_{\mathcal C}`-module structure. -/
recall SheafOfModules.pullback

namespace RingedSite.Hom

/- Source-facing notation for direct image of module sheaves on ringed sites. -/
scoped notation:max f:max " _*" => RingedSite.Hom.pushforward f

/- Source-facing notation for inverse image of module sheaves on ringed sites. -/
scoped notation:max f:max "^*" => SheafOfModules.pullback (RingedSite.Hom.structureSheafMap f)

end RingedSite.Hom
